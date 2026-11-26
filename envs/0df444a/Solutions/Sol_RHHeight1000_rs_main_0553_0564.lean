-- Prove2me | solution 1 for RHHeight1000.rs_main_0553_0564
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:28:20.995093+00:00
-- url     : https://prove2.me/submissions/d864d7ec-2780-434e-8531-0fecac89c6c5

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

noncomputable def RS553to564.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS553to564.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS553to564.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS553to564.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS553to564.d2 a b h 

theorem RS553to564.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS553to564.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS553to564.d3 a b h)) 

noncomputable def Ns552p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns552p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns552p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns552p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns552p0 Ns552p1 Ns552p2 Ns552p1 614572177 536870912 1 153760000 614572177 536870912 1 153760000 307286088 268435456 3 268435456 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns552p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns552p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns552p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns552p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns552p8 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625 

noncomputable def Ns552p9 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575 

noncomputable def Ns552p10 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375 

noncomputable def Ns552p11 := BSN.log_dyadic_bound Ns552p6 Ns552p7 16 15 Ns552p8 536870912 153760000 Ns552p9 Ns552p10 614572177 Ns552p4 Ns552p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns552p6) (BSN.artanhQ Ns552p7) 0 15 Ns552p9 Ns552p8 Ns552p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns552p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns552p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns552p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns552p15 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625 

noncomputable def Ns552p16 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575 

noncomputable def Ns552p17 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375 

noncomputable def Ns552p18 := BSN.log_dyadic_bound Ns552p13 Ns552p14 16 15 Ns552p15 536870912 153760000 Ns552p16 Ns552p17 614572177 Ns552p12 Ns552p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns552p13) (BSN.artanhQ Ns552p14) 0 15 Ns552p16 Ns552p15 Ns552p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns552p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 307286088 268435456 3 268435456 38410761 33554432 3 268435456 (Ns552p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns552p0 Ns552p1 614572177 536870912 1 153760000 Bool.false (BSN.logfrac_isNear Ns552p4 Ns552p5 1 Ns552p0 Ns552p1 614572177 536870912 153760000 rfl rfl rfl (Ns552p11 rfl))) (BSN.isNear_log_sfrac Ns552p2 Ns552p1 614572177 536870912 1 153760000 Bool.false (BSN.logfrac_isNear Ns552p12 Ns552p5 1 Ns552p2 Ns552p1 614572177 536870912 153760000 rfl rfl rfl (Ns552p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS553to564.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 3 268435456 := Ns552p19 

noncomputable def Ns552p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 33554432 9610000 385100712855 135135 23258159 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz579 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz579

noncomputable abbrev qz0 := qz316

theorem RS553to564.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 23258159 33554432 1 9610000 := BSN.isNear_log_sfrac 2 1 23258159 33554432 1 9610000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 23258159 33554432 9610000 rfl rfl rfl (Ns552p20 rfl)) 

theorem RS553to564.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 372130544 536870912 56 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 23258159 33554432 1 9610000 372130544 536870912 56 536870912 RS553to564.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz580 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz580

noncomputable def Ns552p21 := @Enclosure.Real.IsNear.inv_image qz317 94906265 67108864 1 67108864 23726566 23726567 33554432 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 94906265 67108864 1 67108864 (BSN.sqrt_enclosure 2 1 47453132 47453133 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS553to564.d8 : Enclosure.Real.IsNear qz320 Bool.false 47453133 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 47453133 67108864 1 67108864 (Ns552p21 rfl rfl) rfl 

theorem RS553to564.d9 : Enclosure.Real.IsNear qz320 Bool.false 379625064 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 379625064 536870912 8 536870912 RS553to564.d8 rfl 

noncomputable def Ns552p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 33554432 9610000 13079757671720842725 316234143225 36863311 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS553to564.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 9610000 := BSN.isNear_log_sfrac 3 1 36863311 33554432 1 9610000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 36863311 33554432 9610000 rfl rfl rfl (Ns552p22 rfl)) 

theorem RS553to564.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 589812976 536870912 56 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 9610000 589812976 536870912 56 536870912 RS553to564.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns552p23 := @Enclosure.Real.IsNear.inv_image qz321 116235963 67108864 1 67108864 19372660 19372661 33554432 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 116235963 67108864 1 67108864 (BSN.sqrt_enclosure 3 1 58117981 58117982 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS553to564.d12 : Enclosure.Real.IsNear qz323 Bool.false 38745321 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 38745321 67108864 1 67108864 (Ns552p23 rfl rfl) rfl 

theorem RS553to564.d13 : Enclosure.Real.IsNear qz323 Bool.false 309962568 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 309962568 536870912 8 536870912 RS553to564.d12 rfl 

noncomputable def Ns552p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns552p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns552p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns552p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns552p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns552p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns552p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns552p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns552p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns552p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns552p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns552p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns552p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns552p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns552p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns552p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns552p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns552p25 Ns552p26 Ns552p27 Ns552p28 200200021673987500790625 Ns552p29 Ns552p30 Ns552p31 Ns552p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns552p32 Ns552p33 151412625 Ns552p34 Ns552p35 1322214852783825 Ns552p27 Ns552p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns552p32 Ns552p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns552p34 Ns552p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns552p36 Ns552p37 1267389585 Ns552p38 Ns552p39 1927077560082675 Ns552p29 Ns552p30 Ns552p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns552p36 Ns552p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns552p38 Ns552p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS553to564.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns552p24 Ns552p25 1 Ns552p26 := Ns552p40 rfl rfl rfl 

noncomputable def Ns552p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns552p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns552p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns552p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns552p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns552p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns552p25 Ns552p26 Ns552p42 Ns552p43 9945 Ns552p44 Ns552p45 65835 Ns552p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns552p42 Ns552p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns552p44 Ns552p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS553to564.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns552p41 Ns552p25 1 Ns552p26 := Ns552p46 rfl 

noncomputable def Ns552p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns552p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS553to564.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns552p47 Ns552p25 1 Ns552p48 := BSN.pi_combine Ns552p24 Ns552p41 Ns552p25 Ns552p26 Ns552p48 Ns552p47 rfl rfl rfl rfl RS553to564.d14 RS553to564.d15 

theorem RS553to564.d17 : Enclosure.Real.IsNear Real.pi Bool.false 28296951008113761 9007199254740992 1 9007199254740992 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns552p47 Ns552p25 1 Ns552p48 28296951008113761 9007199254740992 1 9007199254740992 RS553to564.d16 rfl 

noncomputable def Ns552p49 := nat_lit 129013261453190219981479458510875701904296875 

noncomputable def Ns552p50 := nat_lit 20028702544022979302942508184499384445755625 

noncomputable def Ns552p51 := nat_lit 105610919306899072369715234453255625 

noncomputable def Ns552p52 := nat_lit 11743816085855617508865225 

noncomputable def Ns552p53 := nat_lit 24536140990734100341796875 

noncomputable def Ns552p54 := BSN.log_dyadic_bound 3 5 18 17 Ns552p49 33554432 9610000 Ns552p50 Ns552p51 46516319 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 3) (BSN.artanhQ 5) 0 17 8 816252149187356400 5258090972900390625 87256779635025 Ns552p52 Ns552p53 1210346287688420415225 Ns552p50 Ns552p49 Ns552p51 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 3) (BSN.artanhQ 5) 0 8 816252149187356400 5258090972900390625 87256779635025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 3) (BSN.artanhQ 5) 8 17 Ns552p52 Ns552p53 1210346287688420415225 rfl rfl rfl rfl)) rfl rfl 

theorem RS553to564.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 9610000 := BSN.isNear_log_sfrac 4 1 46516319 33554432 1 9610000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 46516319 33554432 9610000 rfl rfl rfl (Ns552p54 rfl rfl)) 

theorem RS553to564.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 744261104 536870912 56 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 9610000 744261104 536870912 56 536870912 RS553to564.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns552p55 := @Enclosure.Real.IsNear.inv_image qz325 134217729 67108864 1 67108864 16777215 16777216 33554432 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 134217729 67108864 1 67108864 (BSN.sqrt_enclosure 4 1 67108864 67108865 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS553to564.d20 : Enclosure.Real.IsNear qz327 Bool.false 33554431 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 33554431 67108864 1 67108864 (Ns552p55 rfl rfl) rfl 

theorem RS553to564.d21 : Enclosure.Real.IsNear qz327 Bool.false 268435448 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 268435448 536870912 8 536870912 RS553to564.d20 rfl 

noncomputable def Ns552p56 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns552p57 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns552p58 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns552p59 := nat_lit 885951608314392539099884620 

noncomputable def Ns552p60 := nat_lit 1286943652057122751813246125 

noncomputable def Ns552p61 := BSN.log_dyadic_bound 2 3 22 21 Ns552p56 33554432 9610000 Ns552p57 Ns552p58 54003774 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns552p59 Ns552p60 84004523356416638976000 Ns552p57 Ns552p56 Ns552p58 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns552p59 Ns552p60 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS553to564.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 9610000 := BSN.isNear_log_sfrac 5 1 54003774 33554432 1 9610000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 9610000 rfl rfl rfl (Ns552p61 rfl rfl)) 

theorem RS553to564.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 864060384 536870912 56 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 9610000 864060384 536870912 56 536870912 RS553to564.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns552p62 := @Enclosure.Real.IsNear.inv_image qz328 150059981 67108864 1 67108864 15005998 15005999 33554432 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 150059981 67108864 1 67108864 (BSN.sqrt_enclosure 5 1 75029990 75029991 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS553to564.d24 : Enclosure.Real.IsNear qz329 Bool.false 30011997 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 30011997 67108864 1 67108864 (Ns552p62 rfl rfl) rfl 

theorem RS553to564.d25 : Enclosure.Real.IsNear qz329 Bool.false 240095976 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 240095976 536870912 8 536870912 RS553to564.d24 rfl 

noncomputable def Ns552p63 := nat_lit 2166104270535356806332416 

noncomputable def Ns552p64 := nat_lit 1208925819614629174706176 

noncomputable def Ns552p65 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 33554432 9610000 1420244935680 967680 13605151 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz580)

theorem RS553to564.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 50000000961 480500000000000000 := BSN.isNear_log_sfrac 6 1 4034683612241143 2251799813685248 50000000961 480500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false Ns552p63 Ns552p64 1000000019220000 9610000000000000000000 4034683612241143 2251799813685248 50000000961 480500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 13605151 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns552p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS553to564.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 961943533 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 50000000961 480500000000000000 961943533 536870912 57 536870912 RS553to564.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns552p66 := @Enclosure.Real.IsNear.inv_image qz331 164382475 67108864 1 67108864 13698539 13698540 33554432 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 164382475 67108864 1 67108864 (BSN.sqrt_enclosure 6 1 82191237 82191238 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS553to564.d28 : Enclosure.Real.IsNear qz332 Bool.false 27397079 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 27397079 67108864 1 67108864 (Ns552p66 rfl rfl) rfl 

theorem RS553to564.d29 : Enclosure.Real.IsNear qz332 Bool.false 219176632 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 219176632 536870912 8 536870912 RS553to564.d28 rfl 

noncomputable def Ns552p67 := nat_lit 2352460989330532755046400 

noncomputable def Ns552p68 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 33554432 9610000 11010900719820672 5524329195 18777589 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz580)

theorem RS553to564.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 50000000961 480500000000000000 := BSN.isNear_log_sfrac 7 1 4381800050531575 2251799813685248 50000000961 480500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false Ns552p67 Ns552p64 1000000019220000 9610000000000000000000 4381800050531575 2251799813685248 50000000961 480500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 18777589 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns552p68 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS553to564.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 1044702541 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 50000000961 480500000000000000 1044702541 536870912 57 536870912 RS553to564.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns552p69 := @Enclosure.Real.IsNear.inv_image qz334 177553365 67108864 1 67108864 12682383 12682384 33554432 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 177553365 67108864 1 67108864 (BSN.sqrt_enclosure 7 1 88776682 88776683 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS553to564.d32 : Enclosure.Real.IsNear qz335 Bool.false 25364767 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 25364767 67108864 1 67108864 (Ns552p69 rfl rfl) rfl 

theorem RS553to564.d33 : Enclosure.Real.IsNear qz335 Bool.false 202918136 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 202918136 536870912 8 536870912 RS553to564.d32 rfl 

noncomputable def Ns552p70 := nat_lit 2513890570116003237199872 

noncomputable def Ns552p71 := BSN.log_dyadic_bound 0 16 1 0 1 33554432 9610000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz580)

theorem RS553to564.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000002883 961000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000002883 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns552p70 Ns552p64 1000000028830000 9610000000000000000000 9364972152248037 4503599627370496 100000002883 961000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns552p71 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS553to564.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 1116391676 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000002883 961000000000000000 1116391676 536870912 57 536870912 RS553to564.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns552p72 := @Enclosure.Real.IsNear.inv_image qz337 189812531 67108864 1 67108864 11863283 11863284 33554432 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 189812531 67108864 1 67108864 (BSN.sqrt_enclosure 8 1 94906265 94906266 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS553to564.d36 : Enclosure.Real.IsNear qz338 Bool.false 23726567 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 23726567 67108864 1 67108864 (Ns552p72 rfl rfl) rfl 

theorem RS553to564.d37 : Enclosure.Real.IsNear qz338 Bool.false 189812536 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 189812536 536870912 8 536870912 RS553to564.d36 rfl 

noncomputable def Ns552p73 := nat_lit 2656281492024125531619328 

noncomputable def Ns552p74 := BSN.log_dyadic_bound 1 17 3 2 1252815 33554432 9610000 1448 3 3952142 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz580)

theorem RS553to564.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000002883 961000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 100000002883 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns552p73 Ns552p64 1000000028830000 9610000000000000000000 9895419672221413 4503599627370496 100000002883 961000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 3952142 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns552p74 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS553to564.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 1179625948 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000002883 961000000000000000 1179625948 536870912 57 536870912 RS553to564.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns552p75 := @Enclosure.Real.IsNear.inv_image qz340 201326593 67108864 1 67108864 11184810 11184811 33554432 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 201326593 67108864 1 67108864 (BSN.sqrt_enclosure 9 1 100663296 100663297 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS553to564.d40 : Enclosure.Real.IsNear qz341 Bool.false 22369621 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 22369621 67108864 1 67108864 (Ns552p75 rfl rfl) rfl 

theorem RS553to564.d41 : Enclosure.Real.IsNear qz341 Bool.false 178956968 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 178956968 536870912 8 536870912 RS553to564.d40 rfl 

noncomputable def Ns552p76 := nat_lit 2783654566499630094221312 

noncomputable def Ns552p77 := BSN.log_dyadic_bound 2 18 4 3 3571283520 33554432 9610000 14806464 960 7487455 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz580)

theorem RS553to564.d42 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 100000002883 961000000000000000 := BSN.isNear_log_sfrac 10 1 10369921350850277 4503599627370496 100000002883 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false Ns552p76 Ns552p64 1000000028830000 9610000000000000000000 10369921350850277 4503599627370496 100000002883 961000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 7487455 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns552p77 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS553to564.d43 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 1236190956 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 100000002883 961000000000000000 1236190956 536870912 57 536870912 RS553to564.d42 rfl 

noncomputable abbrev qz343 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns552p78 := @Enclosure.Real.IsNear.inv_image qz343 212216861 67108864 1 67108864 10610843 10610844 33554432 (@Enclosure.Real.IsNear.of_eq qz343 (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 212216861 67108864 1 67108864 (BSN.sqrt_enclosure 10 1 106108430 106108431 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz344 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS553to564.d44 : Enclosure.Real.IsNear qz344 Bool.false 21221687 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 21221687 67108864 1 67108864 (Ns552p78 rfl rfl) rfl 

theorem RS553to564.d45 : Enclosure.Real.IsNear qz344 Bool.false 169773496 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 169773496 536870912 8 536870912 RS553to564.d44 rfl 

noncomputable def Ns552p79 := nat_lit 2898877505641241362038784 

noncomputable def Ns552p80 := BSN.log_dyadic_bound 3 19 5 4 16049467073745 33554432 9610000 135406373544 688905 10685534 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 19) 0 4 135406373544 16049467073745 688905 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11) qz580)

theorem RS553to564.d46 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 100000002883 961000000000000000 := BSN.isNear_log_sfrac 11 1 10799160248194789 4503599627370496 100000002883 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false Ns552p79 Ns552p64 1000000028830000 9610000000000000000000 10799160248194789 4503599627370496 100000002883 961000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 10685534 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns552p80 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS553to564.d47 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 1287360220 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 100000002883 961000000000000000 1287360220 536870912 57 536870912 RS553to564.d46 rfl 

noncomputable abbrev qz346 := (Real.sqrt (@Nat.cast Real Real.instNatCast 11))

noncomputable def Ns552p81 := @Enclosure.Real.IsNear.inv_image qz346 222574921 67108864 1 67108864 10117041 10117042 33554432 (@Enclosure.Real.IsNear.of_eq qz346 (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 222574921 67108864 1 67108864 (BSN.sqrt_enclosure 11 1 111287460 111287461 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

theorem RS553to564.d48 : Enclosure.Real.IsNear qz347 Bool.false 20234083 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 20234083 67108864 1 67108864 (Ns552p81 rfl rfl) rfl 

theorem RS553to564.d49 : Enclosure.Real.IsNear qz347 Bool.false 161872664 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 161872664 536870912 8 536870912 RS553to564.d48 rfl 

noncomputable def Ns552p82 := nat_lit 3004067793907357885399040 

noncomputable def Ns552p83 := BSN.log_dyadic_bound 4 20 6 5 106444800000000000 33554432 9610000 1454330814136320 990904320 13605151 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 20) 0 5 1454330814136320 106444800000000000 990904320 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz741 := (Enclosure.sfrac Bool.false 12 1)

noncomputable abbrev qz581 := qz741

noncomputable abbrev qz348 := qz581

noncomputable abbrev qz1 := qz348

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12) qz580)

theorem RS553to564.d50 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 11191024608564965 4503599627370496 100000002883 961000000000000000 := BSN.isNear_log_sfrac 12 1 11191024608564965 4503599627370496 100000002883 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false Ns552p82 Ns552p64 1000000028830000 9610000000000000000000 11191024608564965 4503599627370496 100000002883 961000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 13605151 33554432 24973259072661432 36028797018963968 9610000 1000000000000000 rfl rfl rfl rfl (Ns552p83 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS553to564.d51 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 1334074092 536870912 57 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 11191024608564965 4503599627370496 100000002883 961000000000000000 1334074092 536870912 57 536870912 RS553to564.d50 rfl 

noncomputable abbrev qz350 := (Real.sqrt (@Nat.cast Real Real.instNatCast 12))

noncomputable def Ns552p84 := @Enclosure.Real.IsNear.inv_image qz350 232471925 67108864 1 67108864 9686330 9686331 33554432 (@Enclosure.Real.IsNear.of_eq qz350 (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 232471925 67108864 1 67108864 (BSN.sqrt_enclosure 12 1 116235962 116235963 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz351 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

theorem RS553to564.d52 : Enclosure.Real.IsNear qz351 Bool.false 19372661 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 19372661 67108864 1 67108864 (Ns552p84 rfl rfl) rfl 

theorem RS553to564.d53 : Enclosure.Real.IsNear qz351 Bool.false 154981288 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 154981288 536870912 8 536870912 RS553to564.d52 rfl 

theorem RS553to564.d54 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz742 := (@instHMul Real Real.instMul)

noncomputable abbrev qz582 := (@HMul.hMul Real Real Real qz742 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz352 := qz582

noncomputable abbrev qz2 := qz352

theorem RS553to564.d55 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS553to564.d54 rfl 

noncomputable abbrev qz353 := (@Inv.inv Real Real.instInv qz582)

noncomputable abbrev qz3 := qz353

theorem RS553to564.d56 : Enclosure.Real.IsNear qz3 Bool.false 10680707 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 10680707 67108864 1 67108864 10680707 67108864 1 67108864 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 5340353 5340354 33554432 RS553to564.d55 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns552p85 := nat_lit 11877483121728884608592669 

noncomputable def Ns552p86 := nat_lit 11345485475094322625904640000 

noncomputable def Ns552p87 := nat_lit 6510926019426839762088950235136 

noncomputable abbrev qz743 := (Enclosure.sfrac Bool.false 944396 1000)

noncomputable abbrev qz583 := qz743

noncomputable abbrev qz354 := qz583

noncomputable abbrev qz4 := qz354

noncomputable abbrev qz584 := qz742

noncomputable abbrev qz355 := qz584

noncomputable abbrev qz5 := qz355

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz744 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 944396 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz585 := qz744

noncomputable abbrev qz356 := qz585

noncomputable abbrev qz8 := qz356

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz745 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 944396 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz586 := qz745

noncomputable abbrev qz357 := qz586

noncomputable abbrev qz10 := qz357

noncomputable abbrev qz587 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns552p88 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz10)) 307094083 268435456 271523 268435456 2645264569072738812669 18889465931478580854784 401501898689422331472669 Ns552p86 Ns552p87 

noncomputable def Ns552p89 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignPos 11 12 944396 1000 287 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 1334074092 57 154981288 8 

noncomputable def Ns552p90 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 944396 1000 178 235 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 

noncomputable def Ns552p91 := Ns552p90 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 458902982 218624 Bool.true 305498030 Bool.true 560599452 28296951008113761 1 Bool.false 452271673 Bool.true Bool.false 464136531 Bool.false Bool.true 461981425 

noncomputable def Ns552p92 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 7 8 9 944396 1000 44 115 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 

noncomputable def Ns552p93 := Ns552p92 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 643942597 178540 Bool.true 171727971 Bool.true 14566697 28296951008113761 1 Bool.false 509639126 Bool.false Bool.false 14564909 Bool.false Bool.true 458902982 

noncomputable def Ns552p94 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 944396 1000 128 36 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 

noncomputable def Ns552p95 := Ns552p94 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 926996619 132662 Bool.false 638325161 Bool.false 66015843 28296951008113761 1 Bool.false 200045008 Bool.false Bool.false 532817234 Bool.false Bool.true 643942597 

noncomputable def Ns552p96 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 944396 1000 372 238 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 

noncomputable def Ns552p97 := Ns552p96 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 907150088 78288 Bool.false 447915385 Bool.false 314145326 28296951008113761 1 Bool.false 360611321 Bool.false Bool.false 447553883 Bool.true Bool.true 926996619 

noncomputable def Ns552p98 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 944396 1000 789 545 536870912 268435456 9007199254740992 Bool.false 1017038251589 4497 

noncomputable def Ns552p99 := Ns552p98 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870640 4560 Bool.false 224232553 Bool.false 414639496 28296951008113761 1 Bool.false 217769820 Bool.true Bool.false 374630342 Bool.true Bool.true 907150088 

noncomputable def Ns552p100 := nat_lit 1662436099889779291033973740619078179481093101748477029 

noncomputable def Ns552p101 := nat_lit 877561471945275987067840912319735815298516779008000 

noncomputable def Ns552p102 := nat_lit 3936256000000000000000000 

noncomputable def Ns552p103 := nat_lit 360588806022495212747470990868480000 

noncomputable def Ns552p104 := nat_lit 2043232023588558628847452142088990228480 

noncomputable abbrev qz358 := (@Eq.refl Real qz583)

noncomputable abbrev qz11 := qz358

noncomputable def Ns552p105 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 944396 1000 3567536219264 16000000 1888792 4000 2000 Ns552p103 Ns552p104 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p106 := nat_lit 17431905958780252098752400490433905211275666802590110491607040 

noncomputable abbrev qz746 := (@instHSub Real Real.instSub)

noncomputable abbrev qz588 := qz746

noncomputable abbrev qz359 := qz588

noncomputable abbrev qz589 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz747 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz748 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz590 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1888792))))

noncomputable abbrev qz360 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 944396 4000) (Real.log (Enclosure.sfrac Bool.false 3567536219264 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz590))

noncomputable abbrev qz591 := (Enclosure.sfrac Bool.false 944396 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz360 qz591) (@HMul.hMul Real Real Real qz355 qz591 (Real.log Real.pi)))

noncomputable def Ns552p107 := @Enclosure.Real.IsNear.addLit_ft_p qz12 (Enclosure.sfrac Bool.true Ns552p103 Ns552p104) 8531536008383398071173 4503599627370496000 32963188780284025973 Ns552p102 Ns552p103 Ns552p104 0 1 Ns552p106 

noncomputable def Ns552p108 := nat_lit 143135422424426080254052794368000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz359 qz360 qz591)

noncomputable def Ns552p109 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (@HMul.hMul Real Real Real qz5 qz591 (Real.log Real.pi)) 10965907972652403706757 4503599627370496000 186015084829343 60062500000000000000 9068742261339 16777216000 708297 134217728000 Ns552p108 8531536008383398071173 4503599627370496000 

noncomputable def Ns552p110 := nat_lit 4386363189060961482702800 

noncomputable abbrev qz14 := qz360

noncomputable def Ns552p111 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz591 2618499741899499435393 900719925474099200 186015084829343 60062500000000000000 944396 2000 0 1 Ns552p110 10965907972652403706757 4503599627370496000 186015084829343 60062500000000000000 

noncomputable def Ns552p112 := nat_lit 5896337230944162804548711170613182464 

noncomputable def Ns552p113 := nat_lit 119101408995707121754439680 

noncomputable def Ns552p114 := nat_lit 9671406556917033397649408 

noncomputable def Ns552p115 := nat_lit 71010613871926202724469514972229619758619770183908556441165235655807722660642055850463281644157485064171197302009021174946281093262928746768136761130058548069333722939609867356628582400 

noncomputable def Ns552p116 := nat_lit 1662567049000434741980423933727546940456462808508030068581505240320445334656604861371437952466194746976999667238178473705247805407388092795362321892115723651466578486026140260960829440 

noncomputable def Ns552p117 := nat_lit 29840047400238486897455460243780501339204937752196364249722247926622174452821424675546988593197595571228097494813342615983812923010615100568015305525321927971985821060468572160 

noncomputable def Ns552p118 := BSN.log_dyadic_bound 1470384219264 5664688219264 8 7 Ns552p115 268435456 76880000 Ns552p116 Ns552p117 142618412 7135072438528 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1470384219264) (BSN.artanhQ 5664688219264) 0 7 Ns552p116 Ns552p115 Ns552p117 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz361 := (Real.log (Enclosure.sfrac Bool.false 3567536219264 16000000))

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns552p119 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 944396 4000) qz361 944396 4000 0 1 55460915433106535 4503599627370496 12500016337 961000000000000000 2618853334568203961393 900719925474099200 2951241357149363 961000000000000000000 (Enclosure.Real.IsNear.const Bool.false 944396 4000) (BSN.isNear_log_sfrac 3567536219264 16000000 55460915433106535 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3567536219264) qz362)) Bool.false Ns552p113 Ns552p114 1000001306960000 76880000000000000000000 55460915433106535 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3567536219264 16000000 17 7135072438528 4194304000000 142618412 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p120 := BSN.arctan_dyadic_bound_f 1000 1888792 1 0 33554432 9610000 0 1 1 0 1 1 17765 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1888792) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1888792) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz592 := qz747

noncomputable abbrev qz363 := qz592

noncomputable abbrev qz15 := qz363

noncomputable abbrev qz593 := qz748

noncomputable abbrev qz364 := qz593

noncomputable abbrev qz16 := qz364

noncomputable abbrev qz749 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz594 := qz749

noncomputable abbrev qz365 := qz594

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz365 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def Ns552p121 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1888792))) 884279719003555 562949953421312 1 2000000000000000 17765 33554432 1 9610000 29661502894361364398080 883981671761315 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p120 rfl) rfl rfl 

noncomputable abbrev qz366 := (@HMul.hMul Real Real Real qz584 qz589 qz590)

noncomputable abbrev qz18 := qz366

noncomputable abbrev qz367 := qz589

noncomputable abbrev qz19 := qz367

noncomputable abbrev qz368 := qz590

noncomputable abbrev qz20 := qz368

noncomputable abbrev qz369 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns552p122 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 944396 4000) qz361) qz18 2618853334568203961393 900719925474099200 2951241357149363 961000000000000000000 883981671761315 2251799813685248 200000000961 7688000000000000000 Ns552p112 2618499741899499435393 900719925474099200 186015084829343 60062500000000000000 (Ns552p119 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz20 1 4 0 1 883981671761315 562949953421312 200000000961 1922000000000000000 883981671761315 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p121 rfl) 

noncomputable def Ns552p123 := @Ns552p107 Ns552p100 Ns552p101 32963188780284025973 Ns552p102 (@Ns552p109 32963188780284025973 Ns552p102 (Ns552p111 (Ns552p122 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 944396 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz591 (Real.log Real.pi) 944396 2000 0 1 38410761 33554432 3 268435456 9068742261339 16777216000 708297 134217728000 (Enclosure.Real.IsNear.const Bool.false 944396 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p103 Ns552p104) 

noncomputable abbrev qz370 := (@instHAdd Real Real.instAdd)

noncomputable def Ns552p124 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns552p100 Ns552p101 32963188780284025973 Ns552p102 15891222681 8388608 563 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz370 qz12 (Enclosure.sfrac Bool.true Ns552p103 Ns552p104)) Bool.false Ns552p100 Ns552p101 32963188780284025973 Ns552p102 Ns552p105 (Ns552p123 rfl rfl)) 

noncomputable abbrev qz595 := (BSN.cosEvenQ 137438953472)

noncomputable abbrev qz596 := (BSN.cosOddQ 137438953472)

noncomputable def Ns552p125 := BSN.cos_dyadic_bound_f 136859047 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 136859047) qz595 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 136859047) qz596 0 0 rfl) rfl rfl 

noncomputable abbrev qz597 := (@Nat.cast Real Real.instNatCast 8388608)

noncomputable def Ns552p126 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15891222681) qz597) Bool.false 15891222681 8388608 563 67108864 Bool.true 67108830 67108864 1 9610000 (Ns552p124 rfl) (Enclosure.sfrac_false_div 15891222681 8388608) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 15891222681) qz597) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1203824909506672852992) (@Nat.cast Real Real.instNatCast Ns552p64)) 226375608064910080 72057594037927936 Bool.false 67108830 67108864 301 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q2 15891222681 8388608 226375608064910080 72057594037927936 301 1203824909506672852992 Ns552p64 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108830 67108864 1203824909506672852992 Ns552p64 136859047 137438953472 19238770 19220000 (Ns552p125 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p127 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns552p100 Ns552p101 32963188780284025973 Ns552p102 1017038251589 536870912 4497 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz370 qz12 (Enclosure.sfrac Bool.true Ns552p103 Ns552p104)) Bool.false Ns552p100 Ns552p101 32963188780284025973 Ns552p102 Ns552p105 (Ns552p123 rfl rfl)) 

noncomputable def Ns552p128 := Ns552p99 78288 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 789 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 217769820 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 545 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 374630342 536870912) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 33554415 33554432 342346179 40307261440000 536870640 536870912 4560 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 33554415 33554432 342346179 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 67108830 67108864 5477538864 644916183040000 33554415 33554432 342346179 40307261440000 (Ns552p126 rfl rfl) rfl)) rfl) (Ns552p127 rfl) RS553to564.d7 

noncomputable def Ns552p129 := nat_lit 635126598039239361360602070254218844702665865157467381567952078863290945 

noncomputable def Ns552p130 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480 

noncomputable def Ns552p131 := nat_lit 6391301318790713953530520289388863598335020568777197511563866231361 

noncomputable def Ns552p132 := nat_lit 1663416456567301237645652086966295106537346628236255598167712912668054081 

noncomputable def Ns552p133 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800 

noncomputable abbrev qz371 := (BSN.sinEvenQ 536870912)

noncomputable abbrev qz372 := (BSN.sinOddQ 536870912)

noncomputable def Ns552p134 := BSN.sin_dyadic_bound_f 224232553 536870912 3 2 536870912 268435456 Ns552p129 Ns552p130 Ns552p131 Ns552p132 Ns552p133 Ns552p131 217769820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 224232553) qz371 0 2 Ns552p129 Ns552p130 Ns552p131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 224232553) qz372 0 2 Ns552p132 Ns552p133 Ns552p131 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p135 := nat_lit 7426685802839117445275511123479322910980413366861464301919771604780318720 

noncomputable def Ns552p136 := nat_lit 873706051049441103657655365971155568645699713003110803708261523521536 

noncomputable def Ns552p137 := nat_lit 19449429197638846594887083405186654324504227685101830039917207493862752256 

noncomputable def Ns552p138 := BSN.sin_dyadic_bound_f 414639496 536870912 3 2 536870912 268435456 Ns552p135 Ns552p130 Ns552p136 Ns552p137 Ns552p133 Ns552p136 374630342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 414639496) qz371 0 2 Ns552p135 Ns552p130 Ns552p136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 414639496) qz372 0 2 Ns552p137 Ns552p133 Ns552p136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p139 := nat_lit 5619503299986999004706970222954151753694145712923467027084943555012690625 

noncomputable def Ns552p140 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720 

noncomputable def Ns552p141 := nat_lit 1620197056387915266697847447879570581167662146515389971725757687890625 

noncomputable def Ns552p142 := nat_lit 16855269505848221183587514973966696119920101814477370301311379149662290625 

noncomputable def Ns552p143 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400 

noncomputable abbrev qz373 := (BSN.cosEvenQ 536870912)

noncomputable abbrev qz374 := (BSN.cosOddQ 536870912)

noncomputable def Ns552p144 := BSN.cos_dyadic_bound_f 447915385 536870912 3 2 536870912 268435456 Ns552p139 Ns552p140 Ns552p141 Ns552p142 Ns552p143 Ns552p141 360611321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 447915385) qz373 0 2 Ns552p139 Ns552p140 Ns552p141 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 447915385) qz374 0 2 Ns552p142 Ns552p143 Ns552p141 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p145 := nat_lit 1359381930542691498973774907964200558158282129925516757401461559499571456 

noncomputable def Ns552p146 := nat_lit 94851634629517747195843204764887179769385232684611110835306491166976 

noncomputable def Ns552p147 := nat_lit 4077956088358815461426933037483071900115307619311181049982714065516380416 

noncomputable def Ns552p148 := BSN.cos_dyadic_bound_f 314145326 536870912 3 2 536870912 268435456 Ns552p145 Ns552p140 Ns552p146 Ns552p147 Ns552p143 Ns552p146 447553883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 314145326) qz373 0 2 Ns552p145 Ns552p140 Ns552p146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 314145326) qz374 0 2 Ns552p147 Ns552p143 Ns552p146 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p149 := Ns552p97 132662 BSN.abs_quadSignPos (BSN.cos_quad_nat0 372 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 360611321 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 447553883 536870912) qz11 rfl rfl (Ns552p128 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p134 rfl rfl) (Ns552p138 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p127 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p144 rfl rfl) (Ns552p148 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p150 := nat_lit 22896492634018098944384683906937561057112826792298044137375029238464800731419750147974748844021034176057905916001 

noncomputable def Ns552p151 := nat_lit 274647376664257459544000446540783031995164976078897331880025758552119769180746491160307949742358795015190845849600 

noncomputable def Ns552p152 := nat_lit 4576184874883066755249535503698956435489207218707120265757548760415682604933266805724000971320679163111521 

noncomputable def Ns552p153 := nat_lit 138795340677686938225981764919165594763826599102252426479980270088540616879283123349843293047873460023269477460065 

noncomputable def Ns552p154 := nat_lit 24992911276447428818504040635211255911560012823179657201082344028242898995447930695588023426554650346382366972313600 

noncomputable def Ns552p155 := BSN.cos_dyadic_bound_f 638325161 536870912 4 3 536870912 268435456 Ns552p150 Ns552p151 Ns552p152 Ns552p153 Ns552p154 Ns552p152 200045008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 638325161) qz373 0 3 Ns552p150 Ns552p151 Ns552p152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 638325161) qz374 0 3 Ns552p153 Ns552p154 Ns552p152 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p156 := nat_lit 18992961757714848531802046421201 

noncomputable def Ns552p157 := nat_lit 1993841993677373809355710590420516864 

noncomputable def Ns552p158 := nat_lit 29907629905160607140335658856307752960 

noncomputable def Ns552p159 := BSN.cos_dyadic_bound_f 66015843 536870912 2 1 536870912 268435456 Ns552p156 Ns552p157 Ns552p156 Ns552p156 Ns552p158 Ns552p156 532817234 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 66015843) qz373 0 1 Ns552p156 Ns552p157 Ns552p156 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 66015843) qz374 0 1 Ns552p156 Ns552p158 Ns552p156 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p160 := Ns552p95 178540 BSN.abs_quadSignPos (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 200045008 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 532817234 536870912) qz11 rfl rfl (Ns552p149 rfl rfl) (Ns552p127 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p155 rfl rfl) (Ns552p159 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p161 := nat_lit 121382377482960409010385377309816753327401056967109553938297507300231841 

noncomputable def Ns552p162 := nat_lit 756359575467275424049160969279103465452945744787838628422102796961 

noncomputable def Ns552p163 := nat_lit 364145619729730292480308033607511701775272265009839086137635677695101601 

noncomputable def Ns552p164 := BSN.cos_dyadic_bound_f 171727971 536870912 3 2 536870912 268435456 Ns552p161 Ns552p140 Ns552p162 Ns552p163 Ns552p143 Ns552p162 509639126 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 171727971) qz373 0 2 Ns552p161 Ns552p140 Ns552p162 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 171727971) qz374 0 2 Ns552p163 Ns552p143 Ns552p162 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p165 := BSN.sin_dyadic_bound_f 14566697 536870912 1 0 536870912 268435456 0 1 1 0 1 1 14564909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 14566697) qz371 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 14566697) qz372 0 0 rfl) rfl rfl 

noncomputable def Ns552p166 := Ns552p93 218624 BSN.abs_quadSignPos (BSN.cos_quad_nat0 44 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 509639126 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 14564909 536870912) qz11 rfl rfl (Ns552p160 rfl) (Ns552p127 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p164 rfl rfl) (Ns552p165 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p167 := nat_lit 1215764723591519463929148126397030368949317460015779831952657746608800000 

noncomputable def Ns552p168 := nat_lit 75869515793339540753574185625087385351560739121778181178736100000000 

noncomputable def Ns552p169 := nat_lit 3647142431742971712705937230819840932077249258569095939495615767626400000 

noncomputable def Ns552p170 := BSN.cos_dyadic_bound_f 305498030 536870912 3 2 536870912 268435456 Ns552p167 Ns552p140 Ns552p168 Ns552p169 Ns552p143 Ns552p168 452271673 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 305498030) qz373 0 2 Ns552p167 Ns552p140 Ns552p168 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 305498030) qz374 0 2 Ns552p169 Ns552p143 Ns552p168 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p171 := nat_lit 24822336870332610346560011093901132514163116379923368304047240276233748480 

noncomputable def Ns552p172 := nat_lit 9754866969035803495597932892957101956106879669043993284109145231917056 

noncomputable def Ns552p173 := nat_lit 64995088685302207225807156211723892705355417475573226711949452583570046976 

noncomputable def Ns552p174 := BSN.sin_dyadic_bound_f 560599452 536870912 3 2 536870912 268435456 Ns552p171 Ns552p130 Ns552p172 Ns552p173 Ns552p133 Ns552p172 464136531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 560599452) qz371 0 2 Ns552p171 Ns552p130 Ns552p172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 560599452) qz372 0 2 Ns552p173 Ns552p133 Ns552p172 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz598 := (BSN.cos_quad_nat3 235 rfl)

noncomputable def Ns552p175 := Ns552p91 254675 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 178 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 452271673 536870912) BSN.abs_quadSignPos qz598 (BSN.sfrac_eq_quadSignPos_mul Bool.false 464136531 536870912) qz11 rfl rfl (Ns552p166 rfl) (Ns552p127 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p170 rfl rfl) (Ns552p174 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p176 := nat_lit 165910560278547063806370928443197471919344257683186194773619270010612139546399007007952196306069514101258253438976 

noncomputable def Ns552p177 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800 

noncomputable def Ns552p178 := nat_lit 98866977452099539377259931948880138035482451707483864241473845835350428313396407674883400184167487671832576 

noncomputable def Ns552p179 := nat_lit 828610262147882852344741001578959282479407435777192875874745059082289412522168365160273264845721468044598543323136 

noncomputable def Ns552p180 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000 

noncomputable def Ns552p181 := BSN.sin_dyadic_bound_f 824620774 536870912 4 3 536870912 268435456 Ns552p176 Ns552p177 Ns552p178 Ns552p179 Ns552p180 Ns552p178 536545476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 824620774) qz371 0 3 Ns552p176 Ns552p177 Ns552p178 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 824620774) qz372 0 3 Ns552p179 Ns552p180 Ns552p178 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz375 := (BSN.cos_quad_nat3 287 rfl)

noncomputable def Ns552p182 := Ns552p89 Bool.true 461981425 254675 Bool.true 824620774 28296951008113761 1 Bool.false 536545476 Bool.false Bool.true 307094083 271523 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 536545476 536870912) qz11 rfl (Ns552p175 rfl) (Ns552p127 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p181 rfl rfl) rfl 

noncomputable def Ns552p183 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) 307094083 536870912 271523 536870912 307094083 536870912 271523 536870912 329739760820027392 307094083 268435456 271523 268435456 (Ns552p182 rfl rfl rfl rfl) 

noncomputable def Ns552p184 := @Enclosure.Real.IsNear.mulLit_ff qz587 (Zeta.RiemannSiegel.correction qz10) 9583107 33554432 1 33554432 276034126413567 562949953421312 83759069749030311 676243631547351040000 2645264569072738812669 18889465931478580854784 

noncomputable abbrev qz599 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns552p185 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz599 1 1 0 1 9583107 33554432 1 33554432 9583107 33554432 1 33554432 

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz356 (@HMul.hMul Real Real Real qz355 qz354 qz353) Bool.false 2521704241993 16777216000 236099 16777216000 (BSN.t_div_two_pi_mk qz354 944396 1000 qz358) (@Enclosure.Real.IsNear.mulLit_ff qz354 qz353 944396 1000 0 1 10680707 67108864 1 67108864 2521704241993 16777216000 236099 16777216000 (Enclosure.Real.IsNear.const Bool.false 944396 1000) RS553to564.d56 rfl))

noncomputable def Ns552p186 := @Enclosure.Real.IsNear.sqrt_image qz8 2521704241993 16777216000 236099 16777216000 411374149 411374189 33554432 qz21 

noncomputable abbrev qz750 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 944396 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz600 := qz750

noncomputable abbrev qz376 := qz600

noncomputable abbrev qz22 := qz376

noncomputable def Ns552p187 := @Enclosure.Real.IsNear.sqrt_image qz22 411374169 33554432 5 8388608 117487981 117487988 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 822748338 67108864 40 67108864 411374169 33554432 5 8388608 (Ns552p186 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz601 := (Real.sqrt qz750)

noncomputable abbrev qz377 := qz601

noncomputable abbrev qz23 := qz377

noncomputable def Ns552p188 := @Enclosure.Real.IsNear.inv_image qz23 234975969 67108864 7 67108864 9583106 9583108 33554432 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 234975969 67108864 7 67108864 234975969 67108864 7 67108864 (Ns552p187 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p189 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 19166214 67108864 2 67108864 9583107 33554432 1 33554432 (Ns552p188 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz378 := (@HMul.hMul Real Real Real qz584 qz582 qz586)

noncomputable abbrev qz24 := (Real.cos qz378)

noncomputable abbrev qz602 := (@HMul.hMul Real Real Real qz742 qz745 qz745)

noncomputable abbrev qz603 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz379 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz602 qz586) qz603)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz379))

noncomputable def Ns552p190 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 276034126413567 

noncomputable def Ns552p191 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz24) qz25 1078945291 67108864 66945 

noncomputable abbrev qz26 := (@Neg.neg Real Real.instNeg (Real.cos qz378))

noncomputable def Ns552p192 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz24) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz26)) Bool.true 1078945291 67108864 66945 67108864 (BSN.inv_eq_neg_inv_neg qz24) 

noncomputable def Ns552p193 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz26) Bool.false 1078945291 67108864 66945 67108864 1078945291 67108864 

noncomputable def Ns552p194 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true 2087038 33554432 622207216 161229045760000 1043519 16777216 38887951 10076815360000 

noncomputable abbrev qz27 := qz378

noncomputable abbrev qz380 := (@Nat.cast Real Real.instNatCast 67108864)

noncomputable def Ns552p195 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 109591129) qz380) Bool.false 109591129 67108864 63 16777216 Bool.true 2087038 33554432 1 

noncomputable def Ns552p196 := nat_lit 26986075412789679991559623 

noncomputable def Ns552p197 := nat_lit 7205759403792793600000000000000 

noncomputable def Ns552p198 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 8720985 33554432 5 8388608 7711790165234218101675 4722366482869645213696 Ns552p196 

noncomputable def Ns552p199 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 411374169 33554432 5 8388608 12 1 0 1 8720985 8720985 33554432 5 

noncomputable abbrev qz381 := (Enclosure.Real.IsNear.const Bool.false 12 1)

noncomputable def Ns552p200 := @Ns552p199 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 822748338 67108864 40 67108864 411374169 33554432 5 8388608 (Ns552p186 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p201 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 7711790165234218101675 4722366482869645213696 Ns552p196 Ns552p197 109591129 67108864 63 16777216 (@Ns552p198 Ns552p197 RS553to564.d55 (Ns552p200 rfl rfl) rfl) 

noncomputable def Ns552p202 := nat_lit 1189329284169715667436712322708891692078364575083455339570306111597892281500020069768394284610717737121 

noncomputable def Ns552p203 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns552p204 := nat_lit 3001268238875823009376492768544807050240391687162991056306572107949660617391002441455782923591841 

noncomputable def Ns552p205 := nat_lit 7194972380353163791524048998997877572459235455801959972380364813346438023244947643488005130905871704225 

noncomputable def Ns552p206 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable abbrev qz604 := (BSN.cosEvenQ 67108864)

noncomputable def Ns552p207 := BSN.cos_dyadic_bound_t 109591129 67108864 4 3 33554432 9610000 Ns552p202 Ns552p203 Ns552p204 Ns552p205 Ns552p206 Ns552p204 2087038 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 109591129) qz604 0 3 Ns552p202 Ns552p203 Ns552p204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 109591129) (BSN.cosOddQ 67108864) 0 3 Ns552p205 Ns552p206 Ns552p204 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p208 := @Enclosure.Real.IsNear.inv_image qz26 1043519 16777216 38887951 10076815360000 539439173 539506118 33554432 (@Enclosure.Real.IsNear.neg qz24 Bool.true 1043519 16777216 38887951 10076815360000 (Ns552p194 (@Ns552p195 9610000 (Ns552p201 rfl) (Enclosure.sfrac_false_div 109591129 67108864) (Ns552p207 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns552p209 := Ns552p192 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz26) Bool.false 1078945291 67108864 66945 67108864 (@Ns552p193 66945 67108864 (Ns552p208 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p210 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true 1023348 33554432 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz355 qz352 qz379)

noncomputable def Ns552p211 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 107461369)) qz380) Bool.true 107461369 67108864 

noncomputable def Ns552p212 := nat_lit 253735985671522966696354319245 

noncomputable def Ns552p213 := nat_lit 158456325028528675187087900672 

noncomputable def Ns552p214 := nat_lit 3440483224516682302125428447187401 

noncomputable def Ns552p215 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns552p212 Ns552p213 Ns552p214 

noncomputable def Ns552p216 := nat_lit 604462909807314587353088000000000000000 

noncomputable abbrev qz29 := qz379

noncomputable def Ns552p217 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 286940862962959 

noncomputable abbrev qz382 := (@HSub.hSub Real Real Real qz588 qz602 qz586)

noncomputable abbrev qz30 := qz382

noncomputable abbrev qz383 := qz603

noncomputable abbrev qz31 := qz383

noncomputable def Ns552p218 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 216572118785295 1125899906842624 127491055 140737488355328 1 16 

noncomputable abbrev qz384 := qz602

noncomputable abbrev qz32 := qz384

noncomputable def Ns552p219 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz10 76055579370225 1125899906842624 43604975 140737488355328 8720985 33554432 5 8388608 

noncomputable def Ns552p220 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 8720985 33554432 5 8388608 8720985 33554432 5 8388608 76055579370225 1125899906842624 

noncomputable def Ns552p221 := nat_lit 1099187009999796016510291896583407485431539517106718739647411551156000485013851547029485063023551556641 

noncomputable def Ns552p222 := nat_lit 2371528932311152324427443677431388961185348665268024937087631386624446281180620713007220261628961 

noncomputable def Ns552p223 := nat_lit 6651058569598329066063625622849497954448518135196809947054874702807942352816483491971920343707109010465 

noncomputable def Ns552p224 := BSN.cos_dyadic_bound_t 107461369 67108864 4 3 33554432 9610000 Ns552p221 Ns552p203 Ns552p222 Ns552p223 Ns552p206 Ns552p222 1023348 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 107461369) qz604 0 3 Ns552p221 Ns552p203 Ns552p222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 107461369) (BSN.cosOddQ 67108864) 0 3 Ns552p223 Ns552p206 Ns552p222 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz385 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns552p225 := @Ns552p210 3747738864 644916183040000 255837 8388608 234233679 40307261440000 (@Ns552p211 383 67108864 Bool.true 1023348 33554432 1 9610000 (@Ns552p215 Ns552p216 107461369 67108864 383 67108864 (@Ns552p217 1125899906842624 127491055 140737488355328 Ns552p212 Ns552p213 Ns552p214 Ns552p216 RS553to564.d55 (@Ns552p218 0 1 4591053807407344 286940862962959 1125899906842624 127491055 140737488355328 (@Ns552p219 7266954432877103677440 216572118785295 1125899906842624 127491055 140737488355328 (@Ns552p220 43604975 140737488355328 (Ns552p200 rfl rfl) (Ns552p200 rfl rfl) rfl) (Ns552p200 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 107461369 67108864) (BSN.cos_neg_of_bound 107461369 67108864 Bool.true 1023348 33554432 1 9610000 (Ns552p224 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns552p226 := @Ns552p184 401501898689422331472669 Ns552p86 (Ns552p185 qz33 (@Enclosure.Real.IsNear.of_eq qz599 (@Inv.inv Real Real.instInv qz23) Bool.false 9583107 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 944396 1000 qz11)) Ns552p189) rfl) (@Ns552p190 562949953421312 83759069749030311 676243631547351040000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 944396 1000 12 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 944396 1000 12 qz11 rfl rfl rfl))) (@Ns552p191 67108864 255837 8388608 234233679 40307261440000 276034126413567 562949953421312 83759069749030311 676243631547351040000 Ns552p209 (Ns552p225 rfl) rfl)) 

noncomputable abbrev qz34 := qz359

noncomputable def Ns552p227 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 24255089534174053974781 18889465931478580854784 Ns552p85 Ns552p86 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 qz587 (Zeta.RiemannSiegel.correction qz10))) Bool.true 24255089534174053974781 18889465931478580854784 Ns552p85 Ns552p86 (BSN.hardyZApproximantRS₀_eq qz4 12 (@BSN.floor_sqrt_eq_dec qz4 944396 1000 12 qz11 rfl rfl rfl)) (@Ns552p88 24255089534174053974781 18889465931478580854784 Ns552p85 Ns552p86 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12)) Bool.true 307094083 268435456 271523 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (Ns552p183 (Ns552p182 rfl rfl rfl rfl) rfl rfl)) (Ns552p226 rfl) rfl rfl)) 

theorem RS553to564.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 24255089534174053974781 18889465931478580854784 Ns552p85 Ns552p86 := Ns552p227 

theorem RS553to564.d58 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS553to564.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS553to564.d3 a b h)) 

noncomputable def Ns552p228 := nat_lit 11712944579108742707501499 

noncomputable def Ns552p229 := nat_lit 5626165412400376867520608468992 

noncomputable abbrev qz751 := (Enclosure.sfrac Bool.false 945649 1000)

noncomputable abbrev qz605 := qz751

noncomputable abbrev qz386 := qz605

noncomputable abbrev qz35 := qz386

noncomputable abbrev qz752 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 945649 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz606 := qz752

noncomputable abbrev qz387 := qz606

noncomputable abbrev qz36 := qz387

noncomputable abbrev qz753 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 945649 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz607 := qz753

noncomputable abbrev qz388 := qz607

noncomputable abbrev qz37 := qz388

noncomputable abbrev qz608 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz36 qz9))

noncomputable def Ns552p230 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HMul.hMul Real Real Real qz5 qz608 (Zeta.RiemannSiegel.correction qz37)) 334844943 268435456 67971 67108864 2603518704794386195095 18889465931478580854784 221705609132493322541499 Ns552p86 Ns552p229 

noncomputable def Ns552p231 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin BSN.quadSignPos 11 12 945649 1000 287 536870912 268435456 9007199254740992 Bool.false 1018724483773 4503 1334074092 57 154981288 8 

noncomputable def Ns552p232 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 945649 1000 178 235 536870912 268435456 9007199254740992 Bool.false 1018724483773 4503 

noncomputable def Ns552p233 := Ns552p232 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.false 214079342 218916 Bool.true 168213114 Bool.true 487429624 28296951008113761 1 Bool.false 510733413 Bool.true Bool.false 423171487 Bool.false Bool.false 180162248 

noncomputable def Ns552p234 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 945649 1000 43 114 536870912 268435456 9007199254740992 Bool.false 1018724483773 4503 

noncomputable def Ns552p235 := Ns552p234 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.false 91796909 178779 Bool.true 727649413 Bool.true 649720682 28296951008113761 1 Bool.false 524459337 Bool.false Bool.false 189425846 Bool.true Bool.false 214079342 

noncomputable def Ns552p236 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 945649 1000 129 36 536870912 268435456 9007199254740992 Bool.false 1018724483773 4503 

noncomputable def Ns552p237 := Ns552p236 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.false 61946147 132840 Bool.false 275927242 Bool.false 443235743 28296951008113761 1 Bool.false 263939013 Bool.true Bool.false 364064404 Bool.false Bool.false 91796909 

noncomputable def Ns552p238 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 945649 1000 373 239 536870912 268435456 9007199254740992 Bool.false 1018724483773 4503 

noncomputable def Ns552p239 := Ns552p238 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 194915713 78393 Bool.false 358273549 Bool.false 74394992 28296951008113761 1 Bool.false 332267296 Bool.true Bool.false 74157131 Bool.false Bool.false 61946147 

noncomputable def Ns552p240 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 945649 1000 790 546 536870912 268435456 9007199254740992 Bool.false 1018724483773 4503 

noncomputable def Ns552p241 := Ns552p240 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 536870888 4568 Bool.false 600870309 Bool.false 518521164 28296951008113761 1 Bool.false 234287802 Bool.true Bool.false 305340949 Bool.true Bool.false 194915713 

noncomputable def Ns552p242 := nat_lit 220003360752973119172220751130720644799192894457408677802911 

noncomputable def Ns552p243 := nat_lit 115942442546351169788002306966095264666338296338579456000 

noncomputable def Ns552p244 := nat_lit 15745024000000000000000000 

noncomputable def Ns552p245 := nat_lit 362987260467767959003929137559520000 

noncomputable def Ns552p246 := nat_lit 2059551507939814914536254998830871170880 

noncomputable abbrev qz609 := (@Eq.refl Real qz751)

noncomputable abbrev qz389 := qz609

noncomputable abbrev qz38 := qz389

noncomputable def Ns552p247 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 945649 1000 3577009124804 16000000 1891298 4000 2000 Ns552p245 Ns552p246 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p248 := nat_lit 70401075440951398135110640361830606335741726226370776896931520 

noncomputable abbrev qz610 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1891298))))

noncomputable abbrev qz390 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 945649 4000) (Real.log (Enclosure.sfrac Bool.false 3577009124804 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz610))

noncomputable abbrev qz611 := (Enclosure.sfrac Bool.false 945649 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz390 qz611) (@HMul.hMul Real Real Real qz355 qz611 (Real.log Real.pi)))

noncomputable def Ns552p249 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns552p245 Ns552p246) 34182724592487274791479 18014398509481984000 132027150473683464823 Ns552p244 Ns552p245 Ns552p246 0 1 Ns552p248 

noncomputable def Ns552p250 := nat_lit 2293963815826683945711992569856000 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz359 qz390 qz611)

noncomputable def Ns552p251 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz611 (Real.log Real.pi)) 43933131894674157879863 18014398509481984000 11920627949548213 3844000000000000000000 36323097728889 67108864000 2836947 536870912000 Ns552p250 34182724592487274791479 18014398509481984000 

noncomputable def Ns552p252 := nat_lit 87866263789348315759726000 

noncomputable abbrev qz41 := qz390

noncomputable def Ns552p253 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz611 52450780862720722223671 18014398509481984000 11920627949548213 3844000000000000000000 945649 2000 0 1 Ns552p252 43933131894674157879863 18014398509481984000 11920627949548213 3844000000000000000000 

noncomputable def Ns552p254 := nat_lit 118108658574320293659104951435849105408 

noncomputable def Ns552p255 := nat_lit 119127055518404318951636992 

noncomputable def Ns552p256 := nat_lit 72691294095223806059812489776047844283212708521585913887278405522797549856952961738417040217013439474913595438482565616971956466244969254897267140925335239387189608629046305922377318400 

noncomputable def Ns552p257 := nat_lit 1718868028004252926900502726411776099349381056712788020396189508570253233452005942831622031830270529267831439437414717072945645358558990776934516858721393193069048844875957642765271040 

noncomputable def Ns552p258 := nat_lit 32647119925783407156922010539443863609200304081638349685609890328052743742575862435040352000403202001808878698666169496225508000696469441785430733834393681676962565510985154560 

noncomputable def Ns552p259 := BSN.log_dyadic_bound 1479857124804 5674161124804 8 7 Ns552p256 268435456 76880000 Ns552p257 Ns552p258 143330246 7154018249608 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1479857124804) (BSN.artanhQ 5674161124804) 0 7 Ns552p257 Ns552p256 Ns552p258 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz391 := (Real.log (Enclosure.sfrac Bool.false 3577009124804 16000000))

noncomputable def Ns552p260 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 945649 4000) qz391 945649 4000 0 1 55472858025880679 4503599627370496 12500016337 961000000000000000 52457852719316038215671 18014398509481984000 11820627949067713 3844000000000000000000 (Enclosure.Real.IsNear.const Bool.false 945649 4000) (BSN.isNear_log_sfrac 3577009124804 16000000 55472858025880679 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3577009124804) qz362)) Bool.false Ns552p255 Ns552p114 1000001306960000 76880000000000000000000 55472858025880679 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3577009124804 16000000 17 7154018249608 4194304000000 143330246 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p261 := BSN.arctan_dyadic_bound_f 1000 1891298 1 0 33554432 9610000 0 1 1 0 1 1 17741 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1891298) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1891298) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p262 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1891298))) 884279719003555 562949953421312 1 2000000000000000 17741 33554432 1 9610000 29661516405160246509568 883982074414499 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p261 rfl) rfl rfl 

noncomputable abbrev qz392 := (@HMul.hMul Real Real Real qz584 qz589 qz610)

noncomputable abbrev qz42 := qz392

noncomputable abbrev qz393 := qz610

noncomputable abbrev qz43 := qz393

noncomputable def Ns552p263 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 945649 4000) qz391) qz42 52457852719316038215671 18014398509481984000 11820627949067713 3844000000000000000000 883982074414499 2251799813685248 200000000961 7688000000000000000 Ns552p254 52450780862720722223671 18014398509481984000 11920627949548213 3844000000000000000000 (Ns552p260 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz43 1 4 0 1 883982074414499 562949953421312 200000000961 1922000000000000000 883982074414499 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p262 rfl) 

noncomputable def Ns552p264 := @Ns552p249 Ns552p242 Ns552p243 132027150473683464823 Ns552p244 (@Ns552p251 132027150473683464823 Ns552p244 (Ns552p253 (Ns552p263 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 945649 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz611 (Real.log Real.pi) 945649 2000 0 1 38410761 33554432 3 268435456 36323097728889 67108864000 2836947 536870912000 (Enclosure.Real.IsNear.const Bool.false 945649 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p245 Ns552p246) 

noncomputable def Ns552p265 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns552p242 Ns552p243 132027150473683464823 Ns552p244 127340560471 67108864 141 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz370 qz39 (Enclosure.sfrac Bool.true Ns552p245 Ns552p246)) Bool.false Ns552p242 Ns552p243 132027150473683464823 Ns552p244 Ns552p247 (Ns552p264 rfl rfl)) 

noncomputable def Ns552p266 := BSN.cos_dyadic_bound_f 35091606 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 35091606) qz595 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 35091606) qz596 0 0 rfl) rfl rfl 

noncomputable abbrev qz394 := (@Nat.cast Real Real.instNatCast Ns552p114)

noncomputable def Ns552p267 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 127340560471) qz380) Bool.false 127340560471 67108864 141 16777216 Bool.false 67108861 67108864 1 9610000 (Ns552p265 rfl) (Enclosure.sfrac_false_div 127340560471 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 127340560471) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2469352275496509898752) qz394) 226375608064910080 72057594037927936 Bool.false 67108861 67108864 302 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q0 127340560471 67108864 226375608064910080 72057594037927936 302 2469352275496509898752 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108861 67108864 2469352275496509898752 Ns552p114 35091606 137438953472 19238770 19220000 (Ns552p266 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p268 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns552p242 Ns552p243 132027150473683464823 Ns552p244 1018724483773 536870912 4503 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz370 qz39 (Enclosure.sfrac Bool.true Ns552p245 Ns552p246)) Bool.false Ns552p242 Ns552p243 132027150473683464823 Ns552p244 Ns552p247 (Ns552p264 rfl rfl)) 

noncomputable def Ns552p269 := Ns552p241 78393 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 790 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 234287802 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 546 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 305340949 536870912) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 67108861 67108864 85736701 10076815360000 536870888 536870912 4568 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 67108861 67108864 85736701 10076815360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 67108861 67108864 1371787216 161229045760000 67108861 67108864 85736701 10076815360000 (Ns552p267 rfl rfl) rfl)) rfl) (Ns552p268 rfl) RS553to564.d7 

noncomputable def Ns552p270 := nat_lit 17972693922582083401595723712603979573198817886944497779744682244695213795040894899392697891371471707445279684561 

noncomputable def Ns552p271 := nat_lit 2214975543267432914777658727246004985592354105622453169966435461128622263845268452584019582272595516028881 

noncomputable def Ns552p272 := nat_lit 108966505195126494290495023585690927524983816474741849159119869983349630637852820513551407822798198778292090795985 

noncomputable def Ns552p273 := BSN.cos_dyadic_bound_f 600870309 536870912 4 3 536870912 268435456 Ns552p270 Ns552p151 Ns552p271 Ns552p272 Ns552p154 Ns552p271 234287802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 600870309) qz373 0 3 Ns552p270 Ns552p151 Ns552p271 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 600870309) qz374 0 3 Ns552p272 Ns552p154 Ns552p271 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p274 := nat_lit 9962665777920548021307527991957278159919416660208671213266494380810226978898855628061752904308934932279618174976 

noncomputable def Ns552p275 := nat_lit 377744237084821416111687593875203555610555074677992389932925313112376618490063020936939901447312817258496 

noncomputable def Ns552p276 := nat_lit 60419311797495211284194647151838265103813755126416531596847295476587789407657809493926943784754831464453520752640 

noncomputable def Ns552p277 := BSN.cos_dyadic_bound_f 518521164 536870912 4 3 536870912 268435456 Ns552p274 Ns552p151 Ns552p275 Ns552p276 Ns552p154 Ns552p275 305340949 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 518521164) qz373 0 3 Ns552p274 Ns552p151 Ns552p275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 518521164) qz374 0 3 Ns552p276 Ns552p154 Ns552p275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p278 := nat_lit 4139508215501715530368722207019812307506809744592206117540885755601477665 

noncomputable def Ns552p279 := nat_lit 271467576834446395775923275217489940914834392600876539316915923181601 

noncomputable def Ns552p280 := nat_lit 10841129616903903952039206666415822964518258646820138412495806734128242721 

noncomputable def Ns552p281 := BSN.sin_dyadic_bound_f 358273549 536870912 3 2 536870912 268435456 Ns552p278 Ns552p130 Ns552p279 Ns552p280 Ns552p133 Ns552p279 332267296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 358273549) qz371 0 2 Ns552p278 Ns552p130 Ns552p279 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 358273549) qz372 0 2 Ns552p280 Ns552p133 Ns552p279 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p282 := nat_lit 30631961368260632161401239044096 

noncomputable def Ns552p283 := nat_lit 9969209968386869046778552952102584320 

noncomputable def Ns552p284 := nat_lit 69784469778708083327449870664718090240 

noncomputable def Ns552p285 := BSN.sin_dyadic_bound_f 74394992 536870912 2 1 536870912 268435456 Ns552p282 Ns552p283 Ns552p282 Ns552p282 Ns552p284 Ns552p282 74157131 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 74394992) qz371 0 1 Ns552p282 Ns552p283 Ns552p282 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 74394992) qz372 0 1 Ns552p282 Ns552p284 Ns552p282 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p286 := Ns552p239 132840 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 373 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 332267296 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 74157131 536870912) qz38 rfl rfl (Ns552p269 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p273 rfl rfl) (Ns552p277 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p268 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p281 rfl rfl) (Ns552p285 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p287 := nat_lit 1456295892576742531910883763961118886576245026946727301541845335307772160 

noncomputable def Ns552p288 := nat_lit 33601343331892540094775545229930910485752275378982969597205555241216 

noncomputable def Ns552p289 := nat_lit 3814053887907026424225494507110653386225569566890815055420723259669012736 

noncomputable def Ns552p290 := BSN.sin_dyadic_bound_f 275927242 536870912 3 2 536870912 268435456 Ns552p287 Ns552p130 Ns552p288 Ns552p289 Ns552p133 Ns552p288 263939013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 275927242) qz371 0 2 Ns552p287 Ns552p130 Ns552p288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 275927242) qz372 0 2 Ns552p289 Ns552p133 Ns552p288 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p291 := nat_lit 5388252762260420814766117666408397640242447236791618746980072317569729281 

noncomputable def Ns552p292 := nat_lit 1489629282158889469143860762381935237110687911456639147723039775916801 

noncomputable def Ns552p293 := nat_lit 16161779028216944665360065277700429050253120334551942962644770873157354241 

noncomputable def Ns552p294 := BSN.cos_dyadic_bound_f 443235743 536870912 3 2 536870912 268435456 Ns552p291 Ns552p140 Ns552p292 Ns552p293 Ns552p143 Ns552p292 364064404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 443235743) qz373 0 2 Ns552p291 Ns552p140 Ns552p292 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 443235743) qz374 0 2 Ns552p293 Ns552p143 Ns552p292 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p295 := Ns552p237 178779 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 263939013 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 364064404 536870912) qz38 rfl rfl (Ns552p286 rfl rfl) (Ns552p268 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p290 rfl rfl) (Ns552p294 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p296 := nat_lit 100515087337663021843547107037076580268284655304756350469527229114121048662261440944829230074251768228780989696081 

noncomputable def Ns552p297 := nat_lit 22032622832293988372798758504204955515860114091232549474630158533307808999187897821800898225548545776896081 

noncomputable def Ns552p298 := nat_lit 502229042188621775475964026335274153623767842363373964683945909332965749706874524204722215890912649513778578933841 

noncomputable def Ns552p299 := BSN.sin_dyadic_bound_f 727649413 536870912 4 3 536870912 268435456 Ns552p296 Ns552p177 Ns552p297 Ns552p298 Ns552p180 Ns552p297 524459337 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 727649413) qz371 0 3 Ns552p296 Ns552p177 Ns552p297 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 727649413) qz372 0 3 Ns552p298 Ns552p180 Ns552p297 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p300 := nat_lit 24577954149383482920099415302796347493386502709301590953816034380818706294721668308769003362958239726274568851456 

noncomputable def Ns552p301 := nat_lit 5658747271529515803218242129359976832109904547057202448176251386705883425539249367241489752723200547557376 

noncomputable def Ns552p302 := nat_lit 148979470555029025620320979566143376006015356299615277079784258856747272064526632108787113359466098580651880550400 

noncomputable def Ns552p303 := BSN.cos_dyadic_bound_f 649720682 536870912 4 3 536870912 268435456 Ns552p300 Ns552p151 Ns552p301 Ns552p302 Ns552p154 Ns552p301 189425846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 649720682) qz373 0 3 Ns552p300 Ns552p151 Ns552p301 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 649720682) qz374 0 3 Ns552p302 Ns552p154 Ns552p301 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p304 := Ns552p235 218916 BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 524459337 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 189425846 536870912) qz38 rfl rfl (Ns552p295 rfl) (Ns552p268 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p299 rfl rfl) (Ns552p303 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p305 := nat_lit 111745662002871668187850603725399572157205731460628119239731215623495936 

noncomputable def Ns552p306 := nat_lit 641030664773439151434069934648063074389650546951455948856460288256 

noncomputable def Ns552p307 := nat_lit 335235703947285457685248943036329420345468415080790454807295933949911296 

noncomputable def Ns552p308 := BSN.cos_dyadic_bound_f 168213114 536870912 3 2 536870912 268435456 Ns552p305 Ns552p140 Ns552p306 Ns552p307 Ns552p143 Ns552p306 510733413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 168213114) qz373 0 2 Ns552p305 Ns552p140 Ns552p306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 168213114) qz374 0 2 Ns552p307 Ns552p143 Ns552p306 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p309 := nat_lit 14184255198910826662443321689488710488792618608980250774494979796752138240 

noncomputable def Ns552p310 := nat_lit 3186363822359501440338842906997702265896027184283079329767907053797376 

noncomputable def Ns552p311 := nat_lit 37144080931911202065971960583954340714597788503316579423810084761025642496 

noncomputable def Ns552p312 := BSN.sin_dyadic_bound_f 487429624 536870912 3 2 536870912 268435456 Ns552p309 Ns552p130 Ns552p310 Ns552p311 Ns552p133 Ns552p310 423171487 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 487429624) qz371 0 2 Ns552p309 Ns552p130 Ns552p310 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 487429624) qz372 0 2 Ns552p311 Ns552p133 Ns552p310 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p313 := Ns552p233 255014 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 178 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 510733413 536870912) BSN.abs_quadSignPos qz598 (BSN.sfrac_eq_quadSignPos_mul Bool.false 423171487 536870912) qz38 rfl rfl (Ns552p304 rfl) (Ns552p268 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p308 rfl rfl) (Ns552p312 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p314 := nat_lit 154420970357554589539514428201294136397521333196578899891691113998126167571549740297849333641783800850774312174321 

noncomputable def Ns552p315 := nat_lit 79746860550850775672901678466388346355558128479575495744781394886592603028680254667235670400220749133857521 

noncomputable def Ns552p316 := nat_lit 771288153328498266730293027758894599540001291160856625166527980971284562821015647517062494001638476494759672496881 

noncomputable def Ns552p317 := BSN.sin_dyadic_bound_f 809983427 536870912 4 3 536870912 268435456 Ns552p314 Ns552p177 Ns552p315 Ns552p316 Ns552p180 Ns552p315 535836559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 809983427) qz371 0 3 Ns552p314 Ns552p177 Ns552p315 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 809983427) qz372 0 3 Ns552p316 Ns552p180 Ns552p315 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p318 := Ns552p231 Bool.false 180162248 255014 Bool.true 809983427 28296951008113761 1 Bool.false 535836559 Bool.false Bool.false 334844943 271884 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 535836559 536870912) qz38 rfl (Ns552p313 rfl) (Ns552p268 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p317 rfl rfl) rfl 

noncomputable def Ns552p319 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) 334844943 536870912 271884 536870912 334844943 536870912 271884 536870912 359537019853996032 334844943 268435456 67971 67108864 (Ns552p318 rfl rfl rfl rfl) 

noncomputable def Ns552p320 := @Enclosure.Real.IsNear.mulLit_ff qz608 (Zeta.RiemannSiegel.correction qz37) 9579931 33554432 1 33554432 271768001752245 562949953421312 46251346768732989 676243631547351040000 2603518704794386195095 18889465931478580854784 

noncomputable abbrev qz612 := (@HPow.hPow Real Real Real qz7 qz36 qz9)

noncomputable def Ns552p321 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz612 1 1 0 1 9579931 33554432 1 33554432 9579931 33554432 1 33554432 

noncomputable def Ns552p322 := @Enclosure.Real.IsNear.sqrt_image qz36 10100199893843 67108864000 945649 67108864000 411646959 411646999 33554432 (@Enclosure.Real.IsNear.of_eq qz36 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 10100199893843 67108864000 945649 67108864000 (BSN.t_div_two_pi_mk qz35 945649 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 945649 1000 0 1 10680707 67108864 1 67108864 10100199893843 67108864000 945649 67108864000 (Enclosure.Real.IsNear.const Bool.false 945649 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz754 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 945649 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz613 := qz754

noncomputable abbrev qz395 := qz613

noncomputable abbrev qz44 := qz395

noncomputable def Ns552p323 := @Enclosure.Real.IsNear.sqrt_image qz44 411646979 33554432 5 8388608 117526932 117526939 33554432 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 823293958 67108864 40 67108864 411646979 33554432 5 8388608 (Ns552p322 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p324 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 235053871 67108864 7 67108864 9579930 9579932 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 235053871 67108864 7 67108864 235053871 67108864 7 67108864 (Ns552p323 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p325 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 19159862 67108864 2 67108864 9579931 33554432 1 33554432 (Ns552p324 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz396 := (@HMul.hMul Real Real Real qz584 qz582 qz607)

noncomputable abbrev qz45 := (Real.cos qz396)

noncomputable abbrev qz614 := (@HMul.hMul Real Real Real qz742 qz753 qz753)

noncomputable abbrev qz397 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz614 qz607) qz603)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz397))

noncomputable def Ns552p326 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 271768001752245 

noncomputable def Ns552p327 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz45) qz46 296729155 33554432 10127 

noncomputable abbrev qz47 := (@Neg.neg Real Real.instNeg (Real.cos qz396))

noncomputable def Ns552p328 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz45) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz47)) Bool.true 296729155 33554432 10127 33554432 (BSN.inv_eq_neg_inv_neg qz45) 

noncomputable def Ns552p329 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz47) Bool.false 593458310 67108864 20254 67108864 296729155 33554432 

noncomputable def Ns552p330 := @Enclosure.Real.IsNear.recentre' qz45 Bool.true 3794369 33554432 622207216 161229045760000 3794369 33554432 38887951 10076815360000 

noncomputable abbrev qz48 := qz396

noncomputable def Ns552p331 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 113019361) qz380) Bool.false 113019361 67108864 63 16777216 Bool.true 3794369 33554432 1 

noncomputable def Ns552p332 := nat_lit 26986075412906850994361799 

noncomputable def Ns552p333 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 8993795 33554432 5 8388608 7953030515375577941225 4722366482869645213696 Ns552p332 

noncomputable def Ns552p334 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 411646979 33554432 5 8388608 12 1 0 1 8993795 8993795 33554432 5 

noncomputable def Ns552p335 := @Ns552p334 8388608 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 823293958 67108864 40 67108864 411646979 33554432 5 8388608 (Ns552p322 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p336 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 7953030515375577941225 4722366482869645213696 Ns552p332 Ns552p197 113019361 67108864 63 16777216 (@Ns552p333 Ns552p197 RS553to564.d55 (Ns552p335 rfl rfl) rfl) 

noncomputable def Ns552p337 := nat_lit 1346022089359785712183906553991232568311856158530909933377747168791752573289220379993503551159858396801 

noncomputable def Ns552p338 := nat_lit 4343443436074391001575778892486702120892729281618373088540491493151783220865448842734341644385921 

noncomputable def Ns552p339 := nat_lit 8139902487760763085023216560140770704317935348553298489704101492676922718785534549310602338218849107585 

noncomputable def Ns552p340 := BSN.cos_dyadic_bound_t 113019361 67108864 4 3 33554432 9610000 Ns552p337 Ns552p203 Ns552p338 Ns552p339 Ns552p206 Ns552p338 3794369 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 113019361) qz604 0 3 Ns552p337 Ns552p203 Ns552p338 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 113019361) (BSN.cosOddQ 67108864) 0 3 Ns552p339 Ns552p206 Ns552p338 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p341 := @Enclosure.Real.IsNear.inv_image qz47 3794369 33554432 38887951 10076815360000 296719028 296739282 33554432 (@Enclosure.Real.IsNear.neg qz45 Bool.true 3794369 33554432 38887951 10076815360000 (Ns552p330 (@Ns552p331 9610000 (Ns552p336 rfl) (Enclosure.sfrac_false_div 113019361 67108864) (Ns552p340 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns552p342 := Ns552p328 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz47) Bool.false 296729155 33554432 10127 33554432 (@Ns552p329 10127 33554432 (Ns552p341 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p343 := @Enclosure.Real.IsNear.recentre' qz46 Bool.true 1831758 33554432 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz355 qz352 qz397)

noncomputable def Ns552p344 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 109079695)) qz380) Bool.true 109079695 67108864 

noncomputable def Ns552p345 := nat_lit 257557148866120257361602155845 

noncomputable def Ns552p346 := nat_lit 3477293580683028702100745408330631 

noncomputable def Ns552p347 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns552p345 Ns552p213 Ns552p346 

noncomputable abbrev qz50 := qz397

noncomputable def Ns552p348 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 291262078425079 

noncomputable abbrev qz398 := (@HSub.hSub Real Real Real qz588 qz614 qz607)

noncomputable abbrev qz51 := qz398

noncomputable def Ns552p349 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 220893334247415 1125899906842624 128855105 140737488355328 1 16 

noncomputable abbrev qz399 := qz614

noncomputable abbrev qz52 := qz399

noncomputable def Ns552p350 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 80888348502025 1125899906842624 44969025 140737488355328 8993795 33554432 5 8388608 

noncomputable def Ns552p351 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 8993795 33554432 5 8388608 8993795 33554432 5 8388608 80888348502025 1125899906842624 

noncomputable def Ns552p352 := nat_lit 1167191700926626641999710612527453487608946074239942758808158650161068702695516537778966851733641890625 

noncomputable def Ns552p353 := nat_lit 2837441910334948844764457501062932972392636560811702695352725827241819399041447983800371337890625 

noncomputable def Ns552p354 := nat_lit 7061416633186696259235302526327095546633684348624531999928327592411953233373096978005786066772515490625 

noncomputable def Ns552p355 := BSN.cos_dyadic_bound_t 109079695 67108864 4 3 33554432 9610000 Ns552p352 Ns552p203 Ns552p353 Ns552p354 Ns552p206 Ns552p353 1831758 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 109079695) qz604 0 3 Ns552p352 Ns552p203 Ns552p353 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 109079695) (BSN.cosOddQ 67108864) 0 3 Ns552p354 Ns552p206 Ns552p353 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p356 := @Ns552p343 3786178864 644916183040000 915879 16777216 236636179 40307261440000 (@Ns552p344 387 67108864 Bool.true 1831758 33554432 1 9610000 (@Ns552p347 Ns552p216 109079695 67108864 387 67108864 (@Ns552p348 1125899906842624 128855105 140737488355328 Ns552p345 Ns552p213 Ns552p346 Ns552p216 RS553to564.d55 (@Ns552p349 0 1 4660193254801264 291262078425079 1125899906842624 128855105 140737488355328 (@Ns552p350 7411950363258157793280 220893334247415 1125899906842624 128855105 140737488355328 (@Ns552p351 44969025 140737488355328 (Ns552p335 rfl rfl) (Ns552p335 rfl rfl) rfl) (Ns552p335 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 109079695 67108864) (BSN.cos_neg_of_bound 109079695 67108864 Bool.true 1831758 33554432 1 9610000 (Ns552p355 rfl rfl)) rfl rfl) 

noncomputable def Ns552p357 := @Ns552p320 221705609132493322541499 Ns552p86 (Ns552p321 qz33 (@Enclosure.Real.IsNear.of_eq qz612 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 9579931 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz36 (BSN.t_div_two_pi_nonneg qz35 945649 1000 qz38)) Ns552p325) rfl) (@Ns552p326 562949953421312 46251346768732989 676243631547351040000 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 945649 1000 12 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 945649 1000 12 qz38 rfl rfl rfl))) (@Ns552p327 33554432 915879 16777216 236636179 40307261440000 271768001752245 562949953421312 46251346768732989 676243631547351040000 Ns552p342 (Ns552p356 rfl) rfl)) 

noncomputable def Ns552p358 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 20959099428357097758057 18889465931478580854784 Ns552p228 Ns552p86 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HMul.hMul Real Real Real qz5 qz608 (Zeta.RiemannSiegel.correction qz37))) Bool.false 20959099428357097758057 18889465931478580854784 Ns552p228 Ns552p86 (BSN.hardyZApproximantRS₀_eq qz35 12 (@BSN.floor_sqrt_eq_dec qz35 945649 1000 12 qz38 rfl rfl rfl)) (@Ns552p230 20959099428357097758057 18889465931478580854784 Ns552p228 Ns552p86 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12)) Bool.false 334844943 268435456 67971 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (Ns552p319 (Ns552p318 rfl rfl rfl rfl) rfl rfl)) (Ns552p357 rfl) rfl rfl)) 

theorem RS553to564.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 20959099428357097758057 18889465931478580854784 Ns552p228 Ns552p86 := Ns552p358 

noncomputable abbrev qz615 := (@HMul.hMul Real Real Real qz742 (Real.sqrt qz750) qz744)

noncomputable abbrev qz400 := qz615

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz400)

noncomputable abbrev qz401 := (@HMul.hMul Real Real Real qz584 (@HMul.hMul Real Real Real qz584 qz615 qz615) qz615)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz355 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz401))

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz584 qz601 qz601)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz355 qz402 qz377))

noncomputable abbrev qz616 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns552p359 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz370 (@HAdd.hAdd Real Real Real qz370 qz616 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns552p360 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz370 qz616 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 25503001 2147483648 

noncomputable def Ns552p361 := @Enclosure.Real.IsNear.addLit_ff qz616 qz54 3187875 268435456 25 268435456 

noncomputable def Ns552p362 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 127515 67108864 1 67108864 3187875 

noncomputable def Ns552p363 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 127515 67108864 1 67108864 127515 67108864 1 67108864 

noncomputable def Ns552p364 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz8 234975969 67108864 7 67108864 2521704241993 16777216000 236099 16777216000 592539897793715666217 1125899906842624000 2925180906063 

noncomputable def Ns552p365 := @Enclosure.Real.IsNear.sqrt_image qz8 2521704241993 16777216000 236099 16777216000 411374149 411374189 33554432 qz21 

noncomputable def Ns552p366 := @Enclosure.Real.IsNear.sqrt_image qz22 411374169 33554432 5 8388608 117487981 117487988 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 822748338 67108864 40 67108864 411374169 33554432 5 8388608 (Ns552p365 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz403 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 234975969 67108864 7 67108864 234975969 67108864 7 67108864 (Ns552p366 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns552p367 := @Ns552p364 45035996273704960 qz403 

noncomputable def Ns552p368 := Ns552p367 qz21 

noncomputable abbrev qz56 := qz400

noncomputable def Ns552p369 := @Enclosure.Real.IsNear.inv_image qz56 592539897793715666217 1125899906842624000 2925180906063 45035996273704960 63757 63758 33554432 (Ns552p368 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz401)

noncomputable def Ns552p370 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns552p371 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 67108864 1 67108864 

noncomputable def Ns552p372 := nat_lit 208042850064083631061614294209246604791522146696092261955040313 

noncomputable def Ns552p373 := nat_lit 1427247692705959881058285969449495136382746624000000000 

noncomputable def Ns552p374 := nat_lit 3081124410474518909142685970888796353727953015377192671 

noncomputable def Ns552p375 := nat_lit 57089907708238395242331438777979805455309864960000000 

noncomputable abbrev qz58 := qz401

noncomputable def Ns552p376 := @Enclosure.Real.IsNear.inv_image qz58 Ns552p372 Ns552p373 Ns552p374 Ns552p375 0 1 

noncomputable def Ns552p377 := nat_lit 351103530477387007844999678096296155091089 

noncomputable def Ns552p378 := nat_lit 1267650600228229401496703205376000000 

noncomputable def Ns552p379 := nat_lit 3466573004130480544232924233146567 

noncomputable def Ns552p380 := nat_lit 50706024009129176059868128215040000 

noncomputable abbrev qz404 := (@HMul.hMul Real Real Real qz584 qz615 qz615)

noncomputable abbrev qz59 := qz404

noncomputable def Ns552p381 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns552p377 Ns552p378 Ns552p379 Ns552p380 592539897793715666217 1125899906842624000 2925180906063 

noncomputable def Ns552p382 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 592539897793715666217 1125899906842624000 2925180906063 45035996273704960 592539897793715666217 1125899906842624000 2925180906063 45035996273704960 Ns552p377 

noncomputable def Ns552p383 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 1563325 67108864 1 

noncomputable def Ns552p384 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 1563325 67108864 1 67108864 1563325 67108864 

noncomputable def Ns552p385 := nat_lit 12973894071190839867778209 

noncomputable abbrev qz60 := qz402

noncomputable def Ns552p386 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz23 55213706007488961 4503599627370496 3289663615 4503599627370496 234975969 67108864 7 67108864 Ns552p385 

noncomputable def Ns552p387 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 234975969 67108864 7 67108864 234975969 67108864 7 67108864 55213706007488961 4503599627370496 3289663615 

noncomputable def Ns552p388 := @Ns552p387 4503599627370496 qz403 

noncomputable def Ns552p389 := Ns552p388 qz403 

noncomputable def Ns552p390 := @Ns552p386 302231454903657293676544 1159487860698735967 302231454903657293676544 (Ns552p389 rfl) qz403 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz355 qz402 qz377)

noncomputable def Ns552p391 := @Enclosure.Real.IsNear.inv_image qz61 Ns552p385 302231454903657293676544 1159487860698735967 302231454903657293676544 781662 781663 33554432 (Ns552p390 rfl) 

noncomputable def Ns552p392 := @Ns552p360 201 2147483648 4064645 134217728 13 671088640 12151713523826688 90537321 2147483648 1213 10737418240 (@Ns552p361 1 2147483648 1 2147483648 6845909702803456 25503001 2147483648 201 2147483648 (@Ns552p362 268435456 25 268435456 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns552p363 (Ns552p369 rfl rfl rfl rfl) rfl) rfl) (@Ns552p370 67108864 1 67108864 1 2147483648 1 2147483648 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns552p371 1 67108864 1 67108864 (@Ns552p376 33554432 (@Ns552p381 45035996273704960 Ns552p372 Ns552p373 Ns552p374 Ns552p375 (@Ns552p382 Ns552p378 Ns552p379 Ns552p380 (Ns552p368 rfl) (Ns552p368 rfl) rfl) (Ns552p368 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns552p383 67108864 4064645 134217728 13 671088640 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns552p384 1 67108864 (Ns552p391 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS553to564.d60 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 := @Ns552p359 90537321 2147483648 1213 10737418240 (BSN.hardyZErrorBoundRS₀_mk qz4 944396 1000 qz11 rfl rfl) (Ns552p392 rfl rfl) 

noncomputable def Ns552p393 := nat_lit 46639633522684304375319647 

noncomputable def Ns552p394 := nat_lit 45381941900377290503618560000 

noncomputable def Ns552p395 := nat_lit 201999273695847258463534055424 

noncomputable abbrev qz755 := (Enclosure.sfrac Bool.false 946902 1000)

noncomputable abbrev qz617 := qz755

noncomputable abbrev qz405 := qz617

noncomputable abbrev qz62 := qz405

noncomputable abbrev qz756 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 946902 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz618 := qz756

noncomputable abbrev qz406 := qz618

noncomputable abbrev qz63 := qz406

noncomputable abbrev qz757 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 946902 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz619 := qz757

noncomputable abbrev qz407 := qz619

noncomputable abbrev qz64 := qz407

noncomputable abbrev qz620 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns552p396 := @Enclosure.Real.IsNear.subLit_ff_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HMul.hMul Real Real Real qz5 qz620 (Zeta.RiemannSiegel.correction qz64)) 15042373 268435456 272235 268435456 1281762383326492778315 9444732965739290427392 615337264111026781719647 Ns552p394 Ns552p395 

noncomputable def Ns552p397 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin BSN.quadSignPos 11 12 946902 1000 287 536870912 268435456 9007199254740992 Bool.false 1020411161899 4508 1334074092 57 154981288 8 

noncomputable def Ns552p398 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 946902 1000 178 235 536870912 268435456 9007199254740992 Bool.false 1020411161899 4508 

noncomputable def Ns552p399 := Ns552p398 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 82586088 219197 Bool.true 30482256 Bool.true 413813854 28296951008113761 1 Bool.false 536005789 Bool.true Bool.false 374038501 Bool.false Bool.true 139309162 

noncomputable def Ns552p400 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 946902 1000 43 114 536870912 268435456 9007199254740992 Bool.false 1020411161899 4508 

noncomputable def Ns552p401 := Ns552p400 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 99390724 179007 Bool.true 439810057 Bool.true 441113869 28296951008113761 1 Bool.false 392241482 Bool.false Bool.false 365621025 Bool.true Bool.true 82586088 

noncomputable def Ns552p402 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 946902 1000 129 36 536870912 268435456 9007199254740992 Bool.false 1020411161899 4508 

noncomputable def Ns552p403 := Ns552p402 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.false 108509306 133008 Bool.false 757290121 Bool.false 820901585 28296951008113761 1 Bool.false 529993620 Bool.true Bool.false 22406761 Bool.false Bool.true 99390724 

noncomputable def Ns552p404 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 946902 1000 374 239 536870912 268435456 9007199254740992 Bool.false 1020411161899 4508 

noncomputable def Ns552p405 := Ns552p404 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 115071475 78490 Bool.false 269077655 Bool.false 678405457 28296951008113761 1 Bool.false 470840326 Bool.true Bool.false 511742007 Bool.false Bool.false 108509306 

noncomputable def Ns552p406 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 946902 1000 792 547 536870912 268435456 9007199254740992 Bool.false 1020411161899 4508 

noncomputable def Ns552p407 := Ns552p406 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870872 4568 Bool.false 134639150 Bool.false 622848775 28296951008113761 1 Bool.false 520076473 Bool.false Bool.false 492236270 Bool.false Bool.false 115071475 

noncomputable def Ns552p408 := nat_lit 192817163112202052336208111903634722024845095711758589793 

noncomputable def Ns552p409 := nat_lit 101447269565972361240283829672729866089926745915392000 

noncomputable def Ns552p410 := nat_lit 7872512000000000000000000 

noncomputable def Ns552p411 := nat_lit 365398460614781993765655816975360000 

noncomputable def Ns552p412 := nat_lit 2075979469040592564766835646547790008320 

noncomputable abbrev qz621 := (@Eq.refl Real qz755)

noncomputable abbrev qz408 := qz621

noncomputable abbrev qz65 := qz408

noncomputable def Ns552p413 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 946902 1000 3586494590416 16000000 1893804 4000 2000 Ns552p411 Ns552p412 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p414 := nat_lit 35540059504841082286609879186077951963619448041591343270645760 

noncomputable abbrev qz622 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1893804))))

noncomputable abbrev qz409 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 946902 4000) (Real.log (Enclosure.sfrac Bool.false 3586494590416 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz622))

noncomputable abbrev qz623 := (Enclosure.sfrac Bool.false 946902 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz409 qz623) (@HMul.hMul Real Real Real qz355 qz623 (Real.log Real.pi)))

noncomputable def Ns552p415 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns552p411 Ns552p412) 17119660057371643259693 9007199254740992000 66100772913115412877 Ns552p410 Ns552p411 Ns552p412 0 1 Ns552p414 

noncomputable def Ns552p416 := nat_lit 574440469258192902485627109376000 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz359 qz409 qz623)

noncomputable def Ns552p417 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz623 (Real.log Real.pi)) 22001323431020515076909 9007199254740992000 5968145235009237 1922000000000000000000 18185613206211 33554432000 1420353 268435456000 Ns552p416 17119660057371643259693 9007199254740992000 

noncomputable def Ns552p418 := nat_lit 44002646862041030153818000 

noncomputable abbrev qz68 := qz409

noncomputable def Ns552p419 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz623 26265790925376892480301 9007199254740992000 5968145235009237 1922000000000000000000 946902 2000 0 1 Ns552p418 22001323431020515076909 9007199254740992000 5968145235009237 1922000000000000000000 

noncomputable def Ns552p420 := nat_lit 59145303112059364141695562802054299648 

noncomputable def Ns552p421 := nat_lit 119152668101974724284776448 

noncomputable def Ns552p422 := nat_lit 74411151265991147444647623732779756706103887464262025850529653396956405440243938441507308953220349505371337815310527821281084281160956892156899986202657028391243071605873736868587110400 

noncomputable def Ns552p423 := nat_lit 1776950001703791560805148597138588875578373421436915985609896806980649538184681312066784173912182873160951632703667855953787969679637662220338198773423757222904520810773044829345546240 

noncomputable def Ns552p424 := nat_lit 35701985850299222984339266134058325713050107497473579848732210827257054019974387789400366021103649424283046419638527449305230269664458743240832040932278084307460590084145807360 

noncomputable def Ns552p425 := BSN.log_dyadic_bound 1489342590416 5683646590416 8 7 Ns552p422 268435456 76880000 Ns552p423 Ns552p424 144041138 7172989180832 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1489342590416) (BSN.artanhQ 5683646590416) 0 7 Ns552p423 Ns552p422 Ns552p424 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz410 := (Real.log (Enclosure.sfrac Bool.false 3586494590416 16000000))

noncomputable def Ns552p426 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 946902 4000) qz410 946902 4000 0 1 55484784814517351 4503599627370496 12500016337 961000000000000000 26269326855218054348301 9007199254740992000 5918145234768987 1922000000000000000000 (Enclosure.Real.IsNear.const Bool.false 946902 4000) (BSN.isNear_log_sfrac 3586494590416 16000000 55484784814517351 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3586494590416) qz362)) Bool.false Ns552p421 Ns552p114 1000001306960000 76880000000000000000000 55484784814517351 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3586494590416 16000000 17 7172989180832 4194304000000 144041138 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p425 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p427 := BSN.arctan_dyadic_bound_f 1000 1893804 1 0 33554432 9610000 0 1 1 0 1 1 17718 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1893804) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1893804) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p428 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1893804))) 884279719003555 562949953421312 1 2000000000000000 17718 33554432 1 9610000 29661529353009175199744 883982460290467 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p427 rfl) rfl rfl 

noncomputable abbrev qz411 := (@HMul.hMul Real Real Real qz584 qz589 qz622)

noncomputable abbrev qz69 := qz411

noncomputable abbrev qz412 := qz622

noncomputable abbrev qz70 := qz412

noncomputable def Ns552p429 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 946902 4000) qz410) qz69 26269326855218054348301 9007199254740992000 5918145234768987 1922000000000000000000 883982460290467 2251799813685248 200000000961 7688000000000000000 Ns552p420 26265790925376892480301 9007199254740992000 5968145235009237 1922000000000000000000 (Ns552p426 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz70 1 4 0 1 883982460290467 562949953421312 200000000961 1922000000000000000 883982460290467 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p428 rfl) 

noncomputable def Ns552p430 := @Ns552p415 Ns552p408 Ns552p409 66100772913115412877 Ns552p410 (@Ns552p417 66100772913115412877 Ns552p410 (Ns552p419 (Ns552p429 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 946902 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz623 (Real.log Real.pi) 946902 2000 0 1 38410761 33554432 3 268435456 18185613206211 33554432000 1420353 268435456000 (Enclosure.Real.IsNear.const Bool.false 946902 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p411 Ns552p412) 

noncomputable def Ns552p431 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns552p408 Ns552p409 66100772913115412877 Ns552p410 127551395237 67108864 141 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz370 qz66 (Enclosure.sfrac Bool.true Ns552p411 Ns552p412)) Bool.false Ns552p408 Ns552p409 66100772913115412877 Ns552p410 Ns552p413 (Ns552p430 rfl rfl)) 

noncomputable def Ns552p432 := BSN.cos_dyadic_bound_f 47485829 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 47485829) qz595 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 47485829) qz596 0 0 rfl) rfl rfl 

noncomputable def Ns552p433 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 127551395237) qz380) Bool.false 127551395237 67108864 141 16777216 Bool.true 67108859 67108864 1 9610000 (Ns552p431 rfl) (Enclosure.sfrac_false_div 127551395237 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 127551395237) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3341518203852070846464) qz394) 226375608064910080 72057594037927936 Bool.false 67108859 67108864 302 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q2 127551395237 67108864 226375608064910080 72057594037927936 302 3341518203852070846464 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108859 67108864 3341518203852070846464 Ns552p114 47485829 137438953472 19238770 19220000 (Ns552p432 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p434 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns552p408 Ns552p409 66100772913115412877 Ns552p410 1020411161899 536870912 4508 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz370 qz66 (Enclosure.sfrac Bool.true Ns552p411 Ns552p412)) Bool.false Ns552p408 Ns552p409 66100772913115412877 Ns552p410 Ns552p413 (Ns552p430 rfl rfl)) 

noncomputable def Ns552p435 := Ns552p407 78490 BSN.abs_quadSignPos (BSN.cos_quad_nat0 792 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 520076473 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 547 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 492236270 536870912) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 67108859 67108864 85736701 10076815360000 536870872 536870912 4568 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 67108859 67108864 85736701 10076815360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 67108859 67108864 1371787216 161229045760000 67108859 67108864 85736701 10076815360000 (Ns552p433 rfl rfl) rfl)) rfl) (Ns552p434 rfl) RS553to564.d7 

noncomputable def Ns552p436 := nat_lit 328613533130039834473362006250000 

noncomputable def Ns552p437 := BSN.cos_dyadic_bound_f 134639150 536870912 2 1 536870912 268435456 Ns552p436 Ns552p157 Ns552p436 Ns552p436 Ns552p158 Ns552p436 520076473 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 134639150) qz373 0 1 Ns552p436 Ns552p157 Ns552p436 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 134639150) qz374 0 1 Ns552p436 Ns552p158 Ns552p436 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p438 := nat_lit 53932262569114412752216008184829536433371245129243106653943321477255435032772392251724998398637211338495025390625 

noncomputable def Ns552p439 := nat_lit 3408720367158607420000232868797924342248002381410327812410353220811922198158634285270118772983551025390625 

noncomputable def Ns552p440 := nat_lit 269561496134071728159741143358699850830442185357991113175276410836428494970808692026634772620640564758271025390625 

noncomputable def Ns552p441 := BSN.sin_dyadic_bound_f 622848775 536870912 4 3 536870912 268435456 Ns552p438 Ns552p177 Ns552p439 Ns552p440 Ns552p180 Ns552p439 492236270 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 622848775) qz371 0 3 Ns552p438 Ns552p177 Ns552p439 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 622848775) qz372 0 3 Ns552p440 Ns552p180 Ns552p439 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p442 := nat_lit 731670637943091634266745255761551883313705712272576003654798190706690625 

noncomputable def Ns552p443 := nat_lit 27480274929591670703688826953036349626457369137659994102422437890625 

noncomputable def Ns552p444 := nat_lit 2194956953279415719458828389630749577241864222079452690976189727244290625 

noncomputable def Ns552p445 := BSN.cos_dyadic_bound_f 269077655 536870912 3 2 536870912 268435456 Ns552p442 Ns552p140 Ns552p443 Ns552p444 Ns552p143 Ns552p443 470840326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 269077655) qz373 0 2 Ns552p442 Ns552p140 Ns552p443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 269077655) qz374 0 2 Ns552p444 Ns552p143 Ns552p443 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p446 := nat_lit 75924416531869812099354049723466600731787514115288550167944563556435098669298216863321874010542700545385085284801 

noncomputable def Ns552p447 := nat_lit 9503246448619383961363848838488609524766647806713366288755958175203007722486660222563035364409638146814401 

noncomputable def Ns552p448 := nat_lit 379424348741286509945634613842722692587566648086093446390630047950546208076450142126361044424302140824288839872961 

noncomputable def Ns552p449 := BSN.sin_dyadic_bound_f 678405457 536870912 4 3 536870912 268435456 Ns552p446 Ns552p177 Ns552p447 Ns552p448 Ns552p180 Ns552p447 511742007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 678405457) qz371 0 3 Ns552p446 Ns552p177 Ns552p447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 678405457) qz372 0 3 Ns552p448 Ns552p180 Ns552p447 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p450 := Ns552p405 133008 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 374 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 470840326 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 511742007 536870912) qz65 rfl rfl (Ns552p435 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p437 rfl rfl) (Ns552p441 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p434 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p445 rfl rfl) (Ns552p449 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p451 := nat_lit 117943916151521311422573617412723946436611182070213987686739345692453636087506039701300030199302950620029439459041 

noncomputable def Ns552p452 := nat_lit 35575212002592969089007024310394127599039114198979527396654339879678661140965168191930665831424724015791841 

noncomputable def Ns552p453 := nat_lit 589242808490279520372856481303705887200741497383617591370634316149382231006816664604552457893680570856932256268001 

noncomputable def Ns552p454 := BSN.sin_dyadic_bound_f 757290121 536870912 4 3 536870912 268435456 Ns552p451 Ns552p177 Ns552p452 Ns552p453 Ns552p180 Ns552p452 529993620 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 757290121) qz371 0 3 Ns552p451 Ns552p177 Ns552p452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 757290121) qz372 0 3 Ns552p453 Ns552p180 Ns552p452 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p455 := nat_lit 62756758758733231994695364403459517479653658775886705991909551458524954247223372718745085648633577823361371890625 

noncomputable def Ns552p456 := nat_lit 93646840698100358780597320701156389366043977831235741285271311723721919282374294708266073533947402587890625 

noncomputable def Ns552p457 := nat_lit 379900703305804729389279849242838434230909012178184950925202843717359095565004350108528416773537721636025077490625 

noncomputable def Ns552p458 := BSN.cos_dyadic_bound_f 820901585 536870912 4 3 536870912 268435456 Ns552p455 Ns552p151 Ns552p456 Ns552p457 Ns552p154 Ns552p456 22406761 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 820901585) qz373 0 3 Ns552p455 Ns552p151 Ns552p456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 820901585) qz374 0 3 Ns552p457 Ns552p154 Ns552p456 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p459 := Ns552p403 179007 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 529993620 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 36 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 22406761 536870912) qz65 rfl rfl (Ns552p450 rfl rfl) (Ns552p434 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p454 rfl rfl) (Ns552p458 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p460 := nat_lit 9401271288763498917281097862292628947444548677635029507253683806781740865 

noncomputable def Ns552p461 := nat_lit 1399978119678030923482706681272064445655931364999469077076168063752001 

noncomputable def Ns552p462 := nat_lit 24620110553615399399955331923758635329442755981119840045253905698039437121 

noncomputable def Ns552p463 := BSN.sin_dyadic_bound_f 439810057 536870912 3 2 536870912 268435456 Ns552p460 Ns552p130 Ns552p461 Ns552p462 Ns552p133 Ns552p461 392241482 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 439810057) qz371 0 2 Ns552p460 Ns552p130 Ns552p461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 439810057) qz372 0 2 Ns552p462 Ns552p133 Ns552p461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p464 := nat_lit 5285784188745919880142804494823972411818384689572845442135371645473036321 

noncomputable def Ns552p465 := nat_lit 1433526417521094409681638841895137465277047604224390119562693249374241 

noncomputable def Ns552p466 := nat_lit 15854485513402717451609050206788126960524599973510087546166989549920360481 

noncomputable def Ns552p467 := BSN.cos_dyadic_bound_f 441113869 536870912 3 2 536870912 268435456 Ns552p464 Ns552p140 Ns552p465 Ns552p466 Ns552p143 Ns552p465 365621025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 441113869) qz373 0 2 Ns552p464 Ns552p140 Ns552p465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 441113869) qz374 0 2 Ns552p466 Ns552p143 Ns552p465 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p468 := Ns552p401 219197 BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 392241482 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 365621025 536870912) qz65 rfl rfl (Ns552p459 rfl) (Ns552p434 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p463 rfl rfl) (Ns552p467 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p469 := nat_lit 863353043719208113882671415296 

noncomputable def Ns552p470 := BSN.cos_dyadic_bound_f 30482256 536870912 2 1 536870912 268435456 Ns552p469 Ns552p157 Ns552p469 Ns552p469 Ns552p158 Ns552p469 536005789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 30482256) qz373 0 1 Ns552p469 Ns552p157 Ns552p469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 30482256) qz374 0 1 Ns552p469 Ns552p158 Ns552p469 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p471 := nat_lit 7367702450697641544395385435867342300053839452673675647885261373950296320 

noncomputable def Ns552p472 := nat_lit 859884676920044681749193716620750269846295256815101599555936271892736 

noncomputable def Ns552p473 := nat_lit 19294971367112143020122225066016129571132685517062878437109736844477235456 

noncomputable def Ns552p474 := BSN.sin_dyadic_bound_f 413813854 536870912 3 2 536870912 268435456 Ns552p471 Ns552p130 Ns552p472 Ns552p473 Ns552p133 Ns552p472 374038501 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 413813854) qz371 0 2 Ns552p471 Ns552p130 Ns552p472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 413813854) qz372 0 2 Ns552p473 Ns552p133 Ns552p472 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p475 := Ns552p399 255343 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 178 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536005789 536870912) BSN.abs_quadSignPos qz598 (BSN.sfrac_eq_quadSignPos_mul Bool.false 374038501 536870912) qz65 rfl rfl (Ns552p468 rfl) (Ns552p434 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p470 rfl rfl) (Ns552p474 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p476 := nat_lit 143218195881036616385813123314128738582828953281030675991994532486376847028680390846728514171147523776435998696721 

noncomputable def Ns552p477 := nat_lit 63643033985391695619362499266596800243461698754670750256493044822983123603565205832079008456403887293211921 

noncomputable def Ns552p478 := nat_lit 715388326300078059883958945476422192319295571615471491367118872422385426472346205171979660679711706167895475627281 

noncomputable def Ns552p479 := BSN.sin_dyadic_bound_f 794900139 536870912 4 3 536870912 268435456 Ns552p476 Ns552p177 Ns552p477 Ns552p478 Ns552p180 Ns552p477 534689384 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 794900139) qz371 0 3 Ns552p476 Ns552p177 Ns552p477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 794900139) qz372 0 3 Ns552p478 Ns552p180 Ns552p477 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p480 := Ns552p397 Bool.true 139309162 255343 Bool.true 794900139 28296951008113761 1 Bool.false 534689384 Bool.false Bool.false 15042373 272235 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 534689384 536870912) qz65 rfl (Ns552p475 rfl) (Ns552p434 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p479 rfl rfl) rfl 

noncomputable def Ns552p481 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) 15042373 536870912 272235 536870912 15042373 536870912 272235 536870912 16151625022308352 15042373 268435456 272235 268435456 (Ns552p480 rfl rfl rfl rfl) 

noncomputable def Ns552p482 := @Enclosure.Real.IsNear.mulLit_ff qz620 (Zeta.RiemannSiegel.correction qz64) 1197095 4194304 1 33554432 1070727371951677 2251799813685248 32093009237844001 676243631547351040000 1281762383326492778315 9444732965739290427392 

noncomputable abbrev qz624 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns552p483 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz624 1 1 0 1 1197095 4194304 1 33554432 1197095 4194304 1 33554432 

noncomputable def Ns552p484 := @Enclosure.Real.IsNear.sqrt_image qz63 5056791409857 33554432000 473451 33554432000 411919588 411919628 33554432 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 5056791409857 33554432000 473451 33554432000 (BSN.t_div_two_pi_mk qz62 946902 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 946902 1000 0 1 10680707 67108864 1 67108864 5056791409857 33554432000 473451 33554432000 (Enclosure.Real.IsNear.const Bool.false 946902 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz758 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 946902 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz625 := qz758

noncomputable abbrev qz413 := qz625

noncomputable abbrev qz71 := qz413

noncomputable def Ns552p485 := @Enclosure.Real.IsNear.sqrt_image qz71 51489951 4194304 5 8388608 117565844 117565851 33554432 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 823839216 67108864 40 67108864 51489951 4194304 5 8388608 (Ns552p484 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p486 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 235131695 67108864 7 67108864 9576759 9576761 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 235131695 67108864 7 67108864 235131695 67108864 7 67108864 (Ns552p485 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p487 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 19153520 67108864 2 67108864 1197095 4194304 1 33554432 (Ns552p486 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real qz584 qz582 qz619)

noncomputable abbrev qz72 := (Real.cos qz414)

noncomputable abbrev qz626 := (@HMul.hMul Real Real Real qz742 qz757 qz757)

noncomputable abbrev qz415 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz626 qz619) qz603)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz415))

noncomputable def Ns552p488 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 1070727371951677 

noncomputable def Ns552p489 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz72) qz73 410113253 67108864 9673 

noncomputable abbrev qz74 := (@Neg.neg Real Real.instNeg (Real.cos qz414))

noncomputable def Ns552p490 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz72) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz74)) Bool.true 410113253 67108864 9673 67108864 (BSN.inv_eq_neg_inv_neg qz72) 

noncomputable def Ns552p491 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz74) Bool.false 410113253 67108864 9673 67108864 410113253 67108864 

noncomputable def Ns552p492 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true 5490678 33554432 622207216 161229045760000 2745339 16777216 38887951 10076815360000 

noncomputable abbrev qz75 := qz414

noncomputable abbrev qz627 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable def Ns552p493 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 58222659) qz627) Bool.false 58222659 33554432 63 16777216 Bool.true 5490678 33554432 1 

noncomputable def Ns552p494 := nat_lit 134930377065119721291279587 

noncomputable def Ns552p495 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns552p496 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 1158303 4194304 5 8388608 1024263851360974767165 590295810358705651712 Ns552p494 

noncomputable def Ns552p497 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 51489951 4194304 5 8388608 12 1 0 1 1158303 1158303 4194304 5 

noncomputable def Ns552p498 := @Ns552p497 8388608 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 823839216 67108864 40 67108864 51489951 4194304 5 8388608 (Ns552p484 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p499 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 1024263851360974767165 590295810358705651712 Ns552p494 Ns552p495 58222659 33554432 63 16777216 (@Ns552p496 Ns552p495 RS553to564.d55 (Ns552p498 rfl rfl) rfl) 

noncomputable def Ns552p500 := nat_lit 370537239012489713997969234141365337538918288930378105935747467683292944141474710118103913584184561 

noncomputable def Ns552p501 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns552p502 := nat_lit 1517415188619035091924026928282199968890701741438997842745112947922939931867901200474161597681 

noncomputable def Ns552p503 := nat_lit 2239875356277245405440096640845164491177253241186483126542676418675626628119900498239645427301141745 

noncomputable def Ns552p504 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns552p505 := BSN.cos_dyadic_bound_t 58222659 33554432 4 3 33554432 9610000 Ns552p500 Ns552p501 Ns552p502 Ns552p503 Ns552p504 Ns552p502 5490678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 58222659) (BSN.cosEvenQ 33554432) 0 3 Ns552p500 Ns552p501 Ns552p502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 58222659) (BSN.cosOddQ 33554432) 0 3 Ns552p503 Ns552p504 Ns552p502 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p506 := @Enclosure.Real.IsNear.inv_image qz74 2745339 16777216 38887951 10076815360000 205051790 205061463 33554432 (@Enclosure.Real.IsNear.neg qz72 Bool.true 2745339 16777216 38887951 10076815360000 (Ns552p492 (@Ns552p493 9610000 (Ns552p499 rfl) (Enclosure.sfrac_false_div 58222659 33554432) (Ns552p505 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns552p507 := Ns552p490 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz74) Bool.false 410113253 67108864 9673 67108864 (@Ns552p491 9673 67108864 (Ns552p506 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p508 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true 2610809 33554432 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz355 qz352 qz415)

noncomputable def Ns552p509 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 110641257)) qz380) Bool.true 110641257 67108864 

noncomputable def Ns552p510 := nat_lit 4081941910246673392868450845 

noncomputable def Ns552p511 := nat_lit 2475880078570760549798248448 

noncomputable def Ns552p512 := nat_lit 1757039757225483585369943175246947 

noncomputable def Ns552p513 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns552p510 Ns552p511 Ns552p512 

noncomputable def Ns552p514 := nat_lit 302231454903657293676544000000000000000 

noncomputable abbrev qz77 := qz415

noncomputable def Ns552p515 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 4616120694079 

noncomputable abbrev qz416 := (@HSub.hSub Real Real Real qz588 qz626 qz619)

noncomputable abbrev qz78 := qz416

noncomputable def Ns552p516 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 3516609066303 17592186044416 65109125 70368744177664 1 16 

noncomputable abbrev qz417 := qz626

noncomputable abbrev qz79 := qz417

noncomputable def Ns552p517 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 1341665839809 17592186044416 23166085 70368744177664 1158303 4194304 5 8388608 

noncomputable def Ns552p518 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 1158303 4194304 5 8388608 1158303 4194304 5 8388608 1341665839809 17592186044416 

noncomputable def Ns552p519 := nat_lit 1235777200726670093919152544081689982113977741759208911219327840736236019265474028012921295060925411681 

noncomputable def Ns552p520 := nat_lit 3365156094550161033585500537568249061201853381222689221784387473970280180967511539795006148047201 

noncomputable def Ns552p521 := nat_lit 7475147050656355348832623456721066388109590807443751181311269435859475306863244170525643172843225608545 

noncomputable def Ns552p522 := BSN.cos_dyadic_bound_t 110641257 67108864 4 3 33554432 9610000 Ns552p519 Ns552p203 Ns552p520 Ns552p521 Ns552p206 Ns552p520 2610809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 110641257) qz604 0 3 Ns552p519 Ns552p203 Ns552p520 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 110641257) (BSN.cosOddQ 67108864) 0 3 Ns552p521 Ns552p206 Ns552p520 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p523 := @Ns552p508 3824618864 644916183040000 2610809 33554432 239038679 40307261440000 (@Ns552p509 391 67108864 Bool.true 2610809 33554432 1 9610000 (@Ns552p513 Ns552p514 110641257 67108864 391 67108864 (@Ns552p515 17592186044416 65109125 70368744177664 Ns552p510 Ns552p511 Ns552p512 Ns552p514 RS553to564.d55 (@Ns552p516 0 1 73857931105264 4616120694079 17592186044416 65109125 70368744177664 (@Ns552p517 14749727473230938112 3516609066303 17592186044416 65109125 70368744177664 (@Ns552p518 23166085 70368744177664 (Ns552p498 rfl rfl) (Ns552p498 rfl rfl) rfl) (Ns552p498 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 110641257 67108864) (BSN.cos_neg_of_bound 110641257 67108864 Bool.true 2610809 33554432 1 9610000 (Ns552p522 rfl rfl)) rfl rfl) 

noncomputable def Ns552p524 := @Ns552p482 615337264111026781719647 Ns552p394 (Ns552p483 qz33 (@Enclosure.Real.IsNear.of_eq qz624 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 1197095 4194304 1 33554432 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 946902 1000 qz65)) Ns552p487) rfl) (@Ns552p488 2251799813685248 32093009237844001 676243631547351040000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 946902 1000 12 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 946902 1000 12 qz65 rfl rfl rfl))) (@Ns552p489 67108864 2610809 33554432 239038679 40307261440000 1070727371951677 2251799813685248 32093009237844001 676243631547351040000 Ns552p507 (Ns552p523 rfl) rfl)) 

noncomputable def Ns552p525 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 752505934595492699979 9444732965739290427392 Ns552p393 Ns552p394 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HMul.hMul Real Real Real qz5 qz620 (Zeta.RiemannSiegel.correction qz64))) Bool.true 752505934595492699979 9444732965739290427392 Ns552p393 Ns552p394 (BSN.hardyZApproximantRS₀_eq qz62 12 (@BSN.floor_sqrt_eq_dec qz62 946902 1000 12 qz65 rfl rfl rfl)) (@Ns552p396 752505934595492699979 9444732965739290427392 Ns552p393 Ns552p394 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12)) Bool.false 15042373 268435456 272235 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (Ns552p481 (Ns552p480 rfl rfl rfl rfl) rfl rfl)) (Ns552p524 rfl) rfl rfl)) 

theorem RS553to564.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 752505934595492699979 9444732965739290427392 Ns552p393 Ns552p394 := Ns552p525 

noncomputable def Ns552p526 := nat_lit 9309421314539439481640411 

noncomputable def Ns552p527 := nat_lit 9076388380075458100723712000 

noncomputable def Ns552p528 := nat_lit 3729133498090027957358170210304 

noncomputable abbrev qz759 := (Enclosure.sfrac Bool.false 948154 1000)

noncomputable abbrev qz628 := qz759

noncomputable abbrev qz418 := qz628

noncomputable abbrev qz80 := qz418

noncomputable abbrev qz760 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 948154 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz629 := qz760

noncomputable abbrev qz419 := qz629

noncomputable abbrev qz81 := qz419

noncomputable abbrev qz761 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 948154 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz630 := qz761

noncomputable abbrev qz420 := qz630

noncomputable abbrev qz82 := qz420

noncomputable abbrev qz631 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz81 qz9))

noncomputable def Ns552p529 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HMul.hMul Real Real Real qz5 qz631 (Zeta.RiemannSiegel.correction qz82)) 58326257 67108864 272597 268435456 10101107954362458443157 75557863725914323419136 92322053093776909096411 Ns552p527 Ns552p528 

noncomputable def Ns552p530 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin BSN.quadSignPos 11 12 948154 1000 287 536870912 268435456 9007199254740992 Bool.false 1022096938124 4514 1334074092 57 154981288 8 

noncomputable def Ns552p531 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 948154 1000 177 235 536870912 268435456 9007199254740992 Bool.false 1022096938124 4514 

noncomputable def Ns552p532 := Ns552p531 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.false 150045543 219489 Bool.true 735731964 Bool.true 339812624 28296951008113761 1 Bool.false 526127733 Bool.true Bool.false 317573179 Bool.false Bool.false 79421250 

noncomputable def Ns552p533 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 948154 1000 43 114 536870912 268435456 9007199254740992 Bool.false 1022096938124 4514 

noncomputable def Ns552p534 := Ns552p533 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.false 259577450 179246 Bool.true 151756211 Bool.true 232229331 28296951008113761 1 Bool.false 149743352 Bool.false Bool.false 487422541 Bool.true Bool.false 150045543 

noncomputable def Ns552p535 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 948154 1000 130 37 536870912 268435456 9007199254740992 Bool.false 1022096938124 4514 

noncomputable def Ns552p536 := Ns552p535 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.false 546679713 133186 Bool.false 395398186 Bool.false 355395372 28296951008113761 1 Bool.false 397731740 Bool.true Bool.false 330001802 Bool.true Bool.false 259577450 

noncomputable def Ns552p537 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 948154 1000 375 240 536870912 268435456 9007199254740992 Bool.false 1022096938124 4514 

noncomputable def Ns552p538 := Ns552p537 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 294305643 78596 Bool.false 179724122 Bool.false 439063225 28296951008113761 1 Bool.false 176386060 Bool.false Bool.false 367119965 Bool.false Bool.false 546679713 

noncomputable def Ns552p539 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 948154 1000 793 548 536870912 268435456 9007199254740992 Bool.false 1022096938124 4514 

noncomputable def Ns552p540 := Ns552p539 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 536870496 4576 Bool.false 511193077 Bool.false 726864297 28296951008113761 1 Bool.false 437376168 Bool.true Bool.false 115539572 Bool.false Bool.false 294305643 

noncomputable def Ns552p541 := nat_lit 1752056755032643443182376072458512119726045702155595868031 

noncomputable def Ns552p542 := nat_lit 920292658029593376279650737876957396040807551598592000 

noncomputable def Ns552p543 := nat_lit 367820517525351796641171391851520000 

noncomputable def Ns552p544 := nat_lit 2092503241396101148620006683533932564480 

noncomputable abbrev qz632 := (@Eq.refl Real qz759)

noncomputable abbrev qz421 := qz632

noncomputable abbrev qz83 := qz421

noncomputable def Ns552p545 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 948154 1000 3595985030864 16000000 1896308 4000 2000 Ns552p543 Ns552p544 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p546 := nat_lit 35882122343068537716375061963950328211989415980146603377274880 

noncomputable abbrev qz633 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1896308))))

noncomputable abbrev qz422 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 948154 4000) (Real.log (Enclosure.sfrac Bool.false 3595985030864 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz633))

noncomputable abbrev qz634 := (Enclosure.sfrac Bool.false 948154 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz422 qz634) (@HMul.hMul Real Real Real qz355 qz634 (Real.log Real.pi)))

noncomputable def Ns552p547 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns552p543 Ns552p544) 17147942687133409918731 9007199254740992000 66187900998266767979 Ns552p410 Ns552p543 Ns552p544 0 1 Ns552p546 

noncomputable def Ns552p548 := nat_lit 575389476835315278046184865792000 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz359 qz422 qz634)

noncomputable def Ns552p549 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz634 (Real.log Real.pi)) 22036060627932639837963 9007199254740992000 5975970245236199 1922000000000000000000 18209658342597 33554432000 1422231 268435456000 Ns552p548 17147942687133409918731 9007199254740992000 

noncomputable def Ns552p550 := nat_lit 44072121255865279675926000 

noncomputable abbrev qz86 := qz422

noncomputable def Ns552p551 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz634 26306166629022485102347 9007199254740992000 5975970245236199 1922000000000000000000 948154 2000 0 1 Ns552p550 22036060627932639837963 9007199254740992000 5975970245236199 1922000000000000000000 

noncomputable def Ns552p552 := nat_lit 59236221114005920396464660332524077056 

noncomputable def Ns552p553 := nat_lit 119178226390148022039216128 

noncomputable def Ns552p554 := nat_lit 76169661496758200892506884116485498260705058897606790266506188779859331649698721762749331235532683432337710499543836232018602880322499382559872768846446970118890481548550174243448422400 

noncomputable def Ns552p555 := nat_lit 1836817507286088976737346197166539738970993266782017897386809758528864137867840977406959980867776404761768539980983144145385864724905583257623126199656174502106016241327952872540733440 

noncomputable def Ns552p556 := nat_lit 39022350136509641531773155360001943479787514261373526699992658069702975778731172026618210927836823560739382974512264176284906843709015566369517322271352430586461691844923228160 

noncomputable def Ns552p557 := BSN.log_dyadic_bound 1498833030864 5693137030864 8 7 Ns552p554 268435456 76880000 Ns552p555 Ns552p556 144750523 7191970061728 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1498833030864) (BSN.artanhQ 5693137030864) 0 7 Ns552p555 Ns552p554 Ns552p556 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz423 := (Real.log (Enclosure.sfrac Bool.false 3595985030864 16000000))

noncomputable def Ns552p558 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 948154 4000) qz423 948154 4000 0 1 55496686319889511 4503599627370496 12500016337 961000000000000000 26309702560474259706347 9007199254740992000 5925970244995949 1922000000000000000000 (Enclosure.Real.IsNear.const Bool.false 948154 4000) (BSN.isNear_log_sfrac 3595985030864 16000000 55496686319889511 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3595985030864) qz362)) Bool.false Ns552p553 Ns552p114 1000001306960000 76880000000000000000000 55496686319889511 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3595985030864 16000000 17 7191970061728 4194304000000 144750523 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p557 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p559 := BSN.arctan_dyadic_bound_f 1000 1896308 1 0 33554432 9610000 0 1 1 0 1 1 17694 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1896308) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1896308) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p560 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1896308))) 884279719003555 562949953421312 1 2000000000000000 17694 33554432 1 9610000 29661542863808057311232 883982862943651 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p559 rfl) rfl rfl 

noncomputable abbrev qz424 := (@HMul.hMul Real Real Real qz584 qz589 qz633)

noncomputable abbrev qz87 := qz424

noncomputable abbrev qz425 := qz633

noncomputable abbrev qz88 := qz425

noncomputable def Ns552p561 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 948154 4000) qz423) qz87 26309702560474259706347 9007199254740992000 5925970244995949 1922000000000000000000 883982862943651 2251799813685248 200000000961 7688000000000000000 Ns552p552 26306166629022485102347 9007199254740992000 5975970245236199 1922000000000000000000 (Ns552p558 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz88 1 4 0 1 883982862943651 562949953421312 200000000961 1922000000000000000 883982862943651 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p560 rfl) 

noncomputable def Ns552p562 := @Ns552p547 Ns552p541 Ns552p542 66187900998266767979 Ns552p410 (@Ns552p549 66187900998266767979 Ns552p410 (Ns552p551 (Ns552p561 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 948154 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz634 (Real.log Real.pi) 948154 2000 0 1 38410761 33554432 3 268435456 18209658342597 33554432000 1422231 268435456000 (Enclosure.Real.IsNear.const Bool.false 948154 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p543 Ns552p544) 

noncomputable def Ns552p563 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns552p541 Ns552p542 66187900998266767979 Ns552p410 127762117265 67108864 565 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz370 qz84 (Enclosure.sfrac Bool.true Ns552p543 Ns552p544)) Bool.false Ns552p541 Ns552p542 66187900998266767979 Ns552p410 Ns552p545 (Ns552p562 rfl rfl)) 

noncomputable def Ns552p564 := nat_lit 15179776320604265523445760 

noncomputable def Ns552p565 := nat_lit 14334781706638207150424751439520220546246006605293350461832480984543358565540546559817757923323209327963228492076734517061671113318244269142001 

noncomputable def Ns552p566 := nat_lit 282877490902138091004622673603363019119652456796264491099280832830873987773707601701812303598028785564314492868916806270538811366318583631052800 

noncomputable def Ns552p567 := nat_lit 10153759181490585918879292830078027292808042092505003869067891349277568613236246002860312526283140673083058793091868520368689431480610801 

noncomputable def Ns552p568 := nat_lit 71585126279009087865578300936055470110361581430574552106950496595906315332110805772608120121143141159694494210581766420866228341326059450904561 

noncomputable def Ns552p569 := nat_lit 9900712181574833185161793576117705669187835987869257188474829149080589572079766059563430625931007494751007250412088219468858397821150427086848000 

noncomputable abbrev qz635 := (BSN.sinEvenQ 137438953472)

noncomputable abbrev qz636 := (BSN.sinOddQ 137438953472)

noncomputable def Ns552p570 := BSN.sin_dyadic_bound_f 215717595901 137438953472 4 3 67108864 19238770 Ns552p565 Ns552p566 Ns552p567 Ns552p568 Ns552p569 Ns552p567 67108812 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215717595901) qz635 0 3 Ns552p565 Ns552p566 Ns552p567 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215717595901) qz636 0 3 Ns552p568 Ns552p569 Ns552p567 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p571 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 127762117265) qz380) Bool.false 127762117265 67108864 565 67108864 Bool.false 67108812 67108864 1 9610000 (Ns552p563 rfl) (Enclosure.sfrac_false_div 127762117265 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 127762117265) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns552p564) qz394) 226375608064910080 72057594037927936 Bool.false 67108812 67108864 302 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q3 127762117265 67108864 226375608064910080 72057594037927936 302 Ns552p564 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108812 67108864 Ns552p564 Ns552p114 215717595901 137438953472 19238770 19220000 (Ns552p570 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p572 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns552p541 Ns552p542 66187900998266767979 Ns552p410 1022096938124 536870912 4514 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz370 qz84 (Enclosure.sfrac Bool.true Ns552p543 Ns552p544)) Bool.false Ns552p541 Ns552p542 66187900998266767979 Ns552p410 Ns552p545 (Ns552p562 rfl rfl)) 

noncomputable def Ns552p573 := Ns552p540 78596 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 793 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 437376168 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 548 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 115539572 536870912) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 16777203 16777216 343547429 40307261440000 536870496 536870912 4576 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 16777203 16777216 343547429 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 67108812 67108864 5496758864 644916183040000 16777203 16777216 343547429 40307261440000 (Ns552p571 rfl rfl) rfl)) rfl) (Ns552p572 rfl) RS553to564.d7 

noncomputable def Ns552p574 := nat_lit 17160074595963636087147627899100419476823351561002337691386589459398155105 

noncomputable def Ns552p575 := nat_lit 4663153470779442496287780176319431390191036386172817925836915884579681 

noncomputable def Ns552p576 := nat_lit 44935502645713975416583130948787057645619897172285652248418284053658229601 

noncomputable def Ns552p577 := BSN.sin_dyadic_bound_f 511193077 536870912 3 2 536870912 268435456 Ns552p574 Ns552p130 Ns552p575 Ns552p576 Ns552p133 Ns552p575 437376168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 511193077) qz371 0 2 Ns552p574 Ns552p130 Ns552p575 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 511193077) qz372 0 2 Ns552p576 Ns552p133 Ns552p575 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p578 := nat_lit 38527073460534417203801488655172080058673106156055417780473415233084194624021768334406485399479262880912473729121 

noncomputable def Ns552p579 := nat_lit 21749037703529457315773127294928139228595753013410380268289389863100838499285687387307153779659385039366241 

noncomputable def Ns552p580 := nat_lit 233419787007431102154572520635633622533239232066235674107526716981718002143921703030390817857472073747874318788705 

noncomputable def Ns552p581 := BSN.cos_dyadic_bound_f 726864297 536870912 4 3 536870912 268435456 Ns552p578 Ns552p151 Ns552p579 Ns552p580 Ns552p154 Ns552p579 115539572 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 726864297) qz373 0 3 Ns552p578 Ns552p151 Ns552p579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 726864297) qz374 0 3 Ns552p580 Ns552p154 Ns552p579 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p582 := nat_lit 1043339098429782686965699589341456 

noncomputable def Ns552p583 := BSN.sin_dyadic_bound_f 179724122 536870912 2 1 536870912 268435456 Ns552p582 Ns552p283 Ns552p582 Ns552p582 Ns552p284 Ns552p582 176386060 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 179724122) qz371 0 1 Ns552p582 Ns552p283 Ns552p582 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 179724122) qz372 0 1 Ns552p582 Ns552p284 Ns552p582 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p584 := nat_lit 5188151558581866309719545123605640952143348832798436326672557213087890625 

noncomputable def Ns552p585 := nat_lit 1381072584987031073622491212012935637840973394600835558007965087890625 

noncomputable def Ns552p586 := nat_lit 15561692530575624867011390388392896985154364551606107308901655709087890625 

noncomputable def Ns552p587 := BSN.cos_dyadic_bound_f 439063225 536870912 3 2 536870912 268435456 Ns552p584 Ns552p140 Ns552p585 Ns552p586 Ns552p143 Ns552p585 367119965 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 439063225) qz373 0 2 Ns552p584 Ns552p140 Ns552p585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 439063225) qz374 0 2 Ns552p586 Ns552p143 Ns552p585 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p588 := Ns552p538 133186 BSN.abs_quadSignPos (BSN.cos_quad_nat3 375 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 176386060 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 367119965 536870912) qz83 rfl rfl (Ns552p573 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p577 rfl rfl) (Ns552p581 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p572 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p583 rfl rfl) (Ns552p587 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p589 := nat_lit 3411956757447952395695578646196795167111041325378966096206472946271150336 

noncomputable def Ns552p590 := nat_lit 597416729859253346850499565199430591941022876814308948186791371366656 

noncomputable def Ns552p591 := nat_lit 10234675438884138680393034939459986640149241930383269670723045256070717696 

noncomputable def Ns552p592 := BSN.cos_dyadic_bound_f 395398186 536870912 3 2 536870912 268435456 Ns552p589 Ns552p140 Ns552p590 Ns552p591 Ns552p143 Ns552p590 397731740 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 395398186) qz373 0 2 Ns552p589 Ns552p140 Ns552p590 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 395398186) qz374 0 2 Ns552p591 Ns552p143 Ns552p590 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p593 := nat_lit 4008075869186740815311381032974202102817605733493970424118310419650641920 

noncomputable def Ns552p594 := nat_lit 254503725812064431409048073103363013675348384544149304968539694759936 

noncomputable def Ns552p595 := nat_lit 10496929508504434983402764246623600062500159690337803440482768701483974656 

noncomputable def Ns552p596 := BSN.sin_dyadic_bound_f 355395372 536870912 3 2 536870912 268435456 Ns552p593 Ns552p130 Ns552p594 Ns552p595 Ns552p133 Ns552p594 330001802 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 355395372) qz371 0 2 Ns552p593 Ns552p130 Ns552p594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 355395372) qz372 0 2 Ns552p595 Ns552p133 Ns552p594 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p597 := Ns552p536 179246 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 397731740 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 330001802 536870912) qz83 rfl rfl (Ns552p588 rfl rfl) (Ns552p572 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p592 rfl rfl) (Ns552p596 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p598 := nat_lit 530378485402892720166085089463441 

noncomputable def Ns552p599 := BSN.sin_dyadic_bound_f 151756211 536870912 2 1 536870912 268435456 Ns552p598 Ns552p283 Ns552p598 Ns552p598 Ns552p284 Ns552p598 149743352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 151756211) qz371 0 1 Ns552p598 Ns552p283 Ns552p598 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 151756211) qz372 0 1 Ns552p598 Ns552p284 Ns552p598 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p600 := nat_lit 405943987390330608736096881302417207317811934629177124819126612550341921 

noncomputable def Ns552p601 := nat_lit 8459341714228694176252377152782706546511960414316325579283831575841 

noncomputable def Ns552p602 := nat_lit 1217815043487563368819938139152946056540342779966702741806221269987874081 

noncomputable def Ns552p603 := BSN.cos_dyadic_bound_f 232229331 536870912 3 2 536870912 268435456 Ns552p600 Ns552p140 Ns552p601 Ns552p602 Ns552p143 Ns552p601 487422541 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 232229331) qz373 0 2 Ns552p600 Ns552p140 Ns552p601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 232229331) qz374 0 2 Ns552p602 Ns552p143 Ns552p601 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p604 := Ns552p534 219489 BSN.abs_quadSignPos (BSN.cos_quad_nat3 43 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 149743352 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 487422541 536870912) qz83 rfl rfl (Ns552p597 rfl) (Ns552p572 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p599 rfl rfl) (Ns552p603 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p605 := nat_lit 105061330582516011519188567717485436827019660309323238149262180923306231439483846495157545723655201437763760029696 

noncomputable def Ns552p606 := nat_lit 25155647092347531740035666161580371045882329075158417500933857929871446549540787144094226901279451062992896 

noncomputable def Ns552p607 := nat_lit 524928249096012167324441263473134175431232988886559228211376181621299634947024962546605745116628075937715512672256 

noncomputable def Ns552p608 := BSN.sin_dyadic_bound_f 735731964 536870912 4 3 536870912 268435456 Ns552p605 Ns552p177 Ns552p606 Ns552p607 Ns552p180 Ns552p606 526127733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 735731964) qz371 0 3 Ns552p605 Ns552p177 Ns552p606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 735731964) qz372 0 3 Ns552p607 Ns552p180 Ns552p606 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p609 := nat_lit 3349981194395479681237238634692609479925627528060770681268343320860426240 

noncomputable def Ns552p610 := nat_lit 177793578252522054497592826362844410714631960842809243460052373733376 

noncomputable def Ns552p611 := nat_lit 8773472414766228415152152702476056413616438883651130093118154326981738496 

noncomputable def Ns552p612 := BSN.sin_dyadic_bound_f 339812624 536870912 3 2 536870912 268435456 Ns552p609 Ns552p130 Ns552p610 Ns552p611 Ns552p133 Ns552p610 317573179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 339812624) qz371 0 2 Ns552p609 Ns552p130 Ns552p610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 339812624) qz372 0 2 Ns552p611 Ns552p133 Ns552p610 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p613 := Ns552p532 255682 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 526127733 536870912) BSN.abs_quadSignPos qz598 (BSN.sfrac_eq_quadSignPos_mul Bool.false 317573179 536870912) qz83 rfl rfl (Ns552p604 rfl) (Ns552p572 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p608 rfl rfl) (Ns552p612 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p614 := nat_lit 132343641822837726993272716643634176561059128819401020918544643796579203274578085478472696037219266599302799194321 

noncomputable def Ns552p615 := nat_lit 50236845109170192252926961656463047758249005688739234408273188211408635061069494931741254648618628174477521 

noncomputable def Ns552p616 := nat_lit 661118081844272372037917284713421755837451156120096178673437124555216165653816106658576888113699432410647237916881 

noncomputable def Ns552p617 := BSN.sin_dyadic_bound_f 779384677 536870912 4 3 536870912 268435456 Ns552p614 Ns552p177 Ns552p615 Ns552p616 Ns552p180 Ns552p615 533069029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 779384677) qz371 0 3 Ns552p614 Ns552p177 Ns552p615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 779384677) qz372 0 3 Ns552p616 Ns552p180 Ns552p615 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p618 := Ns552p530 Bool.false 79421250 255682 Bool.true 779384677 28296951008113761 1 Bool.false 533069029 Bool.false Bool.false 233305028 272597 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 533069029 536870912) qz83 rfl (Ns552p613 rfl) (Ns552p572 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p617 rfl rfl) rfl 

noncomputable def Ns552p619 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) 233305028 536870912 272597 536870912 233305028 536870912 272597 536870912 250509366313091072 58326257 67108864 272597 268435456 (Ns552p618 rfl rfl rfl rfl) 

noncomputable def Ns552p620 := @Enclosure.Real.IsNear.mulLit_ff qz631 (Zeta.RiemannSiegel.correction qz82) 9573597 33554432 1 33554432 1055100601619481 2251799813685248 9630162989296957 270497452618940416000 10101107954362458443157 75557863725914323419136 

noncomputable abbrev qz637 := (@HPow.hPow Real Real Real qz7 qz81 qz9)

noncomputable def Ns552p621 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz637 1 1 0 1 9573597 33554432 1 33554432 9573597 33554432 1 33554432 

noncomputable def Ns552p622 := @Enclosure.Real.IsNear.sqrt_image qz81 5063477532439 33554432000 474077 33554432000 412191820 412191859 33554432 (@Enclosure.Real.IsNear.of_eq qz81 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 5063477532439 33554432000 474077 33554432000 (BSN.t_div_two_pi_mk qz80 948154 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 948154 1000 0 1 10680707 67108864 1 67108864 5063477532439 33554432000 474077 33554432000 (Enclosure.Real.IsNear.const Bool.false 948154 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz762 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 948154 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz638 := qz762

noncomputable abbrev qz426 := qz638

noncomputable abbrev qz89 := qz426

noncomputable def Ns552p623 := @Enclosure.Real.IsNear.sqrt_image qz89 824383679 67108864 39 67108864 117604686 117604693 33554432 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 824383679 67108864 39 67108864 824383679 67108864 39 67108864 (Ns552p622 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p624 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 235209379 67108864 7 67108864 9573596 9573598 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 235209379 67108864 7 67108864 235209379 67108864 7 67108864 (Ns552p623 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p625 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 19147194 67108864 2 67108864 9573597 33554432 1 33554432 (Ns552p624 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz427 := (@HMul.hMul Real Real Real qz584 qz582 qz630)

noncomputable abbrev qz90 := (Real.cos qz427)

noncomputable abbrev qz639 := (@HMul.hMul Real Real Real qz742 qz761 qz761)

noncomputable abbrev qz428 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz639 qz630) qz603)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz428))

noncomputable def Ns552p626 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 1055100601619481 

noncomputable def Ns552p627 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz90) qz91 314048039 67108864 5541 

noncomputable abbrev qz92 := (@Neg.neg Real Real.instNeg (Real.cos qz427))

noncomputable def Ns552p628 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz90) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz92)) Bool.true 314048039 67108864 5541 67108864 (BSN.inv_eq_neg_inv_neg qz90) 

noncomputable def Ns552p629 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz92) Bool.false 314048039 67108864 5541 67108864 314048039 67108864 

noncomputable def Ns552p630 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true 7170240 33554432 1215584432 322458091520000 112035 524288 75974027 20153630720000 

noncomputable abbrev qz93 := qz427

noncomputable def Ns552p631 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 14983285) qz597) Bool.false 14983285 8388608 123 33554432 Bool.true 7170240 33554432 1 

noncomputable def Ns552p632 := nat_lit 42098277644663625057313273 

noncomputable def Ns552p633 := nat_lit 11529215046068469760000000000000 

noncomputable def Ns552p634 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 19077311 67108864 39 67108864 16869679210423428840605 9444732965739290427392 Ns552p632 

noncomputable def Ns552p635 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 824383679 67108864 39 67108864 12 1 0 1 19077311 19077311 67108864 39 

noncomputable def Ns552p636 := @Ns552p635 67108864 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 824383679 67108864 39 67108864 824383679 67108864 39 67108864 (Ns552p622 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p637 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 16869679210423428840605 9444732965739290427392 Ns552p632 Ns552p633 14983285 8388608 123 33554432 (@Ns552p634 Ns552p633 RS553to564.d55 (Ns552p636 rfl rfl) rfl) 

noncomputable def Ns552p638 := nat_lit 24814099899297844483071790778349954328413842843391353452460504190734493692151944314453140625 

noncomputable def Ns552p639 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600 

noncomputable def Ns552p640 := nat_lit 128021963792186914489565151980373048832275930736849198326098714033860760750390869140625 

noncomputable def Ns552p641 := nat_lit 149933870302907105480898424441513766635619152321649050315934923487784847053550218090478740625 

noncomputable def Ns552p642 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600 

noncomputable def Ns552p643 := BSN.cos_dyadic_bound_t 14983285 8388608 4 3 33554432 9610000 Ns552p638 Ns552p639 Ns552p640 Ns552p641 Ns552p642 Ns552p640 7170240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 14983285) (BSN.cosEvenQ 8388608) 0 3 Ns552p638 Ns552p639 Ns552p640 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 14983285) (BSN.cosOddQ 8388608) 0 3 Ns552p641 Ns552p642 Ns552p640 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p644 := @Enclosure.Real.IsNear.inv_image qz92 112035 524288 75974027 20153630720000 157021249 157026790 33554432 (@Enclosure.Real.IsNear.neg qz90 Bool.true 112035 524288 75974027 20153630720000 (Ns552p630 (@Ns552p631 9610000 (Ns552p637 rfl) (Enclosure.sfrac_false_div 14983285 8388608) (Ns552p643 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns552p645 := Ns552p628 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz92) Bool.false 314048039 67108864 5541 67108864 (@Ns552p629 5541 67108864 (Ns552p644 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p646 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true 3359679 33554432 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz355 qz352 qz428)

noncomputable def Ns552p647 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3504531)) (@Nat.cast Real Real.instNatCast 2097152)) Bool.true 3504531 2097152 

noncomputable def Ns552p648 := nat_lit 1059179504400682150327117991645 

noncomputable def Ns552p649 := nat_lit 633825300114114700748351602688 

noncomputable def Ns552p650 := nat_lit 110785327525688850386062366501890613 

noncomputable def Ns552p651 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns552p648 Ns552p649 Ns552p650 

noncomputable def Ns552p652 := nat_lit 19342813113834066795298816000000000000000 

noncomputable abbrev qz95 := qz428

noncomputable def Ns552p653 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 1197787851104639 

noncomputable abbrev qz429 := (@HSub.hSub Real Real Real qz588 qz639 qz630)

noncomputable abbrev qz96 := qz429

noncomputable def Ns552p654 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 916312874393983 4503599627370496 4105277475 4503599627370496 1 16 

noncomputable abbrev qz430 := qz639

noncomputable abbrev qz97 := qz430

noncomputable def Ns552p655 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 363943794990721 4503599627370496 1488031779 4503599627370496 19077311 67108864 39 67108864 

noncomputable def Ns552p656 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 19077311 67108864 39 67108864 19077311 67108864 39 67108864 363943794990721 4503599627370496 

noncomputable def Ns552p657 := nat_lit 1131611099475014497307620162844098323178886898043759816991400542089694290089701691441 

noncomputable def Ns552p658 := nat_lit 3466537250751077332112698720796095110148055492926080949987665366995300109908547993600 

noncomputable def Ns552p659 := nat_lit 3432091610487142038200722535983823401364749150111312271243768048343122087923761 

noncomputable def Ns552p660 := nat_lit 6843943656841008294713664850325162090826332463622304787032135979785174282180875145265 

noncomputable def Ns552p661 := nat_lit 315454889818348037222255583592444655023473049856273366448877548396572310001677867417600 

noncomputable def Ns552p662 := BSN.cos_dyadic_bound_t 3504531 2097152 4 3 33554432 9610000 Ns552p657 Ns552p658 Ns552p659 Ns552p660 Ns552p661 Ns552p659 3359679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 3504531) (BSN.cosEvenQ 2097152) 0 3 Ns552p657 Ns552p658 Ns552p659 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 3504531) (BSN.cosOddQ 2097152) 0 3 Ns552p660 Ns552p661 Ns552p659 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p663 := @Ns552p646 3766958864 644916183040000 3359679 33554432 235434929 40307261440000 (@Ns552p647 385 67108864 Bool.true 3359679 33554432 1 9610000 (@Ns552p651 Ns552p652 3504531 2097152 385 67108864 (@Ns552p653 4503599627370496 4105277475 4503599627370496 Ns552p648 Ns552p649 Ns552p650 Ns552p652 RS553to564.d55 (@Ns552p654 0 1 19164605617674224 1197787851104639 4503599627370496 4105277475 4503599627370496 (@Ns552p655 61492716069154887565312 916312874393983 4503599627370496 4105277475 4503599627370496 (@Ns552p656 1488031779 4503599627370496 (Ns552p636 rfl rfl) (Ns552p636 rfl rfl) rfl) (Ns552p636 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3504531 2097152) (BSN.cos_neg_of_bound 3504531 2097152 Bool.true 3359679 33554432 1 9610000 (Ns552p662 rfl rfl)) rfl rfl) 

noncomputable def Ns552p664 := @Ns552p620 92322053093776909096411 Ns552p527 (Ns552p621 qz33 (@Enclosure.Real.IsNear.of_eq qz637 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 9573597 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz81 (BSN.t_div_two_pi_nonneg qz80 948154 1000 qz83)) Ns552p625) rfl) (@Ns552p626 2251799813685248 9630162989296957 270497452618940416000 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 948154 1000 12 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 948154 1000 12 qz83 rfl rfl rfl))) (@Ns552p627 67108864 3359679 33554432 235434929 40307261440000 1055100601619481 2251799813685248 9630162989296957 270497452618940416000 Ns552p645 (Ns552p663 rfl) rfl)) 

noncomputable def Ns552p665 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 55568419368416487535211 75557863725914323419136 Ns552p526 Ns552p527 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HMul.hMul Real Real Real qz5 qz631 (Zeta.RiemannSiegel.correction qz82))) Bool.false 55568419368416487535211 75557863725914323419136 Ns552p526 Ns552p527 (BSN.hardyZApproximantRS₀_eq qz80 12 (@BSN.floor_sqrt_eq_dec qz80 948154 1000 12 qz83 rfl rfl rfl)) (@Ns552p529 55568419368416487535211 75557863725914323419136 Ns552p526 Ns552p527 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12)) Bool.false 58326257 67108864 272597 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (Ns552p619 (Ns552p618 rfl rfl rfl rfl) rfl rfl)) (Ns552p664 rfl) rfl rfl)) 

theorem RS553to564.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 55568419368416487535211 75557863725914323419136 Ns552p526 Ns552p527 := Ns552p665 

noncomputable def Ns552p666 := nat_lit 1453843965471866029521327 

noncomputable def Ns552p667 := nat_lit 1418185684386790328238080000 

noncomputable def Ns552p668 := nat_lit 19011422153064889027048463400960 

noncomputable abbrev qz763 := (Enclosure.sfrac Bool.false 949407 1000)

noncomputable abbrev qz640 := qz763

noncomputable abbrev qz431 := qz640

noncomputable abbrev qz98 := qz431

noncomputable abbrev qz764 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 949407 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz641 := qz764

noncomputable abbrev qz432 := qz641

noncomputable abbrev qz99 := qz432

noncomputable abbrev qz765 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 949407 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz642 := qz765

noncomputable abbrev qz433 := qz642

noncomputable abbrev qz100 := qz433

noncomputable abbrev qz643 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz99 qz9))

noncomputable def Ns552p669 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HMul.hMul Real Real Real qz5 qz643 (Zeta.RiemannSiegel.correction qz100)) 971090001 268435456 136479 134217728 2488682652920067359871 18889465931478580854784 11764987503882864081327 Ns552p667 Ns552p668 

noncomputable def Ns552p670 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin BSN.quadSignPos 11 12 949407 1000 287 536870912 268435456 9007199254740992 Bool.false 1023784504951 4520 1334074092 57 154981288 8 

noncomputable def Ns552p671 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 949407 1000 177 235 536870912 268435456 9007199254740992 Bool.false 1023784504951 4520 

noncomputable def Ns552p672 := Ns552p671 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 1048902859 219780 Bool.true 597112405 Bool.true 265308153 28296951008113761 1 Bool.false 481400628 Bool.true Bool.false 254640808 Bool.false Bool.true 1124358022 

noncomputable def Ns552p673 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 949407 1000 42 114 536870912 268435456 9007199254740992 Bool.false 1023784504951 4520 

noncomputable def Ns552p674 := Ns552p673 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 822203103 179484 Bool.true 706343010 Bool.true 22733817 28296951008113761 1 Bool.false 135490729 Bool.true Bool.false 536389651 Bool.true Bool.true 1048902859 

noncomputable def Ns552p675 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 949407 1000 131 37 536870912 268435456 9007199254740992 Bool.false 1023784504951 4520 

noncomputable def Ns552p676 := Ns552p675 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 637488287 133364 Bool.false 34334910 Bool.false 733949916 28296951008113761 1 Bool.false 34311509 Bool.false Bool.false 525770118 Bool.true Bool.true 822203103 

noncomputable def Ns552p677 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 949407 1000 376 241 536870912 268435456 9007199254740992 Bool.false 1023784504951 4520 

noncomputable def Ns552p678 := Ns552p677 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 814383662 78702 Bool.false 91416929 Bool.false 200647534 28296951008113761 1 Bool.false 529106585 Bool.false Bool.false 196009040 Bool.true Bool.true 637488287 

noncomputable def Ns552p679 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 949407 1000 795 549 536870912 268435456 9007199254740992 Bool.false 1023784504951 4520 

noncomputable def Ns552p680 := Ns552p679 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870840 4584 Bool.false 45850620 Bool.false 832080609 28296951008113761 1 Bool.false 45794903 Bool.false Bool.false 536753375 Bool.true Bool.true 814383662 

noncomputable def Ns552p681 := nat_lit 25157841804023377065920554446033962586631997475963518235561 

noncomputable def Ns552p682 := nat_lit 13192730899869710813529509944788751595330413910818816000 

noncomputable def Ns552p683 := nat_lit 370257351132434902257175806627360000 

noncomputable def Ns552p684 := nat_lit 2109149798791552351704680559107507853120 

noncomputable abbrev qz644 := (@Eq.refl Real qz763)

noncomputable abbrev qz434 := qz644

noncomputable abbrev qz101 := qz434

noncomputable def Ns552p685 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 949407 1000 3605495606596 16000000 1898814 4000 2000 Ns552p683 Ns552p684 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p686 := nat_lit 72454584395587325949851196804577812249500152730774932518415680 

noncomputable abbrev qz645 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1898814))))

noncomputable abbrev qz435 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 949407 4000) (Real.log (Enclosure.sfrac Bool.false 3605495606596 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz645))

noncomputable abbrev qz646 := (Enclosure.sfrac Bool.false 949407 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz435 qz646) (@HMul.hMul Real Real Real qz355 qz646 (Real.log Real.pi)))

noncomputable def Ns552p687 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns552p683 Ns552p684) 34352510716433707602489 18014398509481984000 132550197349080896889 Ns552p244 Ns552p683 Ns552p684 0 1 Ns552p686 

noncomputable def Ns552p688 := nat_lit 2305357969727692248511200362496000 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz359 qz435 qz646)

noncomputable def Ns552p689 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz646 (Real.log Real.pi)) 44141666043143027987001 18014398509481984000 11967603010942659 3844000000000000000000 36467445368727 67108864000 2848221 536870912000 Ns552p688 34352510716433707602489 18014398509481984000 

noncomputable def Ns552p690 := nat_lit 17656666417257211194800400 

noncomputable abbrev qz104 := qz435

noncomputable def Ns552p691 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz646 10538632813197781795749 3602879701896396800 11967603010942659 3844000000000000000000 949407 2000 0 1 Ns552p690 44141666043143027987001 18014398509481984000 11967603010942659 3844000000000000000000 

noncomputable def Ns552p692 := nat_lit 23730891405256006037660555974910410752 

noncomputable def Ns552p693 := nat_lit 119203771311637625758023680 

noncomputable def Ns552p694 := nat_lit 77970550312618605422489854258442246896872051541328737425846357258586274464645971258819272540337564669149575214005317610538199975746053426625479370867635241355396487660884163694061158400 

noncomputable def Ns552p695 := nat_lit 1898620746419429119508329569376839931671472135812740300821689804831647465583475457172771645084254100090792962009282114167172867894113443142501602099399160488394181927105705129583575040 

noncomputable def Ns552p696 := nat_lit 42635549145908207007102885994654906717711504546197304955536019409827127841319475425503610940823778579514570786136381771250879836716310043652802613804232259620529491524777410560 

noncomputable def Ns552p697 := BSN.log_dyadic_bound 1508343606596 5702647606596 8 7 Ns552p694 268435456 76880000 Ns552p695 Ns552p696 145459537 7210991213192 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1508343606596) (BSN.artanhQ 5702647606596) 0 7 Ns552p695 Ns552p694 Ns552p696 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz436 := (Real.log (Enclosure.sfrac Bool.false 3605495606596 16000000))

noncomputable def Ns552p698 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 949407 4000) qz436 949407 4000 0 1 55508581600914535 4503599627370496 12500016337 961000000000000000 10540047186395893186149 3602879701896396800 11867603010462159 3844000000000000000000 (Enclosure.Real.IsNear.const Bool.false 949407 4000) (BSN.isNear_log_sfrac 3605495606596 16000000 55508581600914535 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3605495606596) qz362)) Bool.false Ns552p693 Ns552p114 1000001306960000 76880000000000000000000 55508581600914535 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3605495606596 16000000 17 7210991213192 4194304000000 145459537 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p697 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p699 := BSN.arctan_dyadic_bound_f 1000 1898814 1 0 33554432 9610000 0 1 1 0 1 1 17671 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1898814) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1898814) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p700 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1898814))) 884279719003555 562949953421312 1 2000000000000000 17671 33554432 1 9610000 29661555811656986001408 883983248819619 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p699 rfl) rfl rfl 

noncomputable abbrev qz437 := (@HMul.hMul Real Real Real qz584 qz589 qz645)

noncomputable abbrev qz105 := qz437

noncomputable abbrev qz438 := qz645

noncomputable abbrev qz106 := qz438

noncomputable def Ns552p701 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 949407 4000) qz436) qz105 10540047186395893186149 3602879701896396800 11867603010462159 3844000000000000000000 883983248819619 2251799813685248 200000000961 7688000000000000000 Ns552p692 10538632813197781795749 3602879701896396800 11967603010942659 3844000000000000000000 (Ns552p698 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz106 1 4 0 1 883983248819619 562949953421312 200000000961 1922000000000000000 883983248819619 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p700 rfl) 

noncomputable def Ns552p702 := @Ns552p687 Ns552p681 Ns552p682 132550197349080896889 Ns552p244 (@Ns552p689 132550197349080896889 Ns552p244 (Ns552p691 (Ns552p701 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 949407 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz646 (Real.log Real.pi) 949407 2000 0 1 38410761 33554432 3 268435456 36467445368727 67108864000 2848221 536870912000 (Enclosure.Real.IsNear.const Bool.false 949407 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p683 Ns552p684) 

noncomputable def Ns552p703 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns552p681 Ns552p682 132550197349080896889 Ns552p244 63986531559 33554432 283 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz370 qz102 (Enclosure.sfrac Bool.true Ns552p683 Ns552p684)) Bool.false Ns552p681 Ns552p682 132550197349080896889 Ns552p244 Ns552p685 (Ns552p702 rfl rfl)) 

noncomputable def Ns552p704 := nat_lit 4835703278458516698824704 

noncomputable def Ns552p705 := BSN.cos_dyadic_bound_f 68893028 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108855 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 68893028) qz595 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 68893028) qz596 0 0 rfl) rfl rfl 

noncomputable def Ns552p706 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 63986531559) qz627) Bool.false 63986531559 33554432 283 33554432 Bool.true 67108855 67108864 1 9610000 (Ns552p703 rfl) (Enclosure.sfrac_false_div 63986531559 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 63986531559) qz627) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2423957942524977348608) (@Nat.cast Real Real.instNatCast Ns552p704)) 226375608064910080 72057594037927936 Bool.false 67108855 67108864 303 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q2 63986531559 33554432 226375608064910080 72057594037927936 303 2423957942524977348608 Ns552p704 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108855 67108864 2423957942524977348608 Ns552p704 68893028 137438953472 19238770 19220000 (Ns552p705 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p707 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns552p681 Ns552p682 132550197349080896889 Ns552p244 1023784504951 536870912 4520 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz370 qz102 (Enclosure.sfrac Bool.true Ns552p683 Ns552p684)) Bool.false Ns552p681 Ns552p682 132550197349080896889 Ns552p244 Ns552p685 (Ns552p702 rfl rfl)) 

noncomputable def Ns552p708 := Ns552p680 78702 BSN.abs_quadSignPos (BSN.cos_quad_nat3 795 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 45794903 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 549 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536753375 536870912) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 67108855 67108864 172074027 20153630720000 536870840 536870912 4584 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 67108855 67108864 172074027 20153630720000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 67108855 67108864 2753184432 322458091520000 67108855 67108864 172074027 20153630720000 (Ns552p706 rfl rfl) rfl)) rfl) (Ns552p707 rfl) RS553to564.d7 

noncomputable def Ns552p709 := nat_lit 4419578483870889683502963360000 

noncomputable def Ns552p710 := BSN.sin_dyadic_bound_f 45850620 536870912 2 1 536870912 268435456 Ns552p709 Ns552p283 Ns552p709 Ns552p709 Ns552p284 Ns552p709 45794903 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 45850620) qz371 0 1 Ns552p709 Ns552p283 Ns552p709 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 45850620) qz372 0 1 Ns552p709 Ns552p284 Ns552p709 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p711 := nat_lit 172007678156665100329980270958786483801312590012401475655101269171727167551633990121201199508976272059450839665281 

noncomputable def Ns552p712 := nat_lit 110150079450430980417902843989504469975898302965901809556728974700524563747370898818728880691756719723121281 

noncomputable def Ns552p713 := nat_lit 859025424093834097604022536322733390554009206485473446070572915843262207656050423217768326685490478434167618407041 

noncomputable def Ns552p714 := BSN.sin_dyadic_bound_f 832080609 536870912 4 3 536870912 268435456 Ns552p711 Ns552p177 Ns552p712 Ns552p713 Ns552p180 Ns552p712 536753375 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 832080609) qz371 0 3 Ns552p711 Ns552p177 Ns552p712 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 832080609) qz372 0 3 Ns552p713 Ns552p180 Ns552p712 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p715 := nat_lit 69840366731834324791002119863681 

noncomputable def Ns552p716 := BSN.cos_dyadic_bound_f 91416929 536870912 2 1 536870912 268435456 Ns552p715 Ns552p157 Ns552p715 Ns552p715 Ns552p158 Ns552p715 529106585 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 91416929) qz373 0 1 Ns552p715 Ns552p157 Ns552p715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 91416929) qz374 0 1 Ns552p715 Ns552p158 Ns552p715 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p717 := nat_lit 1620821937452240772232943848696336 

noncomputable def Ns552p718 := BSN.sin_dyadic_bound_f 200647534 536870912 2 1 536870912 268435456 Ns552p717 Ns552p283 Ns552p717 Ns552p717 Ns552p284 Ns552p717 196009040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 200647534) qz371 0 1 Ns552p717 Ns552p283 Ns552p717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 200647534) qz372 0 1 Ns552p717 Ns552p284 Ns552p717 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p719 := Ns552p678 133364 BSN.abs_quadSignPos (BSN.cos_quad_nat0 376 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 529106585 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 196009040 536870912) qz101 rfl rfl (Ns552p708 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p710 rfl rfl) (Ns552p714 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p707 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p716 rfl rfl) (Ns552p718 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p720 := nat_lit 1389772306407508352014205610000 

noncomputable def Ns552p721 := BSN.sin_dyadic_bound_f 34334910 536870912 2 1 536870912 268435456 Ns552p720 Ns552p283 Ns552p720 Ns552p720 Ns552p284 Ns552p720 34311509 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 34334910) qz371 0 1 Ns552p720 Ns552p283 Ns552p720 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 34334910) qz372 0 1 Ns552p720 Ns552p284 Ns552p720 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p722 := nat_lit 104045958014345492302038664304212548326847890855079427023804818723162678669880561790252361871742916795203590291456 

noncomputable def Ns552p723 := nat_lit 24434142442398369367455237406983279086015830845333819808739902916969158996370493038870308612987248973971456 

noncomputable def Ns552p724 := nat_lit 519858657732898663408553552886564971563806721790444017073816556649948420257649219099182537067185551308406931849216 

noncomputable def Ns552p725 := BSN.sin_dyadic_bound_f 733949916 536870912 4 3 536870912 268435456 Ns552p722 Ns552p177 Ns552p723 Ns552p724 Ns552p180 Ns552p723 525770118 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 733949916) qz371 0 3 Ns552p722 Ns552p177 Ns552p723 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 733949916) qz372 0 3 Ns552p724 Ns552p180 Ns552p723 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p726 := Ns552p676 179484 BSN.abs_quadSignPos (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 34311509 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 37 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 525770118 536870912) qz101 rfl rfl (Ns552p719 rfl rfl) (Ns552p707 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p721 rfl rfl) (Ns552p725 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p727 := nat_lit 34349577048722147067016000515119267572867439064420470380763495154285691601463941112768741023942558134361664000000 

noncomputable def Ns552p728 := nat_lit 15423673411140123749825697284641174575125050136328652475568857549833661994283834230330095951601000000000000 

noncomputable def Ns552p729 := nat_lit 208140024110525535139547555121392490686410850859651131549278363475426598793925702801581385779109507021567961600000 

noncomputable def Ns552p730 := BSN.cos_dyadic_bound_f 706343010 536870912 4 3 536870912 268435456 Ns552p727 Ns552p151 Ns552p728 Ns552p729 Ns552p154 Ns552p728 135490729 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 706343010) qz373 0 3 Ns552p727 Ns552p151 Ns552p728 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 706343010) qz374 0 3 Ns552p729 Ns552p154 Ns552p728 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p731 := nat_lit 267109564317405647835131681121 

noncomputable def Ns552p732 := BSN.cos_dyadic_bound_f 22733817 536870912 2 1 536870912 268435456 Ns552p731 Ns552p157 Ns552p731 Ns552p731 Ns552p158 Ns552p731 536389651 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22733817) qz373 0 1 Ns552p731 Ns552p157 Ns552p731 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22733817) qz374 0 1 Ns552p731 Ns552p158 Ns552p731 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p733 := Ns552p674 219780 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 135490729 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536389651 536870912) qz101 rfl rfl (Ns552p726 rfl) (Ns552p707 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p730 rfl rfl) (Ns552p732 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p734 := nat_lit 31952538189333391427035867480778597566686322033787517072344654542726230625 

noncomputable def Ns552p735 := nat_lit 16160275110912906329312178519793016979307544582318067418809665250390625 

noncomputable def Ns552p736 := nat_lit 83659054812360261412941718922530947790021488349643553556510308153877590625 

noncomputable def Ns552p737 := BSN.sin_dyadic_bound_f 597112405 536870912 3 2 536870912 268435456 Ns552p734 Ns552p130 Ns552p735 Ns552p736 Ns552p133 Ns552p735 481400628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 597112405) qz371 0 2 Ns552p734 Ns552p130 Ns552p735 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 597112405) qz372 0 2 Ns552p736 Ns552p133 Ns552p735 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p738 := nat_lit 1244721621309798030315309789898655580554447322949019252237797874306135745 

noncomputable def Ns552p739 := nat_lit 24547358739338738590791724240848724236144111165644023927966911968961 

noncomputable def Ns552p740 := nat_lit 3259945455325797816677616739323898479708122564876972713155492010087167681 

noncomputable def Ns552p741 := BSN.sin_dyadic_bound_f 265308153 536870912 3 2 536870912 268435456 Ns552p738 Ns552p130 Ns552p739 Ns552p740 Ns552p133 Ns552p739 254640808 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 265308153) qz371 0 2 Ns552p738 Ns552p130 Ns552p739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 265308153) qz372 0 2 Ns552p740 Ns552p133 Ns552p739 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p742 := Ns552p672 256021 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 481400628 536870912) BSN.abs_quadSignPos qz598 (BSN.sfrac_eq_quadSignPos_mul Bool.false 254640808 536870912) qz101 rfl rfl (Ns552p733 rfl) (Ns552p707 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p737 rfl rfl) (Ns552p741 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p743 := nat_lit 121809866020182864460669311299857645810677281496767390950323961491139182153946137491328367265144141686433740015681 

noncomputable def Ns552p744 := nat_lit 39184334708568669305630095373012816017841193658151243622425423625237638714105177977626673949584874108143681 

noncomputable def Ns552p745 := nat_lit 608540829017710472863207122052639228946136278308007943796926374374279260612483558776615513378264608104596741605441 

noncomputable def Ns552p746 := BSN.sin_dyadic_bound_f 763412687 536870912 4 3 536870912 268435456 Ns552p743 Ns552p177 Ns552p744 Ns552p745 Ns552p180 Ns552p744 530935983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 763412687) qz371 0 3 Ns552p743 Ns552p177 Ns552p744 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 763412687) qz372 0 3 Ns552p745 Ns552p180 Ns552p744 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p747 := Ns552p670 Bool.true 1124358022 256021 Bool.true 763412687 28296951008113761 1 Bool.false 530935983 Bool.false Bool.true 971090001 272958 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 530935983 536870912) qz101 rfl (Ns552p742 rfl) (Ns552p707 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p746 rfl rfl) rfl 

noncomputable def Ns552p748 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) 971090001 536870912 272958 536870912 971090001 536870912 272958 536870912 1042699948941901824 971090001 268435456 136479 134217728 (Ns552p747 rfl rfl rfl rfl) 

noncomputable def Ns552p749 := @Enclosure.Real.IsNear.mulLit_ff qz643 (Zeta.RiemannSiegel.correction qz100) 9570437 33554432 1 33554432 260038559672883 562949953421312 19636241177500839 676243631547351040000 2488682652920067359871 18889465931478580854784 

noncomputable abbrev qz647 := (@HPow.hPow Real Real Real qz7 qz99 qz9)

noncomputable def Ns552p750 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz647 1 1 0 1 9570437 33554432 1 33554432 9570437 33554432 1 33554432 

noncomputable def Ns552p751 := @Enclosure.Real.IsNear.sqrt_image qz99 10140337990749 67108864000 949407 67108864000 412464089 412464128 33554432 (@Enclosure.Real.IsNear.of_eq qz99 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 10140337990749 67108864000 949407 67108864000 (BSN.t_div_two_pi_mk qz98 949407 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 949407 1000 0 1 10680707 67108864 1 67108864 10140337990749 67108864000 949407 67108864000 (Enclosure.Real.IsNear.const Bool.false 949407 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz766 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 949407 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz648 := qz766

noncomputable abbrev qz439 := qz648

noncomputable abbrev qz107 := qz439

noncomputable def Ns552p752 := @Enclosure.Real.IsNear.sqrt_image qz107 824928217 67108864 39 67108864 117643521 117643528 33554432 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 824928217 67108864 39 67108864 824928217 67108864 39 67108864 (Ns552p751 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p753 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 235287049 67108864 7 67108864 9570436 9570438 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 235287049 67108864 7 67108864 235287049 67108864 7 67108864 (Ns552p752 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p754 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 19140874 67108864 2 67108864 9570437 33554432 1 33554432 (Ns552p753 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz440 := (@HMul.hMul Real Real Real qz584 qz582 qz642)

noncomputable abbrev qz108 := (Real.cos qz440)

noncomputable abbrev qz649 := (@HMul.hMul Real Real Real qz742 qz765 qz765)

noncomputable abbrev qz441 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz649 qz642) qz603)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz441))

noncomputable def Ns552p755 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 260038559672883 

noncomputable def Ns552p756 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz108) qz109 254976511 67108864 3653 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg (Real.cos qz440))

noncomputable def Ns552p757 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz108) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz110)) Bool.true 254976511 67108864 3653 67108864 (BSN.inv_eq_neg_inv_neg qz108) 

noncomputable def Ns552p758 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz110) Bool.false 254976511 67108864 3653 67108864 254976511 67108864 

noncomputable def Ns552p759 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true 8831401 33554432 1215584432 322458091520000 8831401 33554432 75974027 20153630720000 

noncomputable abbrev qz111 := qz440

noncomputable def Ns552p760 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123287713) qz380) Bool.false 123287713 67108864 123 33554432 Bool.true 8831401 33554432 1 

noncomputable def Ns552p761 := nat_lit 1052456941121268172235690321 

noncomputable def Ns552p762 := nat_lit 288230376151711744000000000000000 

noncomputable def Ns552p763 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 19621849 67108864 39 67108864 17351203120050186673195 9444732965739290427392 Ns552p761 

noncomputable def Ns552p764 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 824928217 67108864 39 67108864 12 1 0 1 19621849 19621849 67108864 39 

noncomputable def Ns552p765 := @Ns552p764 67108864 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 824928217 67108864 39 67108864 824928217 67108864 39 67108864 (Ns552p751 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p766 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 17351203120050186673195 9444732965739290427392 Ns552p761 Ns552p762 123287713 67108864 123 33554432 (@Ns552p763 Ns552p762 RS553to564.d55 (Ns552p765 rfl rfl) rfl) 

noncomputable def Ns552p767 := nat_lit 1909772033953949329475026069322254491580870417607932068879042152329388641471290135175239802662034239361 

noncomputable def Ns552p768 := nat_lit 12332114755851753130709892292046900336113559147957704015141522374231914986222549070130417554321281 

noncomputable def Ns552p769 := nat_lit 11533869906292786823041753144349456680949307923281434646670011120812483467183715712779521893899987218305 

noncomputable def Ns552p770 := BSN.cos_dyadic_bound_t 123287713 67108864 4 3 33554432 9610000 Ns552p767 Ns552p203 Ns552p768 Ns552p769 Ns552p206 Ns552p768 8831401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 123287713) qz604 0 3 Ns552p767 Ns552p203 Ns552p768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 123287713) (BSN.cosOddQ 67108864) 0 3 Ns552p769 Ns552p206 Ns552p768 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p771 := @Enclosure.Real.IsNear.inv_image qz110 8831401 33554432 75974027 20153630720000 127486429 127490082 33554432 (@Enclosure.Real.IsNear.neg qz108 Bool.true 8831401 33554432 75974027 20153630720000 (Ns552p759 (@Ns552p760 9610000 (Ns552p766 rfl) (Enclosure.sfrac_false_div 123287713 67108864) (Ns552p770 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns552p772 := Ns552p757 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz110) Bool.false 254976511 67108864 3653 67108864 (@Ns552p758 3653 67108864 (Ns552p771 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p773 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true 4079412 33554432 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz355 qz352 qz441)

noncomputable def Ns552p774 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 113593413)) qz380) Bool.true 113593413 67108864 

noncomputable def Ns552p775 := nat_lit 1072859456142101090830681445005 

noncomputable def Ns552p776 := nat_lit 22386306624249352027769045809082197 

noncomputable def Ns552p777 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns552p775 Ns552p649 Ns552p776 

noncomputable def Ns552p778 := nat_lit 3868562622766813359059763200000000000000 

noncomputable abbrev qz113 := qz441

noncomputable def Ns552p779 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 1213258014501391 

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz588 qz649 qz642)

noncomputable abbrev qz114 := qz442

noncomputable def Ns552p780 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 931783037790735 4503599627370496 4147751439 4503599627370496 1 16 

noncomputable abbrev qz443 := qz649

noncomputable abbrev qz115 := qz443

noncomputable def Ns552p781 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 385016958178801 4503599627370496 1530505743 4503599627370496 19621849 67108864 39 67108864 

noncomputable def Ns552p782 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 19621849 67108864 39 67108864 19621849 67108864 39 67108864 385016958178801 4503599627370496 

noncomputable def Ns552p783 := nat_lit 1373712393874048956275598124992673195909782391455585151763816714774684971493329310219547967058326606161 

noncomputable def Ns552p784 := nat_lit 4615702205360411965430791048107988058881899847303819670241146906334562722831412342926398876832081 

noncomputable def Ns552p785 := nat_lit 8306815865244972871378221507795055560168336713080039458166466487844193368498955402524961826155974381905 

noncomputable def Ns552p786 := BSN.cos_dyadic_bound_t 113593413 67108864 4 3 33554432 9610000 Ns552p783 Ns552p203 Ns552p784 Ns552p785 Ns552p206 Ns552p784 4079412 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 113593413) qz604 0 3 Ns552p783 Ns552p203 Ns552p784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 113593413) (BSN.cosOddQ 67108864) 0 3 Ns552p785 Ns552p206 Ns552p784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p787 := @Ns552p773 3805398864 644916183040000 1019853 8388608 237837429 40307261440000 (@Ns552p774 389 67108864 Bool.true 4079412 33554432 1 9610000 (@Ns552p777 Ns552p778 113593413 67108864 389 67108864 (@Ns552p779 4503599627370496 4147751439 4503599627370496 Ns552p775 Ns552p649 Ns552p776 Ns552p778 RS553to564.d55 (@Ns552p780 0 1 19412128232022256 1213258014501391 4503599627370496 4147751439 4503599627370496 (@Ns552p781 62530901160605295575040 931783037790735 4503599627370496 4147751439 4503599627370496 (@Ns552p782 1530505743 4503599627370496 (Ns552p765 rfl rfl) (Ns552p765 rfl rfl) rfl) (Ns552p765 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 113593413 67108864) (BSN.cos_neg_of_bound 113593413 67108864 Bool.true 4079412 33554432 1 9610000 (Ns552p786 rfl rfl)) rfl rfl) 

noncomputable def Ns552p788 := @Ns552p749 11764987503882864081327 Ns552p667 (Ns552p750 qz33 (@Enclosure.Real.IsNear.of_eq qz647 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 9570437 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz99 (BSN.t_div_two_pi_nonneg qz98 949407 1000 qz101)) Ns552p754) rfl) (@Ns552p755 562949953421312 19636241177500839 676243631547351040000 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 949407 1000 12 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 949407 1000 12 qz101 rfl rfl rfl))) (@Ns552p756 67108864 1019853 8388608 237837429 40307261440000 260038559672883 562949953421312 19636241177500839 676243631547351040000 Ns552p772 (Ns552p787 rfl) rfl)) 

noncomputable def Ns552p789 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 70823066506776545297535 18889465931478580854784 Ns552p666 Ns552p667 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HMul.hMul Real Real Real qz5 qz643 (Zeta.RiemannSiegel.correction qz100))) Bool.true 70823066506776545297535 18889465931478580854784 Ns552p666 Ns552p667 (BSN.hardyZApproximantRS₀_eq qz98 12 (@BSN.floor_sqrt_eq_dec qz98 949407 1000 12 qz101 rfl rfl rfl)) (@Ns552p669 70823066506776545297535 18889465931478580854784 Ns552p666 Ns552p667 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12)) Bool.true 971090001 268435456 136479 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (Ns552p748 (Ns552p747 rfl rfl rfl rfl) rfl rfl)) (Ns552p788 rfl) rfl rfl)) 

theorem RS553to564.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 70823066506776545297535 18889465931478580854784 Ns552p666 Ns552p667 := Ns552p789 

noncomputable def Ns552p790 := nat_lit 141818568438679032823808000 

noncomputable def Ns552p791 := nat_lit 6831820761252057252014785036288 

noncomputable abbrev qz767 := (Enclosure.sfrac Bool.false 950659 1000)

noncomputable abbrev qz650 := qz767

noncomputable abbrev qz444 := qz650

noncomputable abbrev qz116 := qz444

noncomputable abbrev qz768 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 950659 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz651 := qz768

noncomputable abbrev qz445 := qz651

noncomputable abbrev qz117 := qz445

noncomputable abbrev qz769 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 950659 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz652 := qz769

noncomputable abbrev qz446 := qz652

noncomputable abbrev qz118 := qz446

noncomputable abbrev qz653 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns552p792 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HMul.hMul Real Real Real qz5 qz653 (Zeta.RiemannSiegel.correction qz118)) 396543719 268435456 136663 134217728 2453767914847501996843 18889465931478580854784 1024678118484921885391 Ns552p790 Ns552p791 

noncomputable def Ns552p793 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin BSN.quadSignPos 11 12 950659 1000 287 536870912 268435456 9007199254740992 Bool.false 1025471168731 4527 1334074092 57 154981288 8 

noncomputable def Ns552p794 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 950659 1000 177 235 536870912 268435456 9007199254740992 Bool.false 1025471168731 4527 

noncomputable def Ns552p795 := Ns552p794 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.false 315758372 220076 Bool.true 458159702 Bool.true 190419368 28296951008113761 1 Bool.false 404539068 Bool.true Bool.false 186451929 Bool.false Bool.false 244049250 

noncomputable def Ns552p796 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 950659 1000 42 113 536870912 268435456 9007199254740992 Bool.false 1025471168731 4527 

noncomputable def Ns552p797 := Ns552p796 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.false 619241949 179726 Bool.true 417401609 Bool.true 656276580 28296951008113761 1 Bool.false 382622422 Bool.true Bool.false 504618363 Bool.true Bool.false 315758372 

noncomputable def Ns552p798 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 950659 1000 131 38 536870912 268435456 9007199254740992 Bool.false 1025471168731 4527 

noncomputable def Ns552p799 := Ns552p798 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.false 617317121 133544 Bool.false 516645386 Bool.false 269331258 28296951008113761 1 Bool.false 440515437 Bool.false Bool.false 470718424 Bool.true Bool.false 619241949 

noncomputable def Ns552p800 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 950659 1000 377 241 536870912 268435456 9007199254740992 Bool.false 1025471168731 4527 

noncomputable def Ns552p801 := Ns552p800 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 858293474 78809 Bool.false 2950950 Bool.false 805507713 28296951008113761 1 Bool.false 2950935 Bool.true Bool.false 535540248 Bool.true Bool.false 617317121 

noncomputable def Ns552p802 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 950659 1000 796 551 536870912 268435456 9007199254740992 Bool.false 1025471168731 4527 

noncomputable def Ns552p803 := Ns552p802 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 536870824 4592 Bool.false 423292102 Bool.false 93668830 28296951008113761 1 Bool.false 378467415 Bool.false Bool.false 93194333 Bool.false Bool.false 858293474 

noncomputable def Ns552p804 := nat_lit 228593985996628284640321509722117265365546431359261367665157 

noncomputable def Ns552p805 := nat_lit 119677144986420863761694818951282950745531863684612096000 

noncomputable def Ns552p806 := nat_lit 372705122750006611254737371503520000 

noncomputable def Ns552p807 := nat_lit 2125893150165240963675025279955884918080 

noncomputable abbrev qz654 := (@Eq.refl Real qz767)

noncomputable abbrev qz447 := qz654

noncomputable abbrev qz119 := qz447

noncomputable def Ns552p808 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 950659 1000 3615011137124 16000000 1901318 4000 2000 Ns552p806 Ns552p807 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p809 := nat_lit 73150075518921051084902883111077524916974858034963637652850240 

noncomputable abbrev qz655 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1901318))))

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 950659 4000) (Real.log (Enclosure.sfrac Bool.false 3615011137124 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz655))

noncomputable abbrev qz656 := (Enclosure.sfrac Bool.false 950659 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz448 qz656) (@HMul.hMul Real Real Real qz355 qz656 (Real.log Real.pi)))

noncomputable def Ns552p810 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns552p806 Ns552p807) 34409105757405476862453 18014398509481984000 132724453519383607093 Ns552p244 Ns552p806 Ns552p807 0 1 Ns552p809 

noncomputable def Ns552p811 := nat_lit 2309155998635341139617505083392000 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz359 qz448 qz656)

noncomputable def Ns552p812 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz656 (Real.log Real.pi)) 44211170218415513450997 18014398509481984000 11983253031396583 3844000000000000000000 36515535641499 67108864000 2851977 536870912000 Ns552p811 34409105757405476862453 18014398509481984000 

noncomputable def Ns552p813 := nat_lit 3536893617473241076079760 

noncomputable abbrev qz122 := qz448

noncomputable def Ns552p814 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz656 2110957810189133206589 720575940379279360 11983253031396583 3844000000000000000000 950659 2000 0 1 Ns552p813 44211170218415513450997 18014398509481984000 11983253031396583 3844000000000000000000 

noncomputable def Ns552p815 := nat_lit 4753454403681309266745683719405699072 

noncomputable def Ns552p816 := nat_lit 119229262225960498049843200 

noncomputable def Ns552p817 := nat_lit 79811879129545444383852773957466808956408077662280785701994400637976770635372844678098133453790629139161751013691223634811615467503266266235149929461985359160658129535648751268816486400 

noncomputable def Ns552p818 := nat_lit 1962317119138748666782418578467953409862742695451943832760919559744799420637303038891929937051528276909268439422072952755888993384192059923903576432931014303869162416109531267166371840 

noncomputable def Ns552p819 := nat_lit 46559511639631525364391966359794030651532559502365861675475569947263184688779574867496529405626690319058104878696676065027031442573980907797132528397928840647504384359147765760 

noncomputable def Ns552p820 := BSN.log_dyadic_bound 1517859137124 5712163137124 8 7 Ns552p817 268435456 76880000 Ns552p818 Ns552p819 146167052 7230022274248 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1517859137124) (BSN.artanhQ 5712163137124) 0 7 Ns552p818 Ns552p817 Ns552p819 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz449 := (Real.log (Enclosure.sfrac Bool.false 3615011137124 16000000))

noncomputable def Ns552p821 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 950659 4000) qz449 950659 4000 0 1 55520451732892775 4503599627370496 12500016337 961000000000000000 2111240684957604503549 720575940379279360 11883253030916083 3844000000000000000000 (Enclosure.Real.IsNear.const Bool.false 950659 4000) (BSN.isNear_log_sfrac 3615011137124 16000000 55520451732892775 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3615011137124) qz362)) Bool.false Ns552p816 Ns552p114 1000001306960000 76880000000000000000000 55520451732892775 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3615011137124 16000000 17 7230022274248 4194304000000 146167052 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p820 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p822 := BSN.arctan_dyadic_bound_f 1000 1901318 1 0 33554432 9610000 0 1 1 0 1 1 17647 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1901318) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1901318) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p823 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1901318))) 884279719003555 562949953421312 1 2000000000000000 17647 33554432 1 9610000 29661569322455868112896 883983651472803 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p822 rfl) rfl rfl 

noncomputable abbrev qz450 := (@HMul.hMul Real Real Real qz584 qz589 qz655)

noncomputable abbrev qz123 := qz450

noncomputable abbrev qz451 := qz655

noncomputable abbrev qz124 := qz451

noncomputable def Ns552p824 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 950659 4000) qz449) qz123 2111240684957604503549 720575940379279360 11883253030916083 3844000000000000000000 883983651472803 2251799813685248 200000000961 7688000000000000000 Ns552p815 2110957810189133206589 720575940379279360 11983253031396583 3844000000000000000000 (Ns552p821 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz124 1 4 0 1 883983651472803 562949953421312 200000000961 1922000000000000000 883983651472803 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p823 rfl) 

noncomputable def Ns552p825 := @Ns552p810 Ns552p804 Ns552p805 132724453519383607093 Ns552p244 (@Ns552p812 132724453519383607093 Ns552p244 (Ns552p814 (Ns552p824 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 950659 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz656 (Real.log Real.pi) 950659 2000 0 1 38410761 33554432 3 268435456 36515535641499 67108864000 2851977 536870912000 (Enclosure.Real.IsNear.const Bool.false 950659 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p806 Ns552p807) 

noncomputable def Ns552p826 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns552p804 Ns552p805 132724453519383607093 Ns552p244 128183896091 67108864 567 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz370 qz120 (Enclosure.sfrac Bool.true Ns552p806 Ns552p807)) Bool.false Ns552p804 Ns552p805 132724453519383607093 Ns552p244 Ns552p808 (Ns552p825 rfl rfl)) 

noncomputable def Ns552p827 := BSN.cos_dyadic_bound_f 77615187 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108853 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 77615187) qz595 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 77615187) qz596 0 0 rfl) rfl rfl 

noncomputable def Ns552p828 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 128183896091) qz380) Bool.false 128183896091 67108864 567 67108864 Bool.false 67108853 67108864 1 9610000 (Ns552p826 rfl) (Enclosure.sfrac_false_div 128183896091 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 128183896091) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 5461683281185506066432) qz394) 226375608064910080 72057594037927936 Bool.false 67108853 67108864 304 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q0 128183896091 67108864 226375608064910080 72057594037927936 304 5461683281185506066432 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108853 67108864 5461683281185506066432 Ns552p114 77615187 137438953472 19238770 19220000 (Ns552p827 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p829 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns552p804 Ns552p805 132724453519383607093 Ns552p244 1025471168731 536870912 4527 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz370 qz120 (Enclosure.sfrac Bool.true Ns552p806 Ns552p807)) Bool.false Ns552p804 Ns552p805 132724453519383607093 Ns552p244 Ns552p808 (Ns552p825 rfl rfl)) 

noncomputable def Ns552p830 := Ns552p803 78809 BSN.abs_quadSignPos (BSN.cos_quad_nat0 796 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 378467415 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 551 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 93194333 536870912) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 67108853 67108864 344748679 40307261440000 536870824 536870912 4592 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 67108853 67108864 344748679 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 67108853 67108864 5515978864 644916183040000 67108853 67108864 344748679 40307261440000 (Ns552p828 rfl rfl) rfl)) rfl) (Ns552p829 rfl) RS553to564.d7 

noncomputable def Ns552p831 := nat_lit 4481767533193841171183933950060745116317986466513369222000457162566574336 

noncomputable def Ns552p832 := nat_lit 1030674003590323541958393476018796436321329959995256111322832521830656 

noncomputable def Ns552p833 := nat_lit 13443241251574342866467885063230197756081316739620117153778725822656061696 

noncomputable def Ns552p834 := BSN.cos_dyadic_bound_f 423292102 536870912 3 2 536870912 268435456 Ns552p831 Ns552p140 Ns552p832 Ns552p833 Ns552p143 Ns552p832 378467415 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 423292102) qz373 0 2 Ns552p831 Ns552p140 Ns552p832 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 423292102) qz374 0 2 Ns552p833 Ns552p143 Ns552p832 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p835 := nat_lit 76980438796293068572775047210000 

noncomputable def Ns552p836 := BSN.sin_dyadic_bound_f 93668830 536870912 2 1 536870912 268435456 Ns552p835 Ns552p283 Ns552p835 Ns552p835 Ns552p284 Ns552p835 93194333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 93668830) qz371 0 1 Ns552p835 Ns552p283 Ns552p835 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 93668830) qz372 0 1 Ns552p835 Ns552p284 Ns552p835 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p837 := BSN.sin_dyadic_bound_f 2950950 536870912 1 0 536870912 268435456 0 1 1 0 1 1 2950935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2950950) qz371 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 2950950) qz372 0 0 rfl) rfl rfl 

noncomputable def Ns552p838 := nat_lit 151030362876565024170179725644654090955762624147994847491132559999053291053601023111911961957934620267583562145281 

noncomputable def Ns552p839 := nat_lit 74616768970647457555637540836305508657620069664147755422523478046406489825130893576189886841735321412001281 

noncomputable def Ns552p840 := nat_lit 754370534609344383652696640502252925917017223322811917346865304270841576130363581377469034959290347409708878487041 

noncomputable def Ns552p841 := BSN.sin_dyadic_bound_f 805507713 536870912 4 3 536870912 268435456 Ns552p838 Ns552p177 Ns552p839 Ns552p840 Ns552p180 Ns552p839 535540248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 805507713) qz371 0 3 Ns552p838 Ns552p177 Ns552p839 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 805507713) qz372 0 3 Ns552p840 Ns552p180 Ns552p839 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p842 := Ns552p801 133544 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 377 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 2950935 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535540248 536870912) qz119 rfl rfl (Ns552p830 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p834 rfl rfl) (Ns552p836 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p829 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p837 rfl rfl) (Ns552p841 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p843 := nat_lit 17904189005847666524523560488237863830435205390916967126126528638996046080 

noncomputable def Ns552p844 := nat_lit 5076220066382318886006887927329904677967626461444019193717808393216256 

noncomputable def Ns552p845 := nat_lit 46883704944731650476508171079216823519756447485749718823065365221876818176 

noncomputable def Ns552p846 := BSN.sin_dyadic_bound_f 516645386 536870912 3 2 536870912 268435456 Ns552p843 Ns552p130 Ns552p844 Ns552p845 Ns552p133 Ns552p844 440515437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 516645386) qz371 0 2 Ns552p843 Ns552p130 Ns552p844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 516645386) qz372 0 2 Ns552p845 Ns552p133 Ns552p844 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p847 := nat_lit 734433013182972202470630020869811170271444845782721051950932577060823296 

noncomputable def Ns552p848 := nat_lit 27688158785491568273543590379149132434708663621597395708971073577216 

noncomputable def Ns552p849 := nat_lit 2203243663231345624275342975428675212549465120020919961061379789035315456 

noncomputable def Ns552p850 := BSN.cos_dyadic_bound_f 269331258 536870912 3 2 536870912 268435456 Ns552p847 Ns552p140 Ns552p848 Ns552p849 Ns552p143 Ns552p848 470718424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 269331258) qz373 0 2 Ns552p847 Ns552p140 Ns552p848 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 269331258) qz374 0 2 Ns552p849 Ns552p143 Ns552p848 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p851 := Ns552p799 179726 BSN.abs_quadSignPos (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 440515437 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 470718424 536870912) qz119 rfl rfl (Ns552p842 rfl rfl) (Ns552p829 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p846 rfl rfl) (Ns552p850 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p852 := nat_lit 4237402281331417220852972889445815166002635868006147364786937781241147201 

noncomputable def Ns552p853 := nat_lit 921367631063206673864184268050517624032864374663086961009885104729921 

noncomputable def Ns552p854 := nat_lit 12710364108732125249211190299801344462759841875269115920438793573513981761 

noncomputable def Ns552p855 := BSN.cos_dyadic_bound_f 417401609 536870912 3 2 536870912 268435456 Ns552p852 Ns552p140 Ns552p853 Ns552p854 Ns552p143 Ns552p853 382622422 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 417401609) qz373 0 2 Ns552p852 Ns552p140 Ns552p853 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 417401609) qz374 0 2 Ns552p854 Ns552p143 Ns552p853 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p856 := nat_lit 66485400883927991853086832181674115375592736320750459836178533337793510578342605602495883932616687574738534400000 

noncomputable def Ns552p857 := nat_lit 6383265003633192209254319769570151478243889605540668558376554075649741246670511792956176142336000000000000 

noncomputable def Ns552p858 := nat_lit 332275351286120890392385832079937380473006968612378060265162462256003337524239331284100699992211946396188672000000 

noncomputable def Ns552p859 := BSN.sin_dyadic_bound_f 656276580 536870912 4 3 536870912 268435456 Ns552p856 Ns552p177 Ns552p857 Ns552p858 Ns552p180 Ns552p857 504618363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 656276580) qz371 0 3 Ns552p856 Ns552p177 Ns552p857 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 656276580) qz372 0 3 Ns552p858 Ns552p180 Ns552p857 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p860 := Ns552p797 220076 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 382622422 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 504618363 536870912) qz119 rfl rfl (Ns552p851 rfl) (Ns552p829 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p855 rfl rfl) (Ns552p859 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p861 := nat_lit 11071462639009653611654322222309306033182031892059019515101998643578036480 

noncomputable def Ns552p862 := nat_lit 1941489745404990489119162577023247013745586143709349617984488900813056 

noncomputable def Ns552p863 := nat_lit 28993544499723198998302746223780621020311638292112378830647545370198302976 

noncomputable def Ns552p864 := BSN.sin_dyadic_bound_f 458159702 536870912 3 2 536870912 268435456 Ns552p861 Ns552p130 Ns552p862 Ns552p863 Ns552p133 Ns552p862 404539068 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 458159702) qz371 0 2 Ns552p861 Ns552p130 Ns552p862 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 458159702) qz372 0 2 Ns552p863 Ns552p133 Ns552p862 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p865 := nat_lit 1314753929869914278833493033291776 

noncomputable def Ns552p866 := BSN.sin_dyadic_bound_f 190419368 536870912 2 1 536870912 268435456 Ns552p865 Ns552p283 Ns552p865 Ns552p865 Ns552p284 Ns552p865 186451929 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 190419368) qz371 0 1 Ns552p865 Ns552p283 Ns552p865 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 190419368) qz372 0 1 Ns552p865 Ns552p284 Ns552p865 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p867 := Ns552p795 256366 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 404539068 536870912) BSN.abs_quadSignPos qz598 (BSN.sfrac_eq_quadSignPos_mul Bool.false 186451929 536870912) qz119 rfl rfl (Ns552p860 rfl) (Ns552p829 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p864 rfl rfl) (Ns552p866 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p868 := nat_lit 111660880450506334232296976484485242236981123900623271286789153666402354654392327746982041142344499927584934400000 

noncomputable def Ns552p869 := nat_lit 30193585258208492846002596580765764092698330569760359593206820888971567882737794713404706380961000000000000 

noncomputable def Ns552p870 := nat_lit 557877020920935941896761828343783844827772906381797070833024463041367874571546374226708957112675702812420672000000 

noncomputable def Ns552p871 := BSN.sin_dyadic_bound_f 747009670 536870912 4 3 536870912 268435456 Ns552p868 Ns552p177 Ns552p869 Ns552p870 Ns552p180 Ns552p869 528256322 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 747009670) qz371 0 3 Ns552p868 Ns552p177 Ns552p869 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 747009670) qz372 0 3 Ns552p870 Ns552p180 Ns552p869 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p872 := Ns552p793 Bool.false 244049250 256366 Bool.true 747009670 28296951008113761 1 Bool.false 528256322 Bool.false Bool.false 396543719 273326 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 528256322 536870912) qz119 rfl (Ns552p867 rfl) (Ns552p829 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p871 rfl rfl) rfl 

noncomputable def Ns552p873 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) 396543719 536870912 273326 536870912 396543719 536870912 273326 536870912 425785576134803456 396543719 268435456 136663 134217728 (Ns552p872 rfl rfl rfl rfl) 

noncomputable def Ns552p874 := @Enclosure.Real.IsNear.mulLit_ff qz653 (Zeta.RiemannSiegel.correction qz118) 2391821 8388608 1 33554432 1025899477781783 2251799813685248 34208327340654357 1352487263094702080000 2453767914847501996843 18889465931478580854784 

noncomputable abbrev qz657 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns552p875 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz657 1 1 0 1 2391821 8388608 1 33554432 2391821 8388608 1 33554432 

noncomputable def Ns552p876 := @Enclosure.Real.IsNear.sqrt_image qz117 10153710235913 67108864000 950659 67108864000 412735961 412736001 33554432 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 10153710235913 67108864000 950659 67108864000 (BSN.t_div_two_pi_mk qz116 950659 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 950659 1000 0 1 10680707 67108864 1 67108864 10153710235913 67108864000 950659 67108864000 (Enclosure.Real.IsNear.const Bool.false 950659 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz770 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 950659 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz658 := qz770

noncomputable abbrev qz452 := qz658

noncomputable abbrev qz125 := qz452

noncomputable def Ns552p877 := @Enclosure.Real.IsNear.sqrt_image qz125 412735981 33554432 5 8388608 117682287 117682293 33554432 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 825471962 67108864 40 67108864 412735981 33554432 5 8388608 (Ns552p876 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p878 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 58841145 16777216 3 33554432 9567283 9567285 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 235364580 67108864 6 67108864 58841145 16777216 3 33554432 (Ns552p877 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p879 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 19134568 67108864 2 67108864 2391821 8388608 1 33554432 (Ns552p878 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz453 := (@HMul.hMul Real Real Real qz584 qz582 qz652)

noncomputable abbrev qz126 := (Real.cos qz453)

noncomputable abbrev qz659 := (@HMul.hMul Real Real Real qz742 qz769 qz769)

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz659 qz652) qz603)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz454))

noncomputable def Ns552p880 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 1025899477781783 

noncomputable def Ns552p881 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz126) qz127 215128243 67108864 2673 

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.cos qz453))

noncomputable def Ns552p882 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz126) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz128)) Bool.true 215128243 67108864 2673 67108864 (BSN.inv_eq_neg_inv_neg qz126) 

noncomputable def Ns552p883 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 215128243 67108864 2673 67108864 215128243 67108864 

noncomputable def Ns552p884 := @Enclosure.Real.IsNear.recentre' qz126 Bool.true 10467244 33554432 2498438864 644916183040000 2616811 8388608 156152429 40307261440000 

noncomputable abbrev qz129 := qz453

noncomputable def Ns552p885 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 126704163) qz380) Bool.false 126704163 67108864 253 67108864 Bool.true 10467244 33554432 1 

noncomputable def Ns552p886 := nat_lit 134930377066872868959448291 

noncomputable def Ns552p887 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 10082797 33554432 5 8388608 8916012897929887343335 4722366482869645213696 Ns552p886 

noncomputable def Ns552p888 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 412735981 33554432 5 8388608 12 1 0 1 10082797 10082797 33554432 5 

noncomputable def Ns552p889 := @Ns552p888 8388608 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 825471962 67108864 40 67108864 412735981 33554432 5 8388608 (Ns552p876 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p890 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 8916012897929887343335 4722366482869645213696 Ns552p886 Ns552p495 126704163 67108864 253 67108864 (@Ns552p887 Ns552p495 RS553to564.d55 (Ns552p889 rfl rfl) rfl) 

noncomputable def Ns552p891 := nat_lit 2132084243196516184633272541166570488663828824125337066651940459287767346411783876682290577653398914161 

noncomputable def Ns552p892 := nat_lit 17119481692849153645929244829586604066442759577621419939639363276871110035042979462631612429780081 

noncomputable def Ns552p893 := nat_lit 12869825235823848269986932432713159308107780834158013055432894537305017428228843053868538377418020897905 

noncomputable def Ns552p894 := BSN.cos_dyadic_bound_t 126704163 67108864 4 3 33554432 9610000 Ns552p891 Ns552p203 Ns552p892 Ns552p893 Ns552p206 Ns552p892 10467244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 126704163) qz604 0 3 Ns552p891 Ns552p203 Ns552p892 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 126704163) (BSN.cosOddQ 67108864) 0 3 Ns552p893 Ns552p206 Ns552p892 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p895 := @Enclosure.Real.IsNear.inv_image qz128 2616811 8388608 156152429 40307261440000 107562785 107565458 33554432 (@Enclosure.Real.IsNear.neg qz126 Bool.true 2616811 8388608 156152429 40307261440000 (Ns552p884 (@Ns552p885 9610000 (Ns552p890 rfl) (Enclosure.sfrac_false_div 126704163 67108864) (Ns552p894 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns552p896 := Ns552p882 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz128) Bool.false 215128243 67108864 2673 67108864 (@Ns552p883 2673 67108864 (Ns552p895 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p897 := @Enclosure.Real.IsNear.recentre' qz127 Bool.true 4768781 33554432 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz355 qz352 qz454)

noncomputable def Ns552p898 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 114984321)) qz380) Bool.true 114984321 67108864 

noncomputable def Ns552p899 := nat_lit 271499053723560340195846398245 

noncomputable def Ns552p900 := nat_lit 3624233031162956659611996837935621 

noncomputable def Ns552p901 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns552p899 Ns552p213 Ns552p900 

noncomputable abbrev qz131 := qz454

noncomputable def Ns552p902 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 307028475140759 

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz588 qz659 qz652)

noncomputable abbrev qz132 := qz455

noncomputable def Ns552p903 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 236659730963095 1125899906842624 134300115 140737488355328 1 16 

noncomputable abbrev qz456 := qz659

noncomputable abbrev qz133 := qz456

noncomputable def Ns552p904 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 101662795343209 1125899906842624 50414035 140737488355328 10082797 33554432 5 8388608 

noncomputable def Ns552p905 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 10082797 33554432 5 8388608 10082797 33554432 5 8388608 101662795343209 1125899906842624 

noncomputable def Ns552p906 := nat_lit 1442590960122560571083802680628229768164410327465836531877625808419614879885784239190373245156376363521 

noncomputable def Ns552p907 := nat_lit 5341503284983943884347943529482973859710786519357236695958358505495642322742391741641217033290241 

noncomputable def Ns552p908 := nat_lit 8721912856067440028706173887850683352309379984727016978838227868849039563235216933574837313532330689025 

noncomputable def Ns552p909 := BSN.cos_dyadic_bound_t 114984321 67108864 4 3 33554432 9610000 Ns552p906 Ns552p203 Ns552p907 Ns552p908 Ns552p206 Ns552p907 4768781 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 114984321) qz604 0 3 Ns552p906 Ns552p203 Ns552p907 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 114984321) (BSN.cosOddQ 67108864) 0 3 Ns552p908 Ns552p206 Ns552p907 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p910 := @Ns552p897 987387216 161229045760000 4768781 33554432 61711701 10076815360000 (@Ns552p898 101 16777216 Bool.true 4768781 33554432 1 9610000 (@Ns552p901 Ns552p216 114984321 67108864 101 16777216 (@Ns552p902 1125899906842624 134300115 140737488355328 Ns552p899 Ns552p213 Ns552p900 Ns552p216 RS553to564.d55 (@Ns552p903 0 1 4912455602252144 307028475140759 1125899906842624 134300115 140737488355328 (@Ns552p904 7940982849739465687040 236659730963095 1125899906842624 134300115 140737488355328 (@Ns552p905 50414035 140737488355328 (Ns552p889 rfl rfl) (Ns552p889 rfl rfl) rfl) (Ns552p889 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 114984321 67108864) (BSN.cos_neg_of_bound 114984321 67108864 Bool.true 4768781 33554432 1 9610000 (Ns552p909 rfl rfl)) rfl rfl) 

noncomputable def Ns552p911 := @Ns552p874 1024678118484921885391 Ns552p790 (Ns552p875 qz33 (@Enclosure.Real.IsNear.of_eq qz657 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 2391821 8388608 1 33554432 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 950659 1000 qz119)) Ns552p879) rfl) (@Ns552p880 2251799813685248 34208327340654357 1352487263094702080000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 950659 1000 12 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 950659 1000 12 qz119 rfl rfl rfl))) (@Ns552p881 67108864 4768781 33554432 61711701 10076815360000 1025899477781783 2251799813685248 34208327340654357 1352487263094702080000 Ns552p896 (Ns552p910 rfl) rfl)) 

noncomputable def Ns552p912 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 25450515602722977295573 18889465931478580854784 145426995959353101853391 Ns552p790 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HMul.hMul Real Real Real qz5 qz653 (Zeta.RiemannSiegel.correction qz118))) Bool.false 25450515602722977295573 18889465931478580854784 145426995959353101853391 Ns552p790 (BSN.hardyZApproximantRS₀_eq qz116 12 (@BSN.floor_sqrt_eq_dec qz116 950659 1000 12 qz119 rfl rfl rfl)) (@Ns552p792 25450515602722977295573 18889465931478580854784 145426995959353101853391 Ns552p790 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12)) Bool.false 396543719 268435456 136663 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (Ns552p873 (Ns552p872 rfl rfl rfl rfl) rfl rfl)) (Ns552p911 rfl) rfl rfl)) 

theorem RS553to564.d64 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 25450515602722977295573 18889465931478580854784 145426995959353101853391 Ns552p790 := Ns552p912 

noncomputable def Ns552p913 := nat_lit 9311031157628566120522961 

noncomputable def Ns552p914 := nat_lit 21374559448617355961351752646656 

noncomputable abbrev qz771 := (Enclosure.sfrac Bool.false 951910 1000)

noncomputable abbrev qz660 := qz771

noncomputable abbrev qz457 := qz660

noncomputable abbrev qz134 := qz457

noncomputable abbrev qz772 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 951910 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz661 := qz772

noncomputable abbrev qz458 := qz661

noncomputable abbrev qz135 := qz458

noncomputable abbrev qz773 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 951910 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz662 := qz773

noncomputable abbrev qz459 := qz662

noncomputable abbrev qz136 := qz459

noncomputable abbrev qz663 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz135 qz9))

noncomputable def Ns552p915 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HMul.hMul Real Real Real qz5 qz663 (Zeta.RiemannSiegel.correction qz136)) 274290597 67108864 136843 134217728 9681998181218979058651 75557863725914323419136 57110430445150283850961 Ns552p527 Ns552p914 

noncomputable def Ns552p916 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin BSN.quadSignPos 11 12 951910 1000 287 536870912 268435456 9007199254740992 Bool.false 1027156927501 4533 1334074092 57 154981288 8 

noncomputable def Ns552p917 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 951910 1000 177 235 536870912 268435456 9007199254740992 Bool.false 1027156927501 4533 

noncomputable def Ns552p918 := Ns552p917 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 1188155826 220367 Bool.true 318875818 Bool.true 115148234 28296951008113761 1 Bool.false 300454951 Bool.true Bool.false 114267424 Bool.false Bool.true 1248715105 

noncomputable def Ns552p919 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 951910 1000 42 113 536870912 268435456 9007199254740992 Bool.false 1027156927501 4533 

noncomputable def Ns552p920 := Ns552p919 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 871534453 179964 Bool.true 128248825 Bool.true 446229871 28296951008113761 1 Bool.false 521625446 Bool.true Bool.false 396596774 Bool.true Bool.true 1188155826 

noncomputable def Ns552p921 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 951910 1000 132 38 536870912 268435456 9007199254740992 Bool.false 1027156927501 4533 

noncomputable def Ns552p922 := Ns552p921 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 1009413132 133721 Bool.false 155697940 Bool.false 648167149 28296951008113761 1 Bool.false 514451726 Bool.false Bool.false 190878671 Bool.true Bool.true 871534453 

noncomputable def Ns552p923 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 951910 1000 377 242 536870912 268435456 9007199254740992 Bool.false 1027156927501 4533 

noncomputable def Ns552p924 := Ns552p923 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 626205214 78914 Bool.false 757639079 Bool.false 567012086 28296951008113761 1 Bool.false 530049184 Bool.true Bool.false 264265961 Bool.true Bool.true 1009413132 

noncomputable def Ns552p925 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 951910 1000 797 552 536870912 268435456 9007199254740992 Bool.false 1027156927501 4533 

noncomputable def Ns552p926 := Ns552p925 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870608 4600 Bool.false 800200705 Bool.false 198256710 28296951008113761 1 Bool.false 535140671 Bool.true Bool.false 500678715 Bool.false Bool.true 626205214 

noncomputable def Ns552p927 := nat_lit 23078357424980173184713950325323877445888209376342773 

noncomputable def Ns552p928 := nat_lit 12062517874797878520481324388979357022368143769600 

noncomputable def Ns552p929 := nat_lit 1574502400000000000000000 

noncomputable def Ns552p930 := nat_lit 375163852473141555678877648000000000 

noncomputable def Ns552p931 := nat_lit 2142733612728498563712045024406080000000 

noncomputable abbrev qz664 := (@Eq.refl Real qz771)

noncomputable abbrev qz460 := qz664

noncomputable abbrev qz137 := qz460

noncomputable def Ns552p932 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 951910 1000 3624531592400 16000000 1903820 4000 2000 Ns552p930 Ns552p931 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p933 := nat_lit 7385074375993655419108464104103640782684227000429687360000000 

noncomputable abbrev qz665 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1903820))))

noncomputable abbrev qz461 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 951910 4000) (Real.log (Enclosure.sfrac Bool.false 3624531592400 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz665))

noncomputable abbrev qz666 := (Enclosure.sfrac Bool.false 951910 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz461 qz666) (@HMul.hMul Real Real Real qz355 qz666 (Real.log Real.pi)))

noncomputable def Ns552p934 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns552p930 Ns552p931) 3446567043126194614817 1801439850948198400 13289857050744166657 Ns552p929 Ns552p930 Ns552p931 0 1 Ns552p933 

noncomputable def Ns552p935 := nat_lit 23129519896403792924328643788800 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz359 qz461 qz666)

noncomputable def Ns552p936 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz666 (Real.log Real.pi)) 4428063371576255459873 1801439850948198400 1199889055183417 384400000000000000000 3656358750351 6710886400 285573 53687091200 Ns552p935 3446567043126194614817 1801439850948198400 

noncomputable def Ns552p937 := nat_lit 1771225348630502183949200 

noncomputable abbrev qz140 := qz461

noncomputable def Ns552p938 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz666 1057093535166861045869 360287970189639680 1199889055183417 384400000000000000000 951910 2000 0 1 Ns552p937 4428063371576255459873 1801439850948198400 1199889055183417 384400000000000000000 

noncomputable def Ns552p939 := nat_lit 2380363025536617857670819820456640512 

noncomputable def Ns552p940 := nat_lit 119254699277231826990530560 

noncomputable def Ns552p941 := nat_lit 81694502751468489485901183201002683064085415732926634128533744906791966900846089482970070905002163388002681091336691550324629193171170200494794490526040064000000000000000000000000000000 

noncomputable def Ns552p942 := nat_lit 2027959494674765739039268338037272718367369514022027449943006570104248562932256555042983523790610921836559675424958385872930106354968701789767743369012838400000000000000000000000000000 

noncomputable def Ns552p943 := nat_lit 50818941693614228027594231967622432544430825076900848336587425233025305357801391154111096535242101930872580974000305278328718047619980581056125337600000000000000000000000000000 

noncomputable def Ns552p944 := BSN.log_dyadic_bound 1527379592400 5721683592400 8 7 Ns552p941 268435456 76880000 Ns552p942 Ns552p943 146873072 7249063184800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1527379592400) (BSN.artanhQ 5721683592400) 0 7 Ns552p942 Ns552p941 Ns552p943 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz462 := (Real.log (Enclosure.sfrac Bool.false 3624531592400 16000000))

noncomputable def Ns552p945 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 951910 4000) qz462 951910 4000 0 1 55532296782933095 4503599627370496 12500016337 961000000000000000 1057234972612836849229 360287970189639680 1189889055135367 384400000000000000000 (Enclosure.Real.IsNear.const Bool.false 951910 4000) (BSN.isNear_log_sfrac 3624531592400 16000000 55532296782933095 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3624531592400) qz362)) Bool.false Ns552p940 Ns552p114 1000001306960000 76880000000000000000000 55532296782933095 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3624531592400 16000000 17 7249063184800 4194304000000 146873072 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p944 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p946 := BSN.arctan_dyadic_bound_f 1000 1903820 1 0 33554432 9610000 0 1 1 0 1 1 17624 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1903820) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1903820) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p947 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1903820))) 884279719003555 562949953421312 1 2000000000000000 17624 33554432 1 9610000 29661582270304796803072 883984037348771 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p946 rfl) rfl rfl 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz584 qz589 qz665)

noncomputable abbrev qz141 := qz463

noncomputable abbrev qz464 := qz665

noncomputable abbrev qz142 := qz464

noncomputable def Ns552p948 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 951910 4000) qz462) qz141 1057234972612836849229 360287970189639680 1189889055135367 384400000000000000000 883984037348771 2251799813685248 200000000961 7688000000000000000 Ns552p939 1057093535166861045869 360287970189639680 1199889055183417 384400000000000000000 (Ns552p945 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz142 1 4 0 1 883984037348771 562949953421312 200000000961 1922000000000000000 883984037348771 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p947 rfl) 

noncomputable def Ns552p949 := @Ns552p934 Ns552p927 Ns552p928 13289857050744166657 Ns552p929 (@Ns552p936 13289857050744166657 Ns552p929 (Ns552p938 (Ns552p948 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 951910 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz666 (Real.log Real.pi) 951910 2000 0 1 38410761 33554432 3 268435456 3656358750351 6710886400 285573 53687091200 (Enclosure.Real.IsNear.const Bool.false 951910 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p930 Ns552p931) 

noncomputable def Ns552p950 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns552p927 Ns552p928 13289857050744166657 Ns552p929 128394615937 67108864 71 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz370 qz138 (Enclosure.sfrac Bool.true Ns552p930 Ns552p931)) Bool.false Ns552p927 Ns552p928 13289857050744166657 Ns552p929 Ns552p932 (Ns552p949 rfl rfl)) 

noncomputable def Ns552p951 := nat_lit 15181582026341217441153024 

noncomputable def Ns552p952 := nat_lit 14341617362053507270904973237607646449556608732218849572373987629681164332367227649687267212970793514173351833830260726285708394590305172331921 

noncomputable def Ns552p953 := nat_lit 10168262716576554720062257593159163933570223832231647216510955351069850941150491730622170256451339569904403454199158960389473908367826321 

noncomputable def Ns552p954 := nat_lit 71619220013022287568300721039278541142503207669870710453587251187479551622193018467001468550088455854408406864182399003801296321397071943572881 

noncomputable def Ns552p955 := BSN.sin_dyadic_bound_f 215743256523 137438953472 4 3 67108864 19238770 Ns552p952 Ns552p566 Ns552p953 Ns552p954 Ns552p569 Ns552p953 67108826 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215743256523) qz635 0 3 Ns552p952 Ns552p566 Ns552p953 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215743256523) qz636 0 3 Ns552p954 Ns552p569 Ns552p953 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p956 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 128394615937) qz380) Bool.false 128394615937 67108864 71 8388608 Bool.true 67108826 67108864 1 9610000 (Ns552p950 rfl) (Enclosure.sfrac_false_div 128394615937 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 128394615937) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns552p951) qz394) 226375608064910080 72057594037927936 Bool.false 67108826 67108864 304 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q1 128394615937 67108864 226375608064910080 72057594037927936 304 Ns552p951 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108826 67108864 Ns552p951 Ns552p114 215743256523 137438953472 19238770 19220000 (Ns552p955 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p957 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns552p927 Ns552p928 13289857050744166657 Ns552p929 1027156927501 536870912 4533 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz370 qz138 (Enclosure.sfrac Bool.true Ns552p930 Ns552p931)) Bool.false Ns552p927 Ns552p928 13289857050744166657 Ns552p929 Ns552p932 (Ns552p949 rfl rfl)) 

noncomputable def Ns552p958 := Ns552p926 78914 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 797 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535140671 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 552 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 500678715 536870912) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 33554413 33554432 43168663 5038407680000 536870608 536870912 4600 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 33554413 33554432 43168663 5038407680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 67108826 67108864 690698608 80614522880000 33554413 33554432 43168663 5038407680000 (Ns552p956 rfl rfl) rfl)) rfl) (Ns552p957 rfl) RS553to564.d7 

noncomputable def Ns552p959 := nat_lit 147082905605856690094276127269284248387361902350088005996231863484370942458958179893811920428891447876341867290625 

noncomputable def Ns552p960 := nat_lit 68926647583351457905334743960829400206519448628663825056966330582740477777865028791879828288245918212890625 

noncomputable def Ns552p961 := nat_lit 734673497564591029006475716032053042143406216257831843720404878418518896165851304433320342687181256066132484890625 

noncomputable def Ns552p962 := BSN.sin_dyadic_bound_f 800200705 536870912 4 3 536870912 268435456 Ns552p959 Ns552p177 Ns552p960 Ns552p961 Ns552p180 Ns552p960 535140671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 800200705) qz371 0 3 Ns552p959 Ns552p177 Ns552p960 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 800200705) qz372 0 3 Ns552p961 Ns552p180 Ns552p960 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p963 := nat_lit 215628005515081487580508045528623734754793267203150231541484400688800000 

noncomputable def Ns552p964 := nat_lit 2386839187304534419889006322278664556695531074906474380256100000000 

noncomputable def Ns552p965 := nat_lit 646879242866869853672684358573226646935266410547300881675692689866400000 

noncomputable def Ns552p966 := BSN.cos_dyadic_bound_f 198256710 536870912 3 2 536870912 268435456 Ns552p963 Ns552p140 Ns552p964 Ns552p965 Ns552p143 Ns552p964 500678715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 198256710) qz373 0 2 Ns552p963 Ns552p140 Ns552p964 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 198256710) qz374 0 2 Ns552p965 Ns552p143 Ns552p964 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p967 := nat_lit 118161744963617363241625047633752647899355402279644125742576373672031169017662841098767358275585771512774775572641 

noncomputable def Ns552p968 := nat_lit 35772427290620876826292361508950728963085829875707089812097386924283692000760273951490446835984478019553441 

noncomputable def Ns552p969 := nat_lit 590330191883313878513114296313727520353242717633980162406993148403176045346650457038321006476004618621695766333601 

noncomputable def Ns552p970 := BSN.sin_dyadic_bound_f 757639079 536870912 4 3 536870912 268435456 Ns552p967 Ns552p177 Ns552p968 Ns552p969 Ns552p180 Ns552p968 530049184 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 757639079) qz371 0 3 Ns552p967 Ns552p177 Ns552p968 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 757639079) qz372 0 3 Ns552p969 Ns552p180 Ns552p968 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p971 := nat_lit 14248709474693935944510192993102291593408083157074438967556147449026274386331227855138294442588965821215880318976 

noncomputable def Ns552p972 := nat_lit 1104352689057810459267170382898318431553823123771702137841168426565984559353496222497003389248042927722496 

noncomputable def Ns552p973 := nat_lit 86399517741061430361384967044002849664728235288766066007804020680772131769347159495636335046963013984935020400640 

noncomputable def Ns552p974 := BSN.cos_dyadic_bound_f 567012086 536870912 4 3 536870912 268435456 Ns552p971 Ns552p151 Ns552p972 Ns552p973 Ns552p154 Ns552p972 264265961 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 567012086) qz373 0 3 Ns552p971 Ns552p151 Ns552p972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 567012086) qz374 0 3 Ns552p973 Ns552p154 Ns552p972 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p975 := Ns552p924 133721 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 377 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530049184 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 242 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 264265961 536870912) qz137 rfl rfl (Ns552p958 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p962 rfl rfl) (Ns552p966 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p957 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p970 rfl rfl) (Ns552p974 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p976 := nat_lit 82020436015935641452241890007931742700991548631477258174635258060800000 

noncomputable def Ns552p977 := nat_lit 345352761084584118836977831680830401102550605809242013721600000000 

noncomputable def Ns552p978 := nat_lit 246060617342284755188487996068131866442172440793220156039878330982400000 

noncomputable def Ns552p979 := BSN.cos_dyadic_bound_f 155697940 536870912 3 2 536870912 268435456 Ns552p976 Ns552p140 Ns552p977 Ns552p978 Ns552p143 Ns552p977 514451726 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 155697940) qz373 0 2 Ns552p976 Ns552p140 Ns552p977 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 155697940) qz374 0 2 Ns552p978 Ns552p143 Ns552p977 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p980 := nat_lit 24343428729848286009663833442820207781069835212424446180463454132336141302839529590764996631836210503524692127281 

noncomputable def Ns552p981 := nat_lit 5498499518103952890067771027793858964835616123161079244977409686339060976189705638747142648450412505329201 

noncomputable def Ns552p982 := nat_lit 147559088294142780238996357335747362145774108958406341752554261785423145668765328231814574705516910926699934117425 

noncomputable def Ns552p983 := BSN.cos_dyadic_bound_f 648167149 536870912 4 3 536870912 268435456 Ns552p980 Ns552p151 Ns552p981 Ns552p982 Ns552p154 Ns552p981 190878671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 648167149) qz373 0 3 Ns552p980 Ns552p151 Ns552p981 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 648167149) qz374 0 3 Ns552p982 Ns552p154 Ns552p981 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p984 := Ns552p922 179964 BSN.abs_quadSignPos (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 514451726 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 38 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 190878671 536870912) qz137 rfl rfl (Ns552p975 rfl rfl) (Ns552p957 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p979 rfl rfl) (Ns552p983 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p985 := nat_lit 270528845659283618030046750390625 

noncomputable def Ns552p986 := BSN.cos_dyadic_bound_f 128248825 536870912 2 1 536870912 268435456 Ns552p985 Ns552p157 Ns552p985 Ns552p985 Ns552p158 Ns552p985 521625446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 128248825) qz373 0 1 Ns552p985 Ns552p157 Ns552p985 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 128248825) qz374 0 1 Ns552p985 Ns552p158 Ns552p985 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p987 := nat_lit 9962409205640331956190482973258054329590295087727545197124509979400073345 

noncomputable def Ns552p988 := nat_lit 1572059978772539874919141017002690048630217035918703592274203652780161 

noncomputable def Ns552p989 := nat_lit 26089478870044761487368062511172137936467276306942559519986225044895690881 

noncomputable def Ns552p990 := BSN.sin_dyadic_bound_f 446229871 536870912 3 2 536870912 268435456 Ns552p987 Ns552p130 Ns552p988 Ns552p989 Ns552p133 Ns552p988 396596774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 446229871) qz371 0 2 Ns552p987 Ns552p130 Ns552p988 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 446229871) qz372 0 2 Ns552p989 Ns552p133 Ns552p988 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p991 := Ns552p920 220367 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 42 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 521625446 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 396596774 536870912) qz137 rfl rfl (Ns552p984 rfl) (Ns552p957 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p986 rfl rfl) (Ns552p990 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p992 := nat_lit 2597559472630595220896631589920263483899994025939875590111772820254122240 

noncomputable def Ns552p993 := nat_lit 106898764445591491509049428362764211348364448361129954455950010245376 

noncomputable def Ns552p994 := nat_lit 6802958877937694620885877607859531315776848906449946620842666800648970496 

noncomputable def Ns552p995 := BSN.sin_dyadic_bound_f 318875818 536870912 3 2 536870912 268435456 Ns552p992 Ns552p130 Ns552p993 Ns552p994 Ns552p133 Ns552p993 300454951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 318875818) qz371 0 2 Ns552p992 Ns552p130 Ns552p993 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 318875818) qz372 0 2 Ns552p994 Ns552p133 Ns552p993 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p996 := nat_lit 175804151620634864276528621387536 

noncomputable def Ns552p997 := BSN.sin_dyadic_bound_f 115148234 536870912 2 1 536870912 268435456 Ns552p996 Ns552p283 Ns552p996 Ns552p996 Ns552p284 Ns552p996 114267424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 115148234) qz371 0 1 Ns552p996 Ns552p283 Ns552p996 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 115148234) qz372 0 1 Ns552p996 Ns552p284 Ns552p996 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p998 := Ns552p918 256704 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 300454951 536870912) BSN.abs_quadSignPos qz598 (BSN.sfrac_eq_quadSignPos_mul Bool.false 114267424 536870912) qz137 rfl rfl (Ns552p991 rfl) (Ns552p957 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p995 rfl rfl) (Ns552p997 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p999 := nat_lit 101920907853878736658737882114895742350837653468652216367171980075772402106734804641095408152761913751994144210321 

noncomputable def Ns552p1000 := nat_lit 22968994864114177055115482225113012728009055518256588082897410361243672826781313077194350751520985434373521 

noncomputable def Ns552p1001 := nat_lit 509248397380234649097167791101165665982807723169419166415865897092364064299818520463513275936835428245395573652881 

noncomputable def Ns552p1002 := BSN.sin_dyadic_bound_f 730177589 536870912 4 3 536870912 268435456 Ns552p999 Ns552p177 Ns552p1000 Ns552p1001 Ns552p180 Ns552p1000 524993995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 730177589) qz371 0 3 Ns552p999 Ns552p177 Ns552p1000 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 730177589) qz372 0 3 Ns552p1001 Ns552p180 Ns552p1000 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1003 := Ns552p916 Bool.true 1248715105 256704 Bool.true 730177589 28296951008113761 1 Bool.false 524993995 Bool.false Bool.true 1097162388 273686 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 524993995 536870912) qz137 rfl (Ns552p998 rfl) (Ns552p957 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p1002 rfl rfl) rfl 

noncomputable def Ns552p1004 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) 1097162388 536870912 273686 536870912 1097162388 536870912 273686 536870912 1178069143715315712 274290597 67108864 136843 134217728 (Ns552p1003 rfl rfl rfl rfl) 

noncomputable def Ns552p1005 := @Enclosure.Real.IsNear.mulLit_ff qz663 (Zeta.RiemannSiegel.correction qz136) 9564139 33554432 1 33554432 1012323030982609 2251799813685248 29792968913594687 1352487263094702080000 9681998181218979058651 75557863725914323419136 

noncomputable abbrev qz667 := (@HPow.hPow Real Real Real qz7 qz135 qz9)

noncomputable def Ns552p1006 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz667 1 1 0 1 9564139 33554432 1 33554432 9564139 33554432 1 33554432 

noncomputable def Ns552p1007 := @Enclosure.Real.IsNear.sqrt_image qz135 1016707180037 6710886400 95191 6710886400 413007437 413007477 33554432 (@Enclosure.Real.IsNear.of_eq qz135 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 1016707180037 6710886400 95191 6710886400 (BSN.t_div_two_pi_mk qz134 951910 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 951910 1000 0 1 10680707 67108864 1 67108864 1016707180037 6710886400 95191 6710886400 (Enclosure.Real.IsNear.const Bool.false 951910 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz774 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 951910 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz668 := qz774

noncomputable abbrev qz465 := qz668

noncomputable abbrev qz143 := qz465

noncomputable def Ns552p1008 := @Enclosure.Real.IsNear.sqrt_image qz143 413007457 33554432 5 8388608 117720983 117720990 33554432 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 826014914 67108864 40 67108864 413007457 33554432 5 8388608 (Ns552p1007 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p1009 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 235441973 67108864 7 67108864 9564138 9564140 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 235441973 67108864 7 67108864 235441973 67108864 7 67108864 (Ns552p1008 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p1010 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 19128278 67108864 2 67108864 9564139 33554432 1 33554432 (Ns552p1009 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz466 := (@HMul.hMul Real Real Real qz584 qz582 qz662)

noncomputable abbrev qz144 := (Real.cos qz466)

noncomputable abbrev qz669 := (@HMul.hMul Real Real Real qz742 qz773 qz773)

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz669 qz662) qz603)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz467))

noncomputable def Ns552p1011 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 1012323030982609 

noncomputable def Ns552p1012 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 186505447 67108864 2009 

noncomputable abbrev qz146 := (@Neg.neg Real Real.instNeg (Real.cos qz466))

noncomputable def Ns552p1013 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz146)) Bool.true 186505447 67108864 2009 67108864 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns552p1014 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz146) Bool.false 186505447 67108864 2009 67108864 186505447 67108864 

noncomputable def Ns552p1015 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 12073641 33554432 2498438864 644916183040000 12073641 33554432 156152429 40307261440000 

noncomputable abbrev qz147 := qz466

noncomputable def Ns552p1016 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 130115631) qz380) Bool.false 130115631 67108864 253 67108864 Bool.true 12073641 33554432 1 

noncomputable def Ns552p1017 := nat_lit 134930377067455859230272739 

noncomputable def Ns552p1018 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 10354273 33554432 5 8388608 9156073618926096440515 4722366482869645213696 Ns552p1017 

noncomputable def Ns552p1019 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 413007457 33554432 5 8388608 12 1 0 1 10354273 10354273 33554432 5 

noncomputable def Ns552p1020 := @Ns552p1019 8388608 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 826014914 67108864 40 67108864 413007457 33554432 5 8388608 (Ns552p1007 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p1021 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 9156073618926096440515 4722366482869645213696 Ns552p1017 Ns552p495 130115631 67108864 253 67108864 (@Ns552p1018 Ns552p495 RS553to564.d55 (Ns552p1020 rfl rfl) rfl) 

noncomputable def Ns552p1022 := nat_lit 2373148628388397176977496708267247615885702204803248414352351431407852206824499487927886103761147080641 

noncomputable def Ns552p1023 := nat_lit 23547980433809882104234320522669932113980957732766491214545461877253467528786344699268903039872961 

noncomputable def Ns552p1024 := nat_lit 14316919593638694550806850459638620576315920371055042827518196888226582587361740751680814710781949718465 

noncomputable def Ns552p1025 := BSN.cos_dyadic_bound_t 130115631 67108864 4 3 33554432 9610000 Ns552p1022 Ns552p203 Ns552p1023 Ns552p1024 Ns552p206 Ns552p1023 12073641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 130115631) qz604 0 3 Ns552p1022 Ns552p203 Ns552p1023 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 130115631) (BSN.cosOddQ 67108864) 0 3 Ns552p1024 Ns552p206 Ns552p1023 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1026 := @Enclosure.Real.IsNear.inv_image qz146 12073641 33554432 156152429 40307261440000 93251719 93253728 33554432 (@Enclosure.Real.IsNear.neg qz144 Bool.true 12073641 33554432 156152429 40307261440000 (Ns552p1015 (@Ns552p1016 9610000 (Ns552p1021 rfl) (Enclosure.sfrac_false_div 130115631 67108864) (Ns552p1025 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns552p1027 := Ns552p1013 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz146) Bool.false 186505447 67108864 2009 67108864 (@Ns552p1014 2009 67108864 (Ns552p1026 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1028 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 5427847 33554432 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz355 qz352 qz467)

noncomputable def Ns552p1029 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 116317959)) qz380) Bool.true 116317959 67108864 

noncomputable def Ns552p1030 := nat_lit 274648017102848615551249637405 

noncomputable def Ns552p1031 := nat_lit 3660863390205508513244375251795169 

noncomputable def Ns552p1032 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns552p1030 Ns552p213 Ns552p1031 

noncomputable abbrev qz149 := qz467

noncomputable def Ns552p1033 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 310589524107071 

noncomputable abbrev qz468 := (@HSub.hSub Real Real Real qz588 qz669 qz662)

noncomputable abbrev qz150 := qz468

noncomputable def Ns552p1034 := @Enclosure.Real.IsNear.subLit_tf qz150 qz31 240220779929407 1125899906842624 135657495 140737488355328 1 16 

noncomputable abbrev qz469 := qz669

noncomputable abbrev qz151 := qz469

noncomputable def Ns552p1035 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz136 107210969358529 1125899906842624 51771415 140737488355328 10354273 33554432 5 8388608 

noncomputable def Ns552p1036 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 10354273 33554432 5 8388608 10354273 33554432 5 8388608 107210969358529 1125899906842624 

noncomputable def Ns552p1037 := nat_lit 1511056073495847528271962896644311490842669455936603816218460688805022395465388543718011492762012464161 

noncomputable def Ns552p1038 := nat_lit 6134247260034599673677709143907728845527937000833426070759513596003205035949817050205758227330081 

noncomputable def Ns552p1039 := nat_lit 9134385976560808585386746343588397209793069566898316053296608004074915447595634106069561108022519247905 

noncomputable def Ns552p1040 := BSN.cos_dyadic_bound_t 116317959 67108864 4 3 33554432 9610000 Ns552p1037 Ns552p203 Ns552p1038 Ns552p1039 Ns552p206 Ns552p1038 5427847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 116317959) qz604 0 3 Ns552p1037 Ns552p203 Ns552p1038 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 116317959) (BSN.cosOddQ 67108864) 0 3 Ns552p1039 Ns552p206 Ns552p1038 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1041 := @Ns552p1028 498498608 80614522880000 5427847 33554432 31156163 5038407680000 (@Ns552p1029 51 8388608 Bool.true 5427847 33554432 1 9610000 (@Ns552p1032 Ns552p216 116317959 67108864 51 8388608 (@Ns552p1033 1125899906842624 135657495 140737488355328 Ns552p1030 Ns552p213 Ns552p1031 Ns552p216 RS553to564.d55 (@Ns552p1034 0 1 4969432385713136 310589524107071 1125899906842624 135657495 140737488355328 (@Ns552p1035 8060471825128251981824 240220779929407 1125899906842624 135657495 140737488355328 (@Ns552p1036 51771415 140737488355328 (Ns552p1020 rfl rfl) (Ns552p1020 rfl rfl) rfl) (Ns552p1020 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 116317959 67108864) (BSN.cos_neg_of_bound 116317959 67108864 Bool.true 5427847 33554432 1 9610000 (Ns552p1040 rfl rfl)) rfl rfl) 

noncomputable def Ns552p1042 := @Ns552p1005 57110430445150283850961 Ns552p527 (Ns552p1006 qz33 (@Enclosure.Real.IsNear.of_eq qz667 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 9564139 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz135 (BSN.t_div_two_pi_nonneg qz134 951910 1000 qz137)) Ns552p1010) rfl) (@Ns552p1011 2251799813685248 29792968913594687 1352487263094702080000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 951910 1000 12 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 951910 1000 12 qz137 rfl rfl rfl))) (@Ns552p1012 67108864 5427847 33554432 31156163 5038407680000 1012323030982609 2251799813685248 29792968913594687 1352487263094702080000 Ns552p1027 (Ns552p1041 rfl) rfl)) 

noncomputable def Ns552p1043 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 318505755791326701065179 75557863725914323419136 Ns552p913 Ns552p527 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HMul.hMul Real Real Real qz5 qz663 (Zeta.RiemannSiegel.correction qz136))) Bool.true 318505755791326701065179 75557863725914323419136 Ns552p913 Ns552p527 (BSN.hardyZApproximantRS₀_eq qz134 12 (@BSN.floor_sqrt_eq_dec qz134 951910 1000 12 qz137 rfl rfl rfl)) (@Ns552p915 318505755791326701065179 75557863725914323419136 Ns552p913 Ns552p527 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12)) Bool.true 274290597 67108864 136843 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (Ns552p1004 (Ns552p1003 rfl rfl rfl rfl) rfl rfl)) (Ns552p1042 rfl) rfl rfl)) 

theorem RS553to564.d65 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 318505755791326701065179 75557863725914323419136 Ns552p913 Ns552p527 := Ns552p1043 

noncomputable def Ns552p1044 := nat_lit 226909709501886452518092800 

noncomputable def Ns552p1045 := nat_lit 11539128347921349306244518641664 

noncomputable abbrev qz775 := (Enclosure.sfrac Bool.false 953162 1000)

noncomputable abbrev qz670 := qz775

noncomputable abbrev qz470 := qz670

noncomputable abbrev qz152 := qz470

noncomputable abbrev qz776 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 953162 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz671 := qz776

noncomputable abbrev qz471 := qz671

noncomputable abbrev qz153 := qz471

noncomputable abbrev qz777 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 953162 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz672 := qz777

noncomputable abbrev qz472 := qz672

noncomputable abbrev qz154 := qz472

noncomputable abbrev qz673 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns552p1046 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HMul.hMul Real Real Real qz5 qz673 (Zeta.RiemannSiegel.correction qz154)) 644823159 268435456 34255 33554432 2388793028285901030057 18889465931478580854784 1267753663315353940853 Ns552p1044 Ns552p1045 

noncomputable def Ns552p1047 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin BSN.quadSignPos 11 12 953162 1000 287 536870912 268435456 9007199254740992 Bool.false 1028844475172 4539 1334074092 57 154981288 8 

noncomputable def Ns552p1048 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 9 10 11 953162 1000 177 235 536870912 268435456 9007199254740992 Bool.false 1028844475172 4539 

noncomputable def Ns552p1049 := Ns552p1048 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.false 538104712 220651 Bool.true 179039224 Bool.true 39375558 28296951008113761 1 Bool.false 175739038 Bool.true Bool.false 39340266 Bool.false Bool.false 494392682 

noncomputable def Ns552p1050 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 953162 1000 41 113 536870912 268435456 9007199254740992 Bool.false 1028844475172 4539 

noncomputable def Ns552p1051 := Ns552p1050 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.false 795414598 180195 Bool.true 681738389 Bool.true 235573887 28296951008113761 1 Bool.false 512739885 Bool.true Bool.false 228086873 Bool.true Bool.false 538104712 

noncomputable def Ns552p1052 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 953162 1000 132 39 536870912 268435456 9007199254740992 Bool.false 1028844475172 4539 

noncomputable def Ns552p1053 := Ns552p1052 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.false 645615625 133891 Bool.false 638892308 Bool.false 184432382 28296951008113761 1 Bool.false 199518592 Bool.false Bool.false 180826117 Bool.false Bool.false 795414598 

noncomputable def Ns552p1054 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 953162 1000 378 243 536870912 268435456 9007199254740992 Bool.false 1028844475172 4539 

noncomputable def Ns552p1055 := Ns552p1054 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 592491612 79012 Bool.false 670056991 Bool.false 329441300 28296951008113761 1 Bool.false 170266110 Bool.true Bool.false 309152192 Bool.false Bool.false 645615625 

noncomputable def Ns552p1056 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 953162 1000 799 553 536870912 268435456 9007199254740992 Bool.false 1028844475172 4539 

noncomputable def Ns552p1057 := Ns552p1056 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 536870792 4600 Bool.false 335211222 Bool.false 304043679 28296951008113761 1 Bool.false 313851515 Bool.false Bool.false 288049945 Bool.true Bool.false 592491612 

noncomputable def Ns552p1058 := nat_lit 1820257540918296574033184927592448475348402937669981074983 

noncomputable def Ns552p1059 := nat_lit 949845530252164380847664081834215519174219549114368000 

noncomputable def Ns552p1060 := nat_lit 377637522238449839905059459599360000 

noncomputable def Ns552p1061 := nat_lit 2159698693167602825377944286251967057920 

noncomputable abbrev qz674 := (@Eq.refl Real qz775)

noncomputable abbrev qz473 := qz674

noncomputable abbrev qz155 := qz473

noncomputable def Ns552p1062 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 953162 1000 3634072192976 16000000 1906324 4000 2000 Ns552p1060 Ns552p1061 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p1063 := nat_lit 37278874438006713836199627317093344775135292163481212415651840 

noncomputable abbrev qz675 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1906324))))

noncomputable abbrev qz474 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 953162 4000) (Real.log (Enclosure.sfrac Bool.false 3634072192976 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz675))

noncomputable abbrev qz676 := (Enclosure.sfrac Bool.false 953162 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz474 qz676) (@HMul.hMul Real Real Real qz355 qz676 (Real.log Real.pi)))

noncomputable def Ns552p1064 := @Enclosure.Real.IsNear.addLit_ft_p qz156 (Enclosure.sfrac Bool.true Ns552p1060 Ns552p1061) 17261147565351656951427 9007199254740992000 66536413338872188387 Ns552p410 Ns552p1060 Ns552p1061 0 1 Ns552p1063 

noncomputable def Ns552p1065 := nat_lit 579188002223557729263984574464000 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz359 qz474 qz676)

noncomputable def Ns552p1066 := @Enclosure.Real.IsNear.subLit_ff_p qz157 (@HMul.hMul Real Real Real qz5 qz676 (Real.log Real.pi)) 22175083774752319278723 9007199254740992000 6007270286144047 1922000000000000000000 18305838888141 33554432000 1429743 268435456000 Ns552p1065 17261147565351656951427 9007199254740992000 

noncomputable def Ns552p1067 := nat_lit 1774006701980185542297840 

noncomputable abbrev qz158 := qz474

noncomputable def Ns552p1068 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz676 1058709752111041439483 360287970189639680 6007270286144047 1922000000000000000000 953162 2000 0 1 Ns552p1067 22175083774752319278723 9007199254740992000 6007270286144047 1922000000000000000000 

noncomputable def Ns552p1069 := nat_lit 2384002422550398208877657141001846784 

noncomputable def Ns552p1070 := nat_lit 119280123177992244009369600 

noncomputable def Ns552p1071 := nat_lit 83622407967322252210635983253518997491943787679882494451177441135707194029883784564854732793538999323203965193471209170345921603469419393526095766938111118253062015249697385025529446400 

noncomputable def Ns552p1072 := nat_lit 2095711990387438424101823642830093508066669088332129654208984461898786154677078856698615479210354618143784928819542767259451915092353216555761664257686271735525747927206437762986147840 

noncomputable def Ns552p1073 := nat_lit 55448050212880222416479572674774037738203486286780316695763132769641018717991863351024561009740915393446215972922046602710772987821532088718424092322162135978380083265808629760 

noncomputable def Ns552p1074 := BSN.log_dyadic_bound 1536920192976 5731224192976 8 7 Ns552p1071 268435456 76880000 Ns552p1072 Ns552p1073 147578727 7268144385952 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1536920192976) (BSN.artanhQ 5731224192976) 0 7 Ns552p1072 Ns552p1071 Ns552p1073 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz475 := (Real.log (Enclosure.sfrac Bool.false 3634072192976 16000000))

noncomputable def Ns552p1075 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 953162 4000) qz475 953162 4000 0 1 55544135709289575 4503599627370496 12500016337 961000000000000000 1058851189618757397723 360287970189639680 5957270285903797 1922000000000000000000 (Enclosure.Real.IsNear.const Bool.false 953162 4000) (BSN.isNear_log_sfrac 3634072192976 16000000 55544135709289575 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3634072192976) qz362)) Bool.false Ns552p1070 Ns552p114 1000001306960000 76880000000000000000000 55544135709289575 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3634072192976 16000000 17 7268144385952 4194304000000 147578727 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p1074 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1076 := BSN.arctan_dyadic_bound_f 1000 1906324 1 0 33554432 9610000 0 1 1 0 1 1 17601 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1906324) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1906324) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p1077 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1906324))) 884279719003555 562949953421312 1 2000000000000000 17601 33554432 1 9610000 29661595218153725493248 883984423224739 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p1076 rfl) rfl rfl 

noncomputable abbrev qz476 := (@HMul.hMul Real Real Real qz584 qz589 qz675)

noncomputable abbrev qz159 := qz476

noncomputable abbrev qz477 := qz675

noncomputable abbrev qz160 := qz477

noncomputable def Ns552p1078 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 953162 4000) qz475) qz159 1058851189618757397723 360287970189639680 5957270285903797 1922000000000000000000 883984423224739 2251799813685248 200000000961 7688000000000000000 Ns552p1069 1058709752111041439483 360287970189639680 6007270286144047 1922000000000000000000 (Ns552p1075 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz160 1 4 0 1 883984423224739 562949953421312 200000000961 1922000000000000000 883984423224739 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p1077 rfl) 

noncomputable def Ns552p1079 := @Ns552p1064 Ns552p1058 Ns552p1059 66536413338872188387 Ns552p410 (@Ns552p1066 66536413338872188387 Ns552p410 (Ns552p1068 (Ns552p1078 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 953162 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz676 (Real.log Real.pi) 953162 2000 0 1 38410761 33554432 3 268435456 18305838888141 33554432000 1429743 268435456000 (Enclosure.Real.IsNear.const Bool.false 953162 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p1060 Ns552p1061) 

noncomputable def Ns552p1080 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns552p1058 Ns552p1059 66536413338872188387 Ns552p410 32151389849 16777216 71 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz370 qz156 (Enclosure.sfrac Bool.true Ns552p1060 Ns552p1061)) Bool.false Ns552p1058 Ns552p1059 66536413338872188387 Ns552p410 Ns552p1062 (Ns552p1079 rfl rfl)) 

noncomputable def Ns552p1081 := nat_lit 2417851639229258349412352 

noncomputable def Ns552p1082 := BSN.cos_dyadic_bound_f 89650738 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108849 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 89650738) qz595 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 89650738) qz596 0 0 rfl) rfl rfl 

noncomputable abbrev qz677 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns552p1083 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 32151389849) qz677) Bool.false 32151389849 16777216 71 8388608 Bool.false 67108849 67108864 1 9610000 (Ns552p1080 rfl) (Enclosure.sfrac_false_div 32151389849 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 32151389849) qz677) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1577152465437068361728) (@Nat.cast Real Real.instNatCast Ns552p1081)) 226375608064910080 72057594037927936 Bool.false 67108849 67108864 305 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q0 32151389849 16777216 226375608064910080 72057594037927936 305 1577152465437068361728 Ns552p1081 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108849 67108864 1577152465437068361728 Ns552p1081 89650738 137438953472 19238770 19220000 (Ns552p1082 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1084 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns552p1058 Ns552p1059 66536413338872188387 Ns552p410 1028844475172 536870912 4539 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz370 qz156 (Enclosure.sfrac Bool.true Ns552p1060 Ns552p1061)) Bool.false Ns552p1058 Ns552p1059 66536413338872188387 Ns552p410 Ns552p1062 (Ns552p1079 rfl rfl)) 

noncomputable def Ns552p1085 := Ns552p1057 79012 BSN.abs_quadSignPos (BSN.cos_quad_nat3 799 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 313851515 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 553 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 288049945 536870912) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 67108849 67108864 43168663 5038407680000 536870792 536870912 4600 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 67108849 67108864 43168663 5038407680000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 67108849 67108864 690698608 80614522880000 67108849 67108864 43168663 5038407680000 (Ns552p1083 rfl rfl) rfl)) rfl) (Ns552p1084 rfl) RS553to564.d7 

noncomputable def Ns552p1086 := nat_lit 3172176236987433101397007130033970059898139699556684826783044142268965120 

noncomputable def Ns552p1087 := nat_lit 159422051692800520773465925176456508445959926754409555266727756718336 

noncomputable def Ns552p1088 := nat_lit 8307822508788155493291861633829159703481453373243238835628017099098317056 

noncomputable def Ns552p1089 := BSN.sin_dyadic_bound_f 335211222 536870912 3 2 536870912 268435456 Ns552p1086 Ns552p130 Ns552p1087 Ns552p1088 Ns552p133 Ns552p1087 313851515 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 335211222) qz371 0 2 Ns552p1086 Ns552p130 Ns552p1087 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 335211222) qz372 0 2 Ns552p1088 Ns552p133 Ns552p1087 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1090 := nat_lit 2146940320757419314902863757100143068373172873033951732232397866820582145 

noncomputable def Ns552p1091 := nat_lit 73027735121000524337039733696520178453425543829058239850596338645761 

noncomputable def Ns552p1092 := nat_lit 5622820699936378490563335585217247003545575788017959871077474399981812481 

noncomputable def Ns552p1093 := BSN.sin_dyadic_bound_f 304043679 536870912 3 2 536870912 268435456 Ns552p1090 Ns552p130 Ns552p1091 Ns552p1092 Ns552p133 Ns552p1091 288049945 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 304043679) qz371 0 2 Ns552p1090 Ns552p130 Ns552p1091 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 304043679) qz372 0 2 Ns552p1092 Ns552p133 Ns552p1091 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1094 := nat_lit 27807286752401878031164086473017014508104647552505537642068440596702870206155884455616820324812074681394126188161 

noncomputable def Ns552p1095 := nat_lit 8191075195376032232918347186227883036261105436852288750186146237059827605350736722468053775967765330980481 

noncomputable def Ns552p1096 := nat_lit 168535298912639505434589570134251914110317279821830776836974777191914208219018205333265725618069636292238996205185 

noncomputable def Ns552p1097 := BSN.cos_dyadic_bound_f 670056991 536870912 4 3 536870912 268435456 Ns552p1094 Ns552p151 Ns552p1095 Ns552p1096 Ns552p154 Ns552p1095 170266110 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 670056991) qz373 0 3 Ns552p1094 Ns552p151 Ns552p1095 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 670056991) qz374 0 3 Ns552p1096 Ns552p154 Ns552p1095 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1098 := nat_lit 2959332871606208640612743029808984740064416819559298564321234150400000000 

noncomputable def Ns552p1099 := nat_lit 138747237289794841221671967574142038821875177296891210000000000000000 

noncomputable def Ns552p1100 := nat_lit 7750409072965410581385682371076030470201094348558729844596565632000000000 

noncomputable def Ns552p1101 := BSN.sin_dyadic_bound_f 329441300 536870912 3 2 536870912 268435456 Ns552p1098 Ns552p130 Ns552p1099 Ns552p1100 Ns552p133 Ns552p1099 309152192 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 329441300) qz371 0 2 Ns552p1098 Ns552p130 Ns552p1099 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 329441300) qz372 0 2 Ns552p1100 Ns552p133 Ns552p1099 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1102 := Ns552p1055 133891 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 378 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 170266110 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 243 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 309152192 536870912) qz155 rfl rfl (Ns552p1085 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p1089 rfl rfl) (Ns552p1093 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p1084 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p1097 rfl rfl) (Ns552p1101 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p1103 := nat_lit 22978071766877059289356408146283013855708450979897246494687937528068773312520355109193285122778995971374203273216 

noncomputable def Ns552p1104 := nat_lit 4625214870227791593625547902923508431870011822690488387509719459782039877665092717119445850715937556135936 

noncomputable def Ns552p1105 := nat_lit 139289469349604927056356865314884244056791718280841677313223091509956324396161371128905956313795727061203151749120 

noncomputable def Ns552p1106 := BSN.cos_dyadic_bound_f 638892308 536870912 4 3 536870912 268435456 Ns552p1103 Ns552p151 Ns552p1104 Ns552p1105 Ns552p154 Ns552p1104 199518592 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 638892308) qz373 0 3 Ns552p1103 Ns552p151 Ns552p1104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 638892308) qz374 0 3 Ns552p1105 Ns552p154 Ns552p1104 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1107 := nat_lit 1157040874251223228343541046517776 

noncomputable def Ns552p1108 := BSN.sin_dyadic_bound_f 184432382 536870912 2 1 536870912 268435456 Ns552p1107 Ns552p283 Ns552p1107 Ns552p1107 Ns552p284 Ns552p1107 180826117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 184432382) qz371 0 1 Ns552p1107 Ns552p283 Ns552p1107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 184432382) qz372 0 1 Ns552p1107 Ns552p284 Ns552p1107 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1109 := Ns552p1053 180195 BSN.abs_quadSignPos (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 199518592 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 180826117 536870912) qz155 rfl rfl (Ns552p1102 rfl rfl) (Ns552p1084 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p1106 rfl rfl) (Ns552p1108 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1110 := nat_lit 77428773057587269544998682813209755982523964514826955617004421492337151483961149594148317374807938836091835592721 

noncomputable def Ns552p1111 := nat_lit 10078896839486914967789055596408789651627672362728600117673263919268963771462765590664689503361670203387921 

noncomputable def Ns552p1112 := nat_lit 386938224071844366797133770167465544339935307177961066354815662900548273933515104106634772547196724636123400843281 

noncomputable def Ns552p1113 := BSN.sin_dyadic_bound_f 681738389 536870912 4 3 536870912 268435456 Ns552p1110 Ns552p177 Ns552p1111 Ns552p1112 Ns552p180 Ns552p1111 512739885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 681738389) qz371 0 3 Ns552p1110 Ns552p177 Ns552p1111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 681738389) qz372 0 3 Ns552p1112 Ns552p180 Ns552p1111 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1114 := nat_lit 773704636456577593316634334573427825602429980012742455837660489073716225 

noncomputable def Ns552p1115 := nat_lit 9484559891921737565732831846882501241109401506850503921612921400321 

noncomputable def Ns552p1116 := nat_lit 2026353930003592490158935880250273162051973865764266769235142479034608641 

noncomputable def Ns552p1117 := BSN.sin_dyadic_bound_f 235573887 536870912 3 2 536870912 268435456 Ns552p1114 Ns552p130 Ns552p1115 Ns552p1116 Ns552p133 Ns552p1115 228086873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 235573887) qz371 0 2 Ns552p1114 Ns552p130 Ns552p1115 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 235573887) qz372 0 2 Ns552p1116 Ns552p133 Ns552p1115 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1118 := Ns552p1051 220651 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 512739885 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 228086873 536870912) qz155 rfl rfl (Ns552p1109 rfl) (Ns552p1084 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p1113 rfl rfl) (Ns552p1117 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1119 := nat_lit 1027525828565689061929785627774976 

noncomputable def Ns552p1120 := BSN.sin_dyadic_bound_f 179039224 536870912 2 1 536870912 268435456 Ns552p1119 Ns552p283 Ns552p1119 Ns552p1119 Ns552p284 Ns552p1119 175739038 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 179039224) qz371 0 1 Ns552p1119 Ns552p283 Ns552p1119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 179039224) qz372 0 1 Ns552p1119 Ns552p284 Ns552p1119 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1121 := nat_lit 2403847349064411073697087540496 

noncomputable def Ns552p1122 := BSN.sin_dyadic_bound_f 39375558 536870912 2 1 536870912 268435456 Ns552p1121 Ns552p283 Ns552p1121 Ns552p1121 Ns552p284 Ns552p1121 39340266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 39375558) qz371 0 1 Ns552p1121 Ns552p283 Ns552p1121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 39375558) qz372 0 1 Ns552p1121 Ns552p284 Ns552p1121 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1123 := Ns552p1049 257036 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 175739038 536870912) BSN.abs_quadSignPos qz598 (BSN.sfrac_eq_quadSignPos_mul Bool.false 39340266 536870912) qz155 rfl rfl (Ns552p1118 rfl) (Ns552p1084 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p1120 rfl rfl) (Ns552p1122 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1124 := nat_lit 92596839098643459845574895373302573432996668668568225413142328552938832246855310271933232758670470139488452939776 

noncomputable def Ns552p1125 := nat_lit 17229602515928919588314123001675126145610650120725881957937245342953967781783723553522399991026734914277376 

noncomputable def Ns552p1126 := nat_lit 462690181276449133766011847877948432657571295511268557759063649007809995666247789295478710517345262266077008039936 

noncomputable def Ns552p1127 := BSN.sin_dyadic_bound_f 712890682 536870912 4 3 536870912 268435456 Ns552p1124 Ns552p177 Ns552p1125 Ns552p1126 Ns552p180 Ns552p1125 521106441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 712890682) qz371 0 3 Ns552p1124 Ns552p177 Ns552p1125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 712890682) qz372 0 3 Ns552p1126 Ns552p180 Ns552p1125 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1128 := Ns552p1047 Bool.false 494392682 257036 Bool.true 712890682 28296951008113761 1 Bool.false 521106441 Bool.false Bool.false 644823159 274040 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 521106441 536870912) qz155 rfl (Ns552p1123 rfl) (Ns552p1084 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p1127 rfl rfl) rfl 

noncomputable def Ns552p1129 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) 644823159 536870912 274040 536870912 644823159 536870912 274040 536870912 692373594902102016 644823159 268435456 34255 33554432 (Ns552p1128 rfl rfl rfl rfl) 

noncomputable def Ns552p1130 := @Enclosure.Real.IsNear.mulLit_ff qz673 (Zeta.RiemannSiegel.correction qz154) 9560997 33554432 1 33554432 249847691436981 562949953421312 529129853566319 27049745261894041600 2388793028285901030057 18889465931478580854784 

noncomputable abbrev qz678 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns552p1131 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz678 1 1 0 1 9560997 33554432 1 33554432 9560997 33554432 1 33554432 

noncomputable def Ns552p1132 := @Enclosure.Real.IsNear.sqrt_image qz153 5090222022767 33554432000 476581 33554432000 413278952 413278992 33554432 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 5090222022767 33554432000 476581 33554432000 (BSN.t_div_two_pi_mk qz152 953162 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 953162 1000 0 1 10680707 67108864 1 67108864 5090222022767 33554432000 476581 33554432000 (Enclosure.Real.IsNear.const Bool.false 953162 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz778 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 953162 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz679 := qz778

noncomputable abbrev qz478 := qz679

noncomputable abbrev qz161 := qz478

noncomputable def Ns552p1133 := @Enclosure.Real.IsNear.sqrt_image qz161 103319743 8388608 5 8388608 117759672 117759679 33554432 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 826557944 67108864 40 67108864 103319743 8388608 5 8388608 (Ns552p1132 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p1134 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 235519351 67108864 7 67108864 9560996 9560998 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 235519351 67108864 7 67108864 235519351 67108864 7 67108864 (Ns552p1133 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p1135 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 19121994 67108864 2 67108864 9560997 33554432 1 33554432 (Ns552p1134 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz479 := (@HMul.hMul Real Real Real qz584 qz582 qz672)

noncomputable abbrev qz162 := (Real.cos qz479)

noncomputable abbrev qz680 := (@HMul.hMul Real Real Real qz742 qz777 qz777)

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz680 qz672) qz603)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz480))

noncomputable def Ns552p1136 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz162) qz163) Bool.false 249847691436981 

noncomputable def Ns552p1137 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz162) qz163 41244571 16777216 783 

noncomputable abbrev qz164 := (@Neg.neg Real Real.instNeg (Real.cos qz479))

noncomputable def Ns552p1138 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz162) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz164)) Bool.true 41244571 16777216 783 33554432 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns552p1139 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz164) Bool.false 164978284 67108864 1566 67108864 41244571 16777216 

noncomputable def Ns552p1140 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 13649068 33554432 622207216 161229045760000 3412267 8388608 38887951 10076815360000 

noncomputable abbrev qz165 := qz479

noncomputable def Ns552p1141 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66763795) qz627) Bool.false 66763795 33554432 63 16777216 Bool.true 13649068 33554432 1 

noncomputable def Ns552p1142 := nat_lit 134930377068038933252959459 

noncomputable def Ns552p1143 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 2656447 8388608 5 8388608 2349042206707836669085 1180591620717411303424 Ns552p1142 

noncomputable def Ns552p1144 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 103319743 8388608 5 8388608 12 1 0 1 2656447 2656447 8388608 5 

noncomputable def Ns552p1145 := @Ns552p1144 8388608 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 826557944 67108864 40 67108864 103319743 8388608 5 8388608 (Ns552p1132 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p1146 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 2349042206707836669085 1180591620717411303424 Ns552p1142 Ns552p495 66763795 33554432 63 16777216 (@Ns552p1143 Ns552p495 RS553to564.d55 (Ns552p1145 rfl rfl) rfl) 

noncomputable def Ns552p1147 := nat_lit 643172028266601336927161299463033130003321672544445257808149921889273957267315203847615955095640625 

noncomputable def Ns552p1148 := nat_lit 7843179952071725294477303282288280678444301595058720355400381497588280353905240187617431640625 

noncomputable def Ns552p1149 := nat_lit 3877826771900836827361004739520432054719237298764103370684386504298006183987615296393733855793240625 

noncomputable def Ns552p1150 := BSN.cos_dyadic_bound_t 66763795 33554432 4 3 33554432 9610000 Ns552p1147 Ns552p501 Ns552p1148 Ns552p1149 Ns552p504 Ns552p1148 13649068 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 66763795) (BSN.cosEvenQ 33554432) 0 3 Ns552p1147 Ns552p501 Ns552p1148 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 66763795) (BSN.cosOddQ 33554432) 0 3 Ns552p1149 Ns552p504 Ns552p1148 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1151 := @Enclosure.Real.IsNear.inv_image qz164 3412267 8388608 38887951 10076815360000 82488359 82489925 33554432 (@Enclosure.Real.IsNear.neg qz162 Bool.true 3412267 8388608 38887951 10076815360000 (Ns552p1140 (@Ns552p1141 9610000 (Ns552p1146 rfl) (Enclosure.sfrac_false_div 66763795 33554432) (Ns552p1150 rfl rfl) rfl rfl) rfl)) 

noncomputable def Ns552p1152 := Ns552p1138 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz164) Bool.false 41244571 16777216 783 33554432 (@Ns552p1139 783 33554432 (Ns552p1151 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1153 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true 6057711 33554432 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz355 qz352 qz480)

noncomputable def Ns552p1154 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 117596575)) qz380) Bool.true 117596575 67108864 

noncomputable def Ns552p1155 := nat_lit 17354191457648210304021917405 

noncomputable def Ns552p1156 := nat_lit 9903520314283042199192993792 

noncomputable def Ns552p1157 := nat_lit 1848749505766303688897019439598377 

noncomputable def Ns552p1158 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns552p1155 Ns552p1156 Ns552p1157 

noncomputable abbrev qz167 := qz480

noncomputable def Ns552p1159 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 19625228403071 

noncomputable abbrev qz481 := (@HSub.hSub Real Real Real qz588 qz680 qz672)

noncomputable abbrev qz168 := qz481

noncomputable def Ns552p1160 := @Enclosure.Real.IsNear.subLit_tf qz168 qz31 15227181891967 70368744177664 68507535 70368744177664 1 16 

noncomputable abbrev qz482 := qz680

noncomputable abbrev qz169 := qz482

noncomputable def Ns552p1161 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz154 7056710663809 70368744177664 26564495 70368744177664 2656447 8388608 5 8388608 

noncomputable def Ns552p1162 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 2656447 8388608 5 8388608 2656447 8388608 5 8388608 7056710663809 70368744177664 

noncomputable def Ns552p1163 := nat_lit 1578977943533909628543765637350119976035253421586445689008717963609409933415471607855277818939462890625 

noncomputable def Ns552p1164 := nat_lit 6994168278998329961917915691483737513643646995191702075642840379107853995361738264560699462890625 

noncomputable def Ns552p1165 := nat_lit 9543456225993221320386254970148560644616042270446335091148216007551427100015929209472998327355462890625 

noncomputable def Ns552p1166 := BSN.cos_dyadic_bound_t 117596575 67108864 4 3 33554432 9610000 Ns552p1163 Ns552p203 Ns552p1164 Ns552p1165 Ns552p206 Ns552p1164 6057711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 117596575) qz604 0 3 Ns552p1163 Ns552p203 Ns552p1164 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 117596575) (BSN.cosOddQ 67108864) 0 3 Ns552p1165 Ns552p206 Ns552p1164 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1167 := @Ns552p1153 1006607216 161229045760000 6057711 33554432 62912951 10076815360000 (@Ns552p1154 103 16777216 Bool.true 6057711 33554432 1 9610000 (@Ns552p1158 Ns552p514 117596575 67108864 103 16777216 (@Ns552p1159 70368744177664 68507535 70368744177664 Ns552p1155 Ns552p1156 Ns552p1157 Ns552p514 RS553to564.d55 (@Ns552p1160 0 1 314003654449136 19625228403071 70368744177664 68507535 70368744177664 (@Ns552p1161 127734859836409511936 15227181891967 70368744177664 68507535 70368744177664 (@Ns552p1162 26564495 70368744177664 (Ns552p1145 rfl rfl) (Ns552p1145 rfl rfl) rfl) (Ns552p1145 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 117596575 67108864) (BSN.cos_neg_of_bound 117596575 67108864 Bool.true 6057711 33554432 1 9610000 (Ns552p1166 rfl rfl)) rfl rfl) 

noncomputable def Ns552p1168 := @Ns552p1130 1267753663315353940853 Ns552p1044 (Ns552p1131 qz33 (@Enclosure.Real.IsNear.of_eq qz678 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 9560997 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 953162 1000 qz155)) Ns552p1135) rfl) (@Ns552p1136 562949953421312 529129853566319 27049745261894041600 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 953162 1000 12 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 953162 1000 12 qz155 rfl rfl rfl))) (@Ns552p1137 33554432 6057711 33554432 62912951 10076815360000 249847691436981 562949953421312 529129853566319 27049745261894041600 Ns552p1152 (Ns552p1167 rfl) rfl)) 

noncomputable def Ns552p1169 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 42986602887218256690519 18889465931478580854784 232915009649860452692853 Ns552p1044 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HMul.hMul Real Real Real qz5 qz673 (Zeta.RiemannSiegel.correction qz154))) Bool.false 42986602887218256690519 18889465931478580854784 232915009649860452692853 Ns552p1044 (BSN.hardyZApproximantRS₀_eq qz152 12 (@BSN.floor_sqrt_eq_dec qz152 953162 1000 12 qz155 rfl rfl rfl)) (@Ns552p1046 42986602887218256690519 18889465931478580854784 232915009649860452692853 Ns552p1044 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12)) Bool.false 644823159 268435456 34255 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (Ns552p1129 (Ns552p1128 rfl rfl rfl rfl) rfl rfl)) (Ns552p1168 rfl) rfl rfl)) 

theorem RS553to564.d66 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 42986602887218256690519 18889465931478580854784 232915009649860452692853 Ns552p1044 := Ns552p1169 

noncomputable def Ns552p1170 := nat_lit 93235746440476216412774151 

noncomputable def Ns552p1171 := nat_lit 90763883800754581007237120000 

noncomputable def Ns552p1172 := nat_lit 25835121241457505737271624597504 

noncomputable abbrev qz779 := (Enclosure.sfrac Bool.false 954413 1000)

noncomputable abbrev qz681 := qz779

noncomputable abbrev qz483 := qz681

noncomputable abbrev qz170 := qz483

noncomputable abbrev qz780 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 954413 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz682 := qz780

noncomputable abbrev qz484 := qz682

noncomputable abbrev qz171 := qz484

noncomputable abbrev qz781 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 954413 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz683 := qz781

noncomputable abbrev qz485 := qz683

noncomputable abbrev qz172 := qz485

noncomputable abbrev qz684 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz171 qz9))

noncomputable def Ns552p1173 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HMul.hMul Real Real Real qz5 qz684 (Zeta.RiemannSiegel.correction qz172)) 137443757 268435456 68599 67108864 18869369919188842160975 151115727451828646838272 456472679442748426854151 Ns552p1171 Ns552p1172 

noncomputable def Ns552p1174 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin BSN.quadSignPos 11 12 954413 1000 287 536870912 268435456 9007199254740992 Bool.false 1030531116265 4544 1334074092 57 154981288 8 

noncomputable def Ns552p1175 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 9 10 11 954413 1000 177 234 536870912 268435456 9007199254740992 Bool.false 1030531116265 4544 

noncomputable def Ns552p1176 := Ns552p1175 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 263200195 220938 Bool.true 38873017 Bool.true 806536957 28296951008113761 1 Bool.false 38839059 Bool.true Bool.false 36749140 Bool.true Bool.true 286562467 

noncomputable def Ns552p1177 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 7 8 9 954413 1000 41 113 536870912 268435456 9007199254740992 Bool.false 1030531116265 4544 

noncomputable def Ns552p1178 := Ns552p1177 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 128463902 180430 Bool.true 391703283 Bool.true 24644855 28296951008113761 1 Bool.false 357864544 Bool.true Bool.false 24636200 Bool.true Bool.true 263200195 

noncomputable def Ns552p1179 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 954413 1000 133 39 536870912 268435456 9007199254740992 Bool.false 1030531116265 4544 

noncomputable def Ns552p1180 := Ns552p1179 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 195779750 134066 Bool.false 278827185 Bool.false 564150596 28296951008113761 1 Bool.false 266460441 Bool.true Bool.false 465911154 Bool.false Bool.true 128463902 

noncomputable def Ns552p1181 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 954413 1000 379 244 536870912 268435456 9007199254740992 Bool.false 1030531116265 4544 

noncomputable def Ns552p1182 := Ns552p1181 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 669705653 79116 Bool.false 582312587 Bool.false 91827996 28296951008113761 1 Bool.false 474666938 Bool.false Bool.false 529036772 Bool.false Bool.true 195779750 

noncomputable def Ns552p1183 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 954413 1000 800 554 536870912 268435456 9007199254740992 Bool.false 1030531116265 4544 

noncomputable def Ns552p1184 := Ns552p1183 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870784 4608 Bool.false 713002148 Bool.false 409513882 28296951008113761 1 Bool.false 129036887 Bool.false Bool.false 388114005 Bool.true Bool.true 669705653 

noncomputable def Ns552p1185 := nat_lit 235218754160143821533362951149453887680393558840870704327467 

noncomputable def Ns552p1186 := nat_lit 122540799663703854828598625878408422214970350925512704000 

noncomputable def Ns552p1187 := nat_lit 380122231690504487576571566380640000 

noncomputable def Ns552p1188 := nat_lit 2176761875881962546028323151119970585920 

noncomputable abbrev qz685 := (@Eq.refl Real qz779)

noncomputable abbrev qz486 := qz685

noncomputable abbrev qz173 := qz486

noncomputable def Ns552p1189 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 954413 1000 3643617698276 16000000 1908826 4000 2000 Ns552p1187 Ns552p1188 qz173 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p1190 := nat_lit 75270001331246022890676144367825244057725938829078625384789440 

noncomputable abbrev qz686 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1908826))))

noncomputable abbrev qz487 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 954413 4000) (Real.log (Enclosure.sfrac Bool.false 3643617698276 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz686))

noncomputable abbrev qz687 := (Enclosure.sfrac Bool.false 954413 2000)

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz487 qz687) (@HMul.hMul Real Real Real qz355 qz687 (Real.log Real.pi)))

noncomputable def Ns552p1191 := @Enclosure.Real.IsNear.addLit_ft_p qz174 (Enclosure.sfrac Bool.true Ns552p1187 Ns552p1188) 34578889410410177058907 18014398509481984000 133246943665802436251 Ns552p244 Ns552p1187 Ns552p1188 0 1 Ns552p1190 

noncomputable def Ns552p1192 := nat_lit 464109997342851351292421970329600 

noncomputable abbrev qz175 := (@HSub.hSub Real Real Real qz359 qz487 qz687)

noncomputable def Ns552p1193 := @Enclosure.Real.IsNear.subLit_ff_p qz175 (@HMul.hMul Real Real Real qz5 qz687 (Real.log Real.pi)) 8883932130540414715103 3602879701896396800 12030178092725681 3844000000000000000000 36659729638293 67108864000 2863239 536870912000 Ns552p1192 34578889410410177058907 18014398509481984000 

noncomputable def Ns552p1194 := nat_lit 88839321305404147151030000 

noncomputable abbrev qz176 := qz487

noncomputable def Ns552p1195 := @Enclosure.Real.IsNear.subLit_ff_p qz176 qz687 53016248715017187973211 18014398509481984000 12030178092725681 3844000000000000000000 954413 2000 0 1 Ns552p1194 8883932130540414715103 3602879701896396800 12030178092725681 3844000000000000000000 

noncomputable def Ns552p1196 := nat_lit 119381978978766472569330476833809891328 

noncomputable def Ns552p1197 := nat_lit 119305493467902696809824256 

noncomputable def Ns552p1198 := nat_lit 85593512831519602795020476222260008175318847650914627000464279342869391445854880757831686857053957614636632252987967734172357727916885689113919041117319605115883583025530107536500326400 

noncomputable def Ns552p1199 := nat_lit 2165527148099531346775231276386030565705729540086015871617591498811846535309981554869916054584708306867224793632656291705300298479111771803365903150565381297749885027715040776384675840 

noncomputable def Ns552p1200 := nat_lit 60468880278768027454816353072265990543683477788417556881545279485855444319421219013358039487290760469271175656072761109410891815871490773261516430731621973683832859582540021760 

noncomputable def Ns552p1201 := BSN.log_dyadic_bound 1546465698276 5740769698276 8 7 Ns552p1198 268435456 76880000 Ns552p1199 Ns552p1200 148282894 7287235396552 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1546465698276) (BSN.artanhQ 5740769698276) 0 7 Ns552p1199 Ns552p1198 Ns552p1200 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz488 := (Real.log (Enclosure.sfrac Bool.false 3643617698276 16000000))

noncomputable def Ns552p1202 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 954413 4000) qz488 954413 4000 0 1 55555949671148647 4503599627370496 12500016337 961000000000000000 53023320593489993629211 18014398509481984000 11930178092245181 3844000000000000000000 (Enclosure.Real.IsNear.const Bool.false 954413 4000) (BSN.isNear_log_sfrac 3643617698276 16000000 55555949671148647 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3643617698276) qz362)) Bool.false Ns552p1197 Ns552p114 1000001306960000 76880000000000000000000 55555949671148647 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3643617698276 16000000 17 7287235396552 4194304000000 148282894 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p1201 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1203 := BSN.arctan_dyadic_bound_f 1000 1908826 1 0 33554432 9610000 0 1 1 0 1 1 17578 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1908826) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1908826) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p1204 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1908826))) 884279719003555 562949953421312 1 2000000000000000 17578 33554432 1 9610000 29661608166002654183424 883984809100707 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p1203 rfl) rfl rfl 

noncomputable abbrev qz489 := (@HMul.hMul Real Real Real qz584 qz589 qz686)

noncomputable abbrev qz177 := qz489

noncomputable abbrev qz490 := qz686

noncomputable abbrev qz178 := qz490

noncomputable def Ns552p1205 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 954413 4000) qz488) qz177 53023320593489993629211 18014398509481984000 11930178092245181 3844000000000000000000 883984809100707 2251799813685248 200000000961 7688000000000000000 Ns552p1196 53016248715017187973211 18014398509481984000 12030178092725681 3844000000000000000000 (Ns552p1202 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz178 1 4 0 1 883984809100707 562949953421312 200000000961 1922000000000000000 883984809100707 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p1204 rfl) 

noncomputable def Ns552p1206 := @Ns552p1191 Ns552p1185 Ns552p1186 133246943665802436251 Ns552p244 (@Ns552p1193 133246943665802436251 Ns552p244 (Ns552p1195 (Ns552p1205 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 954413 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz687 (Real.log Real.pi) 954413 2000 0 1 38410761 33554432 3 268435456 36659729638293 67108864000 2863239 536870912000 (Enclosure.Real.IsNear.const Bool.false 954413 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p1187 Ns552p1188) 

noncomputable def Ns552p1207 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns552p1185 Ns552p1186 133246943665802436251 Ns552p244 128816389533 67108864 569 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz370 qz174 (Enclosure.sfrac Bool.true Ns552p1187 Ns552p1188)) Bool.false Ns552p1185 Ns552p1186 133246943665802436251 Ns552p244 Ns552p1189 (Ns552p1206 rfl rfl)) 

noncomputable def Ns552p1208 := BSN.cos_dyadic_bound_f 92564769 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 92564769) qz595 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 92564769) qz596 0 0 rfl) rfl rfl 

noncomputable def Ns552p1209 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 128816389533) qz380) Bool.false 128816389533 67108864 569 67108864 Bool.true 67108848 67108864 1 9610000 (Ns552p1207 rfl) (Enclosure.sfrac_false_div 128816389533 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 128816389533) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6513666584500697563136) qz394) 226375608064910080 72057594037927936 Bool.false 67108848 67108864 305 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q2 128816389533 67108864 226375608064910080 72057594037927936 305 6513666584500697563136 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108848 67108864 6513666584500697563136 Ns552p114 92564769 137438953472 19238770 19220000 (Ns552p1208 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1210 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns552p1185 Ns552p1186 133246943665802436251 Ns552p244 1030531116265 536870912 4544 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz370 qz174 (Enclosure.sfrac Bool.true Ns552p1187 Ns552p1188)) Bool.false Ns552p1185 Ns552p1186 133246943665802436251 Ns552p244 Ns552p1189 (Ns552p1206 rfl rfl)) 

noncomputable def Ns552p1211 := Ns552p1184 79116 BSN.abs_quadSignPos (BSN.cos_quad_nat0 800 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 129036887 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 554 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 388114005 536870912) qz173 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 4194303 4194304 345949929 40307261440000 536870784 536870912 4608 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 4194303 4194304 345949929 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 67108848 67108864 5535198864 644916183040000 4194303 4194304 345949929 40307261440000 (Ns552p1209 rfl rfl) rfl)) rfl) (Ns552p1210 rfl) RS553to564.d7 

noncomputable def Ns552p1212 := nat_lit 35665779989544919841578615415692792393513803983963031946481809174435001963180964264215157330717801821951204786176 

noncomputable def Ns552p1213 := nat_lit 17261958118792611302692677711518508929477812926385068505186351198889732939304931353176291154369668706205696 

noncomputable def Ns552p1214 := nat_lit 216105698022396213969645029874082631104107301755602069204379307983637519513997889916275666742601993271634863063040 

noncomputable def Ns552p1215 := BSN.cos_dyadic_bound_f 713002148 536870912 4 3 536870912 268435456 Ns552p1212 Ns552p151 Ns552p1213 Ns552p1214 Ns552p154 Ns552p1213 129036887 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 713002148) qz373 0 3 Ns552p1212 Ns552p151 Ns552p1213 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 713002148) qz374 0 3 Ns552p1214 Ns552p154 Ns552p1213 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1216 := nat_lit 3926004525997888780064074799295374189173902647822240223513542345718374656 

noncomputable def Ns552p1217 := nat_lit 790949993857544132798059295202362044123168070582893075166519741522176 

noncomputable def Ns552p1218 := nat_lit 11776431678005951251926628279295717843433461607325554884390293997672079616 

noncomputable def Ns552p1219 := BSN.cos_dyadic_bound_f 409513882 536870912 3 2 536870912 268435456 Ns552p1216 Ns552p140 Ns552p1217 Ns552p1218 Ns552p143 Ns552p1217 388114005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 409513882) qz373 0 2 Ns552p1216 Ns552p140 Ns552p1217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 409513882) qz374 0 2 Ns552p1218 Ns552p143 Ns552p1217 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1220 := nat_lit 28899126619033287314501858462147240403779932306429870804098693398625654625 

noncomputable def Ns552p1221 := nat_lit 13220546917703465769495481909653494650094202667898038459347938195937121 

noncomputable def Ns552p1222 := nat_lit 75666784069125184974354255668246190637609193998234969567514776525035673441 

noncomputable def Ns552p1223 := BSN.sin_dyadic_bound_f 582312587 536870912 3 2 536870912 268435456 Ns552p1220 Ns552p130 Ns552p1221 Ns552p1222 Ns552p133 Ns552p1221 474666938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 582312587) qz371 0 2 Ns552p1220 Ns552p130 Ns552p1221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 582312587) qz372 0 2 Ns552p1222 Ns552p133 Ns552p1221 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1224 := nat_lit 71105046788923381035776556032256 

noncomputable def Ns552p1225 := BSN.cos_dyadic_bound_f 91827996 536870912 2 1 536870912 268435456 Ns552p1224 Ns552p157 Ns552p1224 Ns552p1224 Ns552p158 Ns552p1224 529036772 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 91827996) qz373 0 1 Ns552p1224 Ns552p157 Ns552p1224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 91827996) qz374 0 1 Ns552p1224 Ns552p158 Ns552p1224 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1226 := Ns552p1182 134066 BSN.abs_quadSignPos (BSN.cos_quad_nat3 379 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 474666938 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 244 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 529036772 536870912) qz173 rfl rfl (Ns552p1211 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p1215 rfl rfl) (Ns552p1219 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p1210 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p1223 rfl rfl) (Ns552p1225 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p1227 := nat_lit 1518490884563427759314724782060459217678546290177158302438912711704330625 

noncomputable def Ns552p1228 := nat_lit 36532627907525894194558774222852111617783671747561953509593562890625 

noncomputable def Ns552p1229 := nat_lit 3976940787697127184852726095952460952405954348328775691796232045838090625 

noncomputable def Ns552p1230 := BSN.sin_dyadic_bound_f 278827185 536870912 3 2 536870912 268435456 Ns552p1227 Ns552p130 Ns552p1228 Ns552p1229 Ns552p133 Ns552p1228 266460441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 278827185) qz371 0 2 Ns552p1227 Ns552p130 Ns552p1228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 278827185) qz372 0 2 Ns552p1229 Ns552p133 Ns552p1228 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1231 := nat_lit 25457547373579092418326911351163682639998955240907428979399806968171397120 

noncomputable def Ns552p1232 := nat_lit 10260308294100664605316642254361108421772275778174809418724856876302336 

noncomputable def Ns552p1233 := nat_lit 66657916907850031448161874213207346072076299089211935730797749434077741056 

noncomputable def Ns552p1234 := BSN.sin_dyadic_bound_f 564150596 536870912 3 2 536870912 268435456 Ns552p1231 Ns552p130 Ns552p1232 Ns552p1233 Ns552p133 Ns552p1232 465911154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 564150596) qz371 0 2 Ns552p1231 Ns552p130 Ns552p1232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 564150596) qz372 0 2 Ns552p1233 Ns552p133 Ns552p1232 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1235 := Ns552p1180 180430 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 266460441 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 39 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 465911154 536870912) qz173 rfl rfl (Ns552p1226 rfl rfl) (Ns552p1210 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p1230 rfl rfl) (Ns552p1234 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1236 := nat_lit 5914674157289019855770149349561043895183382609505000725522958335876093985 

noncomputable def Ns552p1237 := nat_lit 554188733276395438261109107756106830624541905837873225933163397470241 

noncomputable def Ns552p1238 := nat_lit 15489916011141175934402730310294938409659276623713169153051475281793865761 

noncomputable def Ns552p1239 := BSN.sin_dyadic_bound_f 391703283 536870912 3 2 536870912 268435456 Ns552p1236 Ns552p130 Ns552p1237 Ns552p1238 Ns552p133 Ns552p1237 357864544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 391703283) qz371 0 2 Ns552p1236 Ns552p130 Ns552p1237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 391703283) qz372 0 2 Ns552p1238 Ns552p133 Ns552p1237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1240 := nat_lit 368896953927781857520739550625 

noncomputable def Ns552p1241 := BSN.sin_dyadic_bound_f 24644855 536870912 2 1 536870912 268435456 Ns552p1240 Ns552p283 Ns552p1240 Ns552p1240 Ns552p284 Ns552p1240 24636200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 24644855) qz371 0 1 Ns552p1240 Ns552p283 Ns552p1240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 24644855) qz372 0 1 Ns552p1240 Ns552p284 Ns552p1240 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1242 := Ns552p1178 220938 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 357864544 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 24636200 536870912) qz173 rfl rfl (Ns552p1235 rfl) (Ns552p1210 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p1239 rfl rfl) (Ns552p1241 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1243 := nat_lit 2283457816383131940683618279521 

noncomputable def Ns552p1244 := BSN.sin_dyadic_bound_f 38873017 536870912 2 1 536870912 268435456 Ns552p1243 Ns552p283 Ns552p1243 Ns552p1243 Ns552p284 Ns552p1243 38839059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 38873017) qz371 0 1 Ns552p1243 Ns552p283 Ns552p1243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 38873017) qz372 0 1 Ns552p1243 Ns552p284 Ns552p1243 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1245 := nat_lit 58465153487493973936360282987093512581784687564761355916877638624229108133443484753671133347964226599397274730481 

noncomputable def Ns552p1246 := nat_lit 75768949880882432220862410730454869536114286967377040467518719817102644894295179982671267318094924180668401 

noncomputable def Ns552p1247 := nat_lit 353973472442240748443091848083510354110091867359137219959420350980810000023632850125245313098940377957184792739825 

noncomputable def Ns552p1248 := BSN.cos_dyadic_bound_f 806536957 536870912 4 3 536870912 268435456 Ns552p1245 Ns552p151 Ns552p1246 Ns552p1247 Ns552p154 Ns552p1246 36749140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 806536957) qz373 0 3 Ns552p1245 Ns552p151 Ns552p1246 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 806536957) qz374 0 3 Ns552p1247 Ns552p154 Ns552p1246 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1249 := Ns552p1176 257370 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38839059 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36749140 536870912) qz173 rfl rfl (Ns552p1242 rfl) (Ns552p1210 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p1244 rfl rfl) (Ns552p1248 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1250 := nat_lit 83722359568343291255012452358551703410198104103595892308511057323184711120087573986908803864199020355427299823616 

noncomputable def Ns552p1251 := nat_lit 12739117031703192547696859194645062326190337001073744516254911429840403497127882953274972789139174178492416 

noncomputable def Ns552p1252 := nat_lit 418371397749943066172546853736015861880023484532950544167645805311161480585649055521213862527281369471940316696576 

noncomputable def Ns552p1253 := BSN.sin_dyadic_bound_f 695176278 536870912 4 3 536870912 268435456 Ns552p1250 Ns552p177 Ns552p1251 Ns552p1252 Ns552p180 Ns552p1251 516562347 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 695176278) qz371 0 3 Ns552p1250 Ns552p177 Ns552p1251 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 695176278) qz372 0 3 Ns552p1252 Ns552p180 Ns552p1251 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1254 := Ns552p1174 Bool.true 286562467 257370 Bool.true 695176278 28296951008113761 1 Bool.false 516562347 Bool.false Bool.true 137443757 274396 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 516562347 536870912) qz173 rfl (Ns552p1249 rfl) (Ns552p1210 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p1253 rfl rfl) rfl 

noncomputable def Ns552p1255 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) 137443757 536870912 274396 536870912 137443757 536870912 274396 536870912 147579110338592768 137443757 268435456 68599 67108864 (Ns552p1254 rfl rfl rfl rfl) 

noncomputable def Ns552p1256 := @Enclosure.Real.IsNear.mulLit_ff qz684 (Zeta.RiemannSiegel.correction qz172) 19115725 67108864 1 67108864 987112438538891 2251799813685248 11924208241799213 676243631547351040000 18869369919188842160975 151115727451828646838272 

noncomputable abbrev qz688 := (@HPow.hPow Real Real Real qz7 qz171 qz9)

noncomputable def Ns552p1257 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz688 1 1 0 1 19115725 67108864 1 67108864 19115725 67108864 1 67108864 

noncomputable def Ns552p1258 := @Enclosure.Real.IsNear.sqrt_image qz171 10193805609991 67108864000 954413 67108864000 413550072 413550112 33554432 (@Enclosure.Real.IsNear.of_eq qz171 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 10193805609991 67108864000 954413 67108864000 (BSN.t_div_two_pi_mk qz170 954413 1000 qz173) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 954413 1000 0 1 10680707 67108864 1 67108864 10193805609991 67108864000 954413 67108864000 (Enclosure.Real.IsNear.const Bool.false 954413 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz782 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 954413 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz689 := qz782

noncomputable abbrev qz491 := qz689

noncomputable abbrev qz179 := qz491

noncomputable def Ns552p1259 := @Enclosure.Real.IsNear.sqrt_image qz179 103387523 8388608 5 8388608 117798292 117798299 33554432 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 827100184 67108864 40 67108864 103387523 8388608 5 8388608 (Ns552p1258 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p1260 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 235596591 67108864 7 67108864 9557862 9557863 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 235596591 67108864 7 67108864 235596591 67108864 7 67108864 (Ns552p1259 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p1261 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 19115725 67108864 1 67108864 19115725 67108864 1 67108864 (Ns552p1260 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz492 := (@HMul.hMul Real Real Real qz584 qz582 qz683)

noncomputable abbrev qz180 := (Real.cos qz492)

noncomputable abbrev qz690 := (@HMul.hMul Real Real Real qz742 qz781 qz781)

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz690 qz683) qz603)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz493))

noncomputable def Ns552p1262 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz172) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 987112438538891 

noncomputable def Ns552p1263 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz180) qz181 148271473 67108864 1265 

noncomputable abbrev qz182 := (@Neg.neg Real Real.instNeg (Real.cos qz492))

noncomputable def Ns552p1264 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz180) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz182)) Bool.true 148271473 67108864 1265 67108864 (BSN.inv_eq_neg_inv_neg qz180) 

noncomputable def Ns552p1265 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz182) Bool.false 148271473 67108864 1265 67108864 148271473 67108864 

noncomputable def Ns552p1266 := @Enclosure.Real.IsNear.recentre' qz180 Bool.true 30374013 67108864 622207216 161229045760000 30374013 67108864 38887951 10076815360000 

noncomputable abbrev qz183 := qz492

noncomputable def Ns552p1267 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17116823) qz597) Bool.false 17116823 8388608 63 16777216 Bool.true 30374013 67108864 1 

noncomputable def Ns552p1268 := nat_lit 134930377068621159019605219 

noncomputable def Ns552p1269 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz172 884279719003555 140737488355328 1 500000000000000 2724227 8388608 5 8388608 2408978686061897626985 1180591620717411303424 Ns552p1268 

noncomputable def Ns552p1270 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 103387523 8388608 5 8388608 12 1 0 1 2724227 2724227 8388608 5 

noncomputable def Ns552p1271 := @Ns552p1270 8388608 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 827100184 67108864 40 67108864 103387523 8388608 5 8388608 (Ns552p1258 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p1272 := @Enclosure.Real.IsNear.recentre' qz183 Bool.false 2408978686061897626985 1180591620717411303424 Ns552p1268 Ns552p495 17116823 8388608 63 16777216 (@Ns552p1269 Ns552p495 RS553to564.d55 (Ns552p1271 rfl rfl) rfl) 

noncomputable def Ns552p1273 := nat_lit 17365094518320773076105381833074398885702561 

noncomputable def Ns552p1274 := nat_lit 42817430781178796431748579083484854091482398720 

noncomputable def Ns552p1275 := nat_lit 299722015468251575022240053584393978640376791040 

noncomputable def Ns552p1276 := BSN.sin_dyadic_bound_f 64553424759 137438953472 2 1 67108864 19238770 Ns552p1273 Ns552p1274 Ns552p1273 Ns552p1273 Ns552p1275 Ns552p1273 30374013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 64553424759) qz635 0 1 Ns552p1273 Ns552p1274 Ns552p1273 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 64553424759) qz636 0 1 Ns552p1273 Ns552p1275 Ns552p1273 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1277 := @Ns552p1267 9610000 (Ns552p1272 rfl) (Enclosure.sfrac_false_div 17116823 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 17116823) qz597) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 567817929087966318166016) (@Nat.cast Real Real.instNatCast Ns552p64)) 226375608064910080 72057594037927936 Bool.false 30374013 67108864 0 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q1 17116823 8388608 226375608064910080 72057594037927936 0 567817929087966318166016 Ns552p64 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 30374013 67108864 567817929087966318166016 Ns552p64 64553424759 137438953472 19238770 19220000 (Ns552p1276 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1278 := @Enclosure.Real.IsNear.inv_image qz182 30374013 67108864 38887951 10076815360000 74135104 74136369 33554432 (@Enclosure.Real.IsNear.neg qz180 Bool.true 30374013 67108864 38887951 10076815360000 (Ns552p1266 (Ns552p1277 rfl rfl) rfl)) 

noncomputable def Ns552p1279 := Ns552p1264 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz182) Bool.false 148271473 67108864 1265 67108864 (@Ns552p1265 1265 67108864 (Ns552p1278 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1280 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true 6657467 33554432 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz355 qz352 qz493)

noncomputable def Ns552p1281 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 59409117)) qz627) Bool.true 59409117 33554432 

noncomputable def Ns552p1282 := nat_lit 17534476431737588297361896005 

noncomputable def Ns552p1283 := nat_lit 1867040667680305039585702812890817 

noncomputable def Ns552p1284 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true Ns552p1282 Ns552p1156 Ns552p1283 

noncomputable abbrev qz185 := qz493

noncomputable def Ns552p1285 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz185 884279719003555 140737488355328 1 500000000000000 19829106169591 

noncomputable abbrev qz494 := (@HSub.hSub Real Real Real qz588 qz690 qz683)

noncomputable abbrev qz186 := qz494

noncomputable def Ns552p1286 := @Enclosure.Real.IsNear.subLit_tf qz186 qz31 15431059658487 70368744177664 69185335 70368744177664 1 16 

noncomputable abbrev qz495 := qz690

noncomputable abbrev qz187 := qz495

noncomputable def Ns552p1287 := @Enclosure.Real.IsNear.subLit_ff_n qz187 qz172 7421412747529 70368744177664 27242295 70368744177664 2724227 8388608 5 8388608 

noncomputable def Ns552p1288 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 2724227 8388608 5 8388608 2724227 8388608 5 8388608 7421412747529 70368744177664 

noncomputable def Ns552p1289 := nat_lit 401857659165939776573392577950184354703019349468099190702919181752569407744958804936584347428425841 

noncomputable def Ns552p1290 := nat_lit 1933023660398680585879909869166075025312529609141296454244652194239573790882272775555184693361 

noncomputable def Ns552p1291 := nat_lit 2428475195069758126247229193434205173324468889514042423085111640323962584160189641771412643884142705 

noncomputable def Ns552p1292 := BSN.cos_dyadic_bound_t 59409117 33554432 4 3 33554432 9610000 Ns552p1289 Ns552p501 Ns552p1290 Ns552p1291 Ns552p504 Ns552p1290 6657467 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 59409117) (BSN.cosEvenQ 33554432) 0 3 Ns552p1289 Ns552p501 Ns552p1290 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 59409117) (BSN.cosOddQ 33554432) 0 3 Ns552p1291 Ns552p504 Ns552p1290 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1293 := @Ns552p1280 4055258864 644916183040000 6657467 33554432 253453679 40307261440000 (@Ns552p1281 415 67108864 Bool.true 6657467 33554432 1 9610000 (@Ns552p1284 Ns552p514 59409117 33554432 415 67108864 (@Ns552p1285 70368744177664 69185335 70368744177664 Ns552p1282 Ns552p1156 Ns552p1283 Ns552p514 RS553to564.d55 (@Ns552p1286 0 1 317265698713456 19829106169591 70368744177664 69185335 70368744177664 (@Ns552p1287 129445110499661316096 15431059658487 70368744177664 69185335 70368744177664 (@Ns552p1288 27242295 70368744177664 (Ns552p1271 rfl rfl) (Ns552p1271 rfl rfl) rfl) (Ns552p1271 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 59409117 33554432) (BSN.cos_neg_of_bound 59409117 33554432 Bool.true 6657467 33554432 1 9610000 (Ns552p1292 rfl rfl)) rfl rfl) 

noncomputable def Ns552p1294 := @Ns552p1256 456472679442748426854151 Ns552p1171 (Ns552p1257 qz33 (@Enclosure.Real.IsNear.of_eq qz688 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 19115725 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz171 (BSN.t_div_two_pi_nonneg qz170 954413 1000 qz173)) Ns552p1261) rfl) (@Ns552p1262 2251799813685248 11924208241799213 676243631547351040000 (BSN.correction_mk qz172 (BSN.cos_two_pi_p_ne_zero_mk qz170 954413 1000 12 qz173 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 954413 1000 12 qz173 rfl rfl rfl))) (@Ns552p1263 67108864 6657467 33554432 253453679 40307261440000 987112438538891 2251799813685248 11924208241799213 676243631547351040000 Ns552p1279 (Ns552p1293 rfl) rfl)) 

noncomputable def Ns552p1295 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 96243326520388967310159 151115727451828646838272 Ns552p1170 Ns552p1171 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HMul.hMul Real Real Real qz5 qz684 (Zeta.RiemannSiegel.correction qz172))) Bool.true 96243326520388967310159 151115727451828646838272 Ns552p1170 Ns552p1171 (BSN.hardyZApproximantRS₀_eq qz170 12 (@BSN.floor_sqrt_eq_dec qz170 954413 1000 12 qz173 rfl rfl rfl)) (@Ns552p1173 96243326520388967310159 151115727451828646838272 Ns552p1170 Ns552p1171 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12)) Bool.true 137443757 268435456 68599 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (Ns552p1255 (Ns552p1254 rfl rfl rfl rfl) rfl rfl)) (Ns552p1294 rfl) rfl rfl)) 

theorem RS553to564.d67 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 96243326520388967310159 151115727451828646838272 Ns552p1170 Ns552p1171 := Ns552p1295 

noncomputable def Ns552p1296 := nat_lit 93319903186982827802979737 

noncomputable def Ns552p1297 := nat_lit 120548151361787443929578251223040 

noncomputable abbrev qz783 := (Enclosure.sfrac Bool.false 955663 1000)

noncomputable abbrev qz691 := qz783

noncomputable abbrev qz496 := qz691

noncomputable abbrev qz188 := qz496

noncomputable abbrev qz784 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 955663 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz692 := qz784

noncomputable abbrev qz497 := qz692

noncomputable abbrev qz189 := qz497

noncomputable abbrev qz785 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 955663 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz693 := qz785

noncomputable abbrev qz498 := qz693

noncomputable abbrev qz190 := qz498

noncomputable abbrev qz694 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz189 qz9))

noncomputable def Ns552p1298 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (@HMul.hMul Real Real Real qz5 qz694 (Zeta.RiemannSiegel.correction qz190)) 830833485 268435456 274759 268435456 18640812916031183100855 151115727451828646838272 417891206823515603299737 Ns552p1171 Ns552p1297 

noncomputable def Ns552p1299 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin BSN.quadSignPos 11 12 955663 1000 287 536870912 268435456 9007199254740992 Bool.false 1032216848363 4550 1334074092 57 154981288 8 

noncomputable def Ns552p1300 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 955663 1000 176 234 536870912 268435456 9007199254740992 Bool.false 1032216848363 4550 

noncomputable def Ns552p1301 := Ns552p1300 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.false 685193680 221230 Bool.true 741694471 Bool.true 730005134 28296951008113761 1 Bool.false 101014663 Bool.false Bool.false 112470372 Bool.true Bool.false 683226230 

noncomputable def Ns552p1302 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 955663 1000 41 112 536870912 268435456 9007199254740992 Bool.false 1032216848363 4550 

noncomputable def Ns552p1303 := Ns552p1302 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.false 659911298 180668 Bool.true 101460780 Bool.true 656760048 28296951008113761 1 Bool.false 100857903 Bool.true Bool.false 182823114 Bool.false Bool.false 685193680 

noncomputable def Ns552p1304 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 955663 1000 133 40 536870912 268435456 9007199254740992 Bool.false 1032216848363 4550 

noncomputable def Ns552p1305 := Ns552p1304 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.false 677226936 134244 Bool.false 762129866 Bool.false 100689662 28296951008113761 1 Bool.false 530744250 Bool.true Bool.false 527456428 Bool.false Bool.false 659911298 

noncomputable def Ns552p1306 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 955663 1000 380 244 536870912 268435456 9007199254740992 Bool.false 1032216848363 4550 

noncomputable def Ns552p1307 := Ns552p1306 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 450376985 79222 Bool.false 494403448 Bool.false 697484614 28296951008113761 1 Bool.false 324863442 Bool.false Bool.false 144043551 Bool.false Bool.false 677226936 

noncomputable def Ns552p1308 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 955663 1000 802 555 536870912 268435456 9007199254740992 Bool.false 1032216848363 4550 

noncomputable def Ns552p1309 := Ns552p1308 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 536870640 4616 Bool.false 246941353 Bool.false 514664904 28296951008113761 1 Bool.false 481073074 Bool.true Bool.false 439380375 Bool.false Bool.false 450376985 

noncomputable def Ns552p1310 := nat_lit 237461022144709767763369481428817035391782339285213586499553 

noncomputable def Ns552p1311 := nat_lit 123506912065465705272409961959578667563982295824072704000 

noncomputable def Ns552p1312 := nat_lit 382618000862252637061716349380640000 

noncomputable def Ns552p1313 := nat_lit 2193923479606953202257279435364599385920 

noncomputable abbrev qz695 := (@Eq.refl Real qz783)

noncomputable abbrev qz499 := qz695

noncomputable abbrev qz191 := qz499

noncomputable def Ns552p1314 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz188 955663 1000 3653168078276 16000000 1911326 4000 2000 Ns552p1312 Ns552p1313 qz191 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p1315 := nat_lit 75987527086307125684278234057221451325370348571268347679856960 

noncomputable abbrev qz696 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1911326))))

noncomputable abbrev qz500 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 955663 4000) (Real.log (Enclosure.sfrac Bool.false 3653168078276 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz696))

noncomputable abbrev qz697 := (Enclosure.sfrac Bool.false 955663 2000)

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz500 qz697) (@HMul.hMul Real Real Real qz355 qz697 (Real.log Real.pi)))

noncomputable def Ns552p1316 := @Enclosure.Real.IsNear.addLit_ft_p qz192 (Enclosure.sfrac Bool.true Ns552p1312 Ns552p1313) 34635453189348984989513 18014398509481984000 133420921471615845001 Ns552p244 Ns552p1312 Ns552p1313 0 1 Ns552p1315 

noncomputable def Ns552p1317 := nat_lit 2324345917662387282199269343232000 

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz359 qz500 qz697)

noncomputable def Ns552p1318 := @Enclosure.Real.IsNear.subLit_ff_p qz193 (@HMul.hMul Real Real Real qz5 qz697 (Real.log Real.pi)) 44489112944321309026121 18014398509481984000 12045803113146931 3844000000000000000000 36707743089543 67108864000 2866989 536870912000 Ns552p1317 34635453189348984989513 18014398509481984000 

noncomputable def Ns552p1319 := nat_lit 88978225888642618052242000 

noncomputable abbrev qz194 := qz500

noncomputable def Ns552p1320 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz697 53096960005704849663817 18014398509481984000 12045803113146931 3844000000000000000000 955663 2000 0 1 Ns552p1319 44489112944321309026121 18014398509481984000 12045803113146931 3844000000000000000000 

noncomputable def Ns552p1321 := nat_lit 119563724648099245056165470288652271616 

noncomputable def Ns552p1322 := nat_lit 119330810255049576448786432 

noncomputable def Ns552p1323 := nat_lit 87608728256022414102130896669677958184084660179100677307144397659860076888628871808276715411085650523111414137085624087811523927572295569406642243392145977512644324426941191365748326400 

noncomputable def Ns552p1324 := nat_lit 2237462255871271727947837887525829503709419136211697851747446730362077483638252235727323017772005430726663733265895893737081716865981350513862131446785237614171240528101624667533475840 

noncomputable def Ns552p1325 := nat_lit 65912072751540741715482202325875523860787719472231146954765853037331517247371055318953726739550392841392992628279146642264570727750437282772824702403968876331498285437823221760 

noncomputable def Ns552p1326 := BSN.log_dyadic_bound 1556016078276 5750320078276 8 7 Ns552p1323 268435456 76880000 Ns552p1324 Ns552p1325 148985576 7306336156552 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1556016078276) (BSN.artanhQ 5750320078276) 0 7 Ns552p1324 Ns552p1323 Ns552p1325 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz501 := (Real.log (Enclosure.sfrac Bool.false 3653168078276 16000000))

noncomputable def Ns552p1327 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 955663 4000) qz501 955663 4000 0 1 55567738718841959 4503599627370496 12500016337 961000000000000000 53104031887264663063817 18014398509481984000 11945803112666431 3844000000000000000000 (Enclosure.Real.IsNear.const Bool.false 955663 4000) (BSN.isNear_log_sfrac 3653168078276 16000000 55567738718841959 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3653168078276) qz362)) Bool.false Ns552p1322 Ns552p114 1000001306960000 76880000000000000000000 55567738718841959 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3653168078276 16000000 17 7306336156552 4194304000000 148985576 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p1326 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1328 := BSN.arctan_dyadic_bound_f 1000 1911326 1 0 33554432 9610000 0 1 1 0 1 1 17555 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1911326) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1911326) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p1329 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1911326))) 884279719003555 562949953421312 1 2000000000000000 17555 33554432 1 9610000 29661621113851582873600 883985194976675 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p1328 rfl) rfl rfl 

noncomputable abbrev qz502 := (@HMul.hMul Real Real Real qz584 qz589 qz696)

noncomputable abbrev qz195 := qz502

noncomputable abbrev qz503 := qz696

noncomputable abbrev qz196 := qz503

noncomputable def Ns552p1330 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 955663 4000) qz501) qz195 53104031887264663063817 18014398509481984000 11945803112666431 3844000000000000000000 883985194976675 2251799813685248 200000000961 7688000000000000000 Ns552p1321 53096960005704849663817 18014398509481984000 12045803113146931 3844000000000000000000 (Ns552p1327 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz196 1 4 0 1 883985194976675 562949953421312 200000000961 1922000000000000000 883985194976675 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p1329 rfl) 

noncomputable def Ns552p1331 := @Ns552p1316 Ns552p1310 Ns552p1311 133420921471615845001 Ns552p244 (@Ns552p1318 133420921471615845001 Ns552p244 (Ns552p1320 (Ns552p1330 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 955663 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz697 (Real.log Real.pi) 955663 2000 0 1 38410761 33554432 3 268435456 36707743089543 67108864000 2866989 536870912000 (Enclosure.Real.IsNear.const Bool.false 955663 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p1312 Ns552p1313) 

noncomputable def Ns552p1332 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns552p1310 Ns552p1311 133420921471615845001 Ns552p244 129027106045 67108864 285 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz370 qz192 (Enclosure.sfrac Bool.true Ns552p1312 Ns552p1313)) Bool.false Ns552p1310 Ns552p1311 133420921471615845001 Ns552p244 Ns552p1314 (Ns552p1331 rfl rfl)) 

noncomputable def Ns552p1333 := nat_lit 15182153529607487729172480 

noncomputable def Ns552p1334 := nat_lit 14343781348100647667262171224669363675033108627240985407250608950626109360988337216264303036416663643701073767749412661695230033701961649673121 

noncomputable def Ns552p1335 := nat_lit 10172857019400923741132224030879547145842140016844467213237160815252811822932351397116423840619887588812945956037128647329261806236783521 

noncomputable def Ns552p1336 := nat_lit 71630013170825902705880515049011189519628387601998475658616792461247719901740180517184071111622419385014489343409157565266087225258761660978081 

noncomputable def Ns552p1337 := BSN.sin_dyadic_bound_f 215751378073 137438953472 4 3 67108864 19238770 Ns552p1334 Ns552p566 Ns552p1335 Ns552p1336 Ns552p569 Ns552p1335 67108830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215751378073) qz635 0 3 Ns552p1334 Ns552p566 Ns552p1335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215751378073) qz636 0 3 Ns552p1336 Ns552p569 Ns552p1335 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1338 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz188) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 129027106045) qz380) Bool.false 129027106045 67108864 285 33554432 Bool.false 67108830 67108864 1 9610000 (Ns552p1332 rfl) (Enclosure.sfrac_false_div 129027106045 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 129027106045) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns552p1333) qz394) 226375608064910080 72057594037927936 Bool.false 67108830 67108864 305 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q3 129027106045 67108864 226375608064910080 72057594037927936 305 Ns552p1333 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108830 67108864 Ns552p1333 Ns552p114 215751378073 137438953472 19238770 19220000 (Ns552p1337 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1339 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns552p1310 Ns552p1311 133420921471615845001 Ns552p244 1032216848363 536870912 4550 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz370 qz192 (Enclosure.sfrac Bool.true Ns552p1312 Ns552p1313)) Bool.false Ns552p1310 Ns552p1311 133420921471615845001 Ns552p244 Ns552p1314 (Ns552p1331 rfl rfl)) 

noncomputable def Ns552p1340 := Ns552p1309 79222 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 802 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 481073074 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 555 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 439380375 536870912) qz191 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) Bool.false 33554415 33554432 173275277 20153630720000 536870640 536870912 4616 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 33554415 33554432 173275277 20153630720000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz188) qz188) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 67108830 67108864 2772404432 322458091520000 33554415 33554432 173275277 20153630720000 (Ns552p1338 rfl rfl) rfl)) rfl) (Ns552p1339 rfl) RS553to564.d7 

noncomputable def Ns552p1341 := nat_lit 519009901088249377554122097480142880195868550389884995906346960336639041 

noncomputable def Ns552p1342 := nat_lit 13827720311539104028471300275218805429441935190653267877361263236161 

noncomputable def Ns552p1343 := nat_lit 1557002047824125054454309349839878202976746767299273681183286158483444801 

noncomputable def Ns552p1344 := BSN.cos_dyadic_bound_f 246941353 536870912 3 2 536870912 268435456 Ns552p1341 Ns552p140 Ns552p1342 Ns552p1343 Ns552p143 Ns552p1342 481073074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 246941353) qz373 0 2 Ns552p1341 Ns552p140 Ns552p1342 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 246941353) qz374 0 2 Ns552p1343 Ns552p143 Ns552p1342 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1345 := nat_lit 17631155321735902574008173743225956934272360333242380604160775354968965120 

noncomputable def Ns552p1346 := nat_lit 4922621350552963515546971156787645092714648079569247419400807656718336 

noncomputable def Ns552p1347 := nat_lit 46168865408074087657662902802766516735801310490172646610313477002998317056 

noncomputable def Ns552p1348 := BSN.sin_dyadic_bound_f 514664904 536870912 3 2 536870912 268435456 Ns552p1345 Ns552p130 Ns552p1346 Ns552p1347 Ns552p133 Ns552p1346 439380375 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 514664904) qz371 0 2 Ns552p1345 Ns552p130 Ns552p1346 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 514664904) qz372 0 2 Ns552p1347 Ns552p133 Ns552p1346 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1349 := nat_lit 8342584621548855449349538990310164890210704497989616668146391635130843136 

noncomputable def Ns552p1350 := nat_lit 3569866103117401113378563750532561334862016349687224290531409664147456 

noncomputable def Ns552p1351 := nat_lit 25020614132440331545821859843429429547962389461269475555858112086064234496 

noncomputable def Ns552p1352 := BSN.cos_dyadic_bound_f 494403448 536870912 3 2 536870912 268435456 Ns552p1349 Ns552p140 Ns552p1350 Ns552p1351 Ns552p143 Ns552p1350 324863442 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 494403448) qz373 0 2 Ns552p1349 Ns552p140 Ns552p1350 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 494403448) qz374 0 2 Ns552p1351 Ns552p143 Ns552p1350 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1353 := nat_lit 32655717528566218462017520007403192435077634651123896952202634883083736724584689818084859225669192008031145496576 

noncomputable def Ns552p1354 := nat_lit 13256094212351350660517587377776013048141269084510926807775088698712452362796841285637144731264438657028096 

noncomputable def Ns552p1355 := nat_lit 197887706401136974206456735419874278010369328461183675989913747790892505759420188697332221317844351870791154339840 

noncomputable def Ns552p1356 := BSN.cos_dyadic_bound_f 697484614 536870912 4 3 536870912 268435456 Ns552p1353 Ns552p151 Ns552p1354 Ns552p1355 Ns552p154 Ns552p1354 144043551 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 697484614) qz373 0 3 Ns552p1353 Ns552p151 Ns552p1354 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 697484614) qz374 0 3 Ns552p1355 Ns552p154 Ns552p1354 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1357 := Ns552p1307 134244 BSN.abs_quadSignPos (BSN.cos_quad_nat0 380 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 324863442 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 244 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 144043551 536870912) qz191 rfl rfl (Ns552p1340 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p1344 rfl rfl) (Ns552p1348 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p1339 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p1352 rfl rfl) (Ns552p1356 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p1358 := nat_lit 120992085707589851214409287009392833892870777925296419138522098873941386462599078275953462393912473597586852089856 

noncomputable def Ns552p1359 := nat_lit 38401463046626746188985432919917099750987267018821946118301554832676031748193379798214680838347597433081856 

noncomputable def Ns552p1360 := nat_lit 604458724210497936452727766522335868115613038792276540755201210231446063359860419224756584201697971978106204655616 

noncomputable def Ns552p1361 := BSN.sin_dyadic_bound_f 762129866 536870912 4 3 536870912 268435456 Ns552p1358 Ns552p177 Ns552p1359 Ns552p1360 Ns552p180 Ns552p1359 530744250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 762129866) qz371 0 3 Ns552p1358 Ns552p177 Ns552p1359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 762129866) qz372 0 3 Ns552p1360 Ns552p180 Ns552p1359 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1362 := nat_lit 102787317457270450661058708971536 

noncomputable def Ns552p1363 := BSN.cos_dyadic_bound_f 100689662 536870912 2 1 536870912 268435456 Ns552p1362 Ns552p157 Ns552p1362 Ns552p1362 Ns552p158 Ns552p1362 527456428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 100689662) qz373 0 1 Ns552p1362 Ns552p157 Ns552p1362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 100689662) qz374 0 1 Ns552p1362 Ns552p158 Ns552p1362 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1364 := Ns552p1305 180668 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530744250 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 527456428 536870912) qz191 rfl rfl (Ns552p1357 rfl rfl) (Ns552p1339 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p1361 rfl rfl) (Ns552p1363 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1365 := nat_lit 105972404096583914905193830560000 

noncomputable def Ns552p1366 := BSN.sin_dyadic_bound_f 101460780 536870912 2 1 536870912 268435456 Ns552p1365 Ns552p283 Ns552p1365 Ns552p1365 Ns552p284 Ns552p1365 100857903 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 101460780) qz371 0 1 Ns552p1365 Ns552p283 Ns552p1365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 101460780) qz372 0 1 Ns552p1365 Ns552p284 Ns552p1365 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1367 := nat_lit 25661986299819607373023128056464344148376768795356838748442959767806593252716568083867559300587914680576063307776 

noncomputable def Ns552p1368 := nat_lit 6439923541159942670436500534941747678491426651905637084392730235892268773807867021504546825777354737975296 

noncomputable def Ns552p1369 := nat_lit 155544515891346769665306601015257041001085457277793436660123283860306940476755898085247541267256175508431558410240 

noncomputable def Ns552p1370 := BSN.cos_dyadic_bound_f 656760048 536870912 4 3 536870912 268435456 Ns552p1367 Ns552p151 Ns552p1368 Ns552p1369 Ns552p154 Ns552p1368 182823114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 656760048) qz373 0 3 Ns552p1367 Ns552p151 Ns552p1368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 656760048) qz374 0 3 Ns552p1369 Ns552p154 Ns552p1368 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1371 := Ns552p1303 221230 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 100857903 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 182823114 536870912) qz191 rfl rfl (Ns552p1364 rfl) (Ns552p1339 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p1366 rfl rfl) (Ns552p1370 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1372 := nat_lit 41775899984952345972652211976489654827648657263006495470523271885328380540743275971676556280480706888352339621921 

noncomputable def Ns552p1373 := nat_lit 27714082065143641956406953884685248093121185773182074712419805954044509707063100585451443866912946455083041 

noncomputable def Ns552p1374 := nat_lit 253074762457247638025726608122970043021965941316214119072152197879108078286983605324806590295759994689107553974305 

noncomputable def Ns552p1375 := BSN.cos_dyadic_bound_f 741694471 536870912 4 3 536870912 268435456 Ns552p1372 Ns552p151 Ns552p1373 Ns552p1374 Ns552p154 Ns552p1373 101014663 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 741694471) qz373 0 3 Ns552p1372 Ns552p151 Ns552p1373 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 741694471) qz374 0 3 Ns552p1374 Ns552p154 Ns552p1373 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1376 := nat_lit 39198677837488745295177965291838617749307130006301191953680788148494215454360024969319227379934856568304454209536 

noncomputable def Ns552p1377 := nat_lit 22903980928619038408747970859282853887710851539790691472462600716399806750383459122954075518544372263161856 

noncomputable def Ns552p1378 := nat_lit 237483265664766474889144689645779488052747524692475574764646393801361768773729637978150036248865662043184291778560 

noncomputable def Ns552p1379 := BSN.cos_dyadic_bound_f 730005134 536870912 4 3 536870912 268435456 Ns552p1376 Ns552p151 Ns552p1377 Ns552p1378 Ns552p154 Ns552p1377 112470372 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 730005134) qz373 0 3 Ns552p1376 Ns552p151 Ns552p1377 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 730005134) qz374 0 3 Ns552p1378 Ns552p154 Ns552p1377 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1380 := Ns552p1301 257710 BSN.abs_quadSignPos (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 101014663 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 112470372 536870912) qz191 rfl rfl (Ns552p1371 rfl) (Ns552p1339 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p1375 rfl rfl) (Ns552p1379 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1381 := nat_lit 75313056956078018658301453647744272875191018958857785404701859128516309001817058165337745779805910722837898540625 

noncomputable def Ns552p1382 := nat_lit 9275712169386405659480683045156683393585259464235559150989436475170750443324121722784549024898750244140625 

noncomputable def Ns552p1383 := nat_lit 376370720095644257987162159319170533583854897083518693973016103493531734874622764179273275083341387207284516140625 

noncomputable def Ns552p1384 := BSN.sin_dyadic_bound_f 677036795 536870912 4 3 536870912 268435456 Ns552p1381 Ns552p177 Ns552p1382 Ns552p1383 Ns552p180 Ns552p1382 511326516 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 677036795) qz371 0 3 Ns552p1381 Ns552p177 Ns552p1382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 677036795) qz372 0 3 Ns552p1383 Ns552p180 Ns552p1382 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1385 := Ns552p1299 Bool.false 683226230 257710 Bool.true 677036795 28296951008113761 1 Bool.false 511326516 Bool.false Bool.false 830833485 274759 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 511326516 536870912) qz191 rfl (Ns552p1380 rfl) (Ns552p1339 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p1384 rfl rfl) rfl 

noncomputable def Ns552p1386 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) 830833485 536870912 274759 536870912 830833485 536870912 274759 536870912 892100661624176640 830833485 268435456 274759 268435456 (Ns552p1385 rfl rfl rfl rfl) 

noncomputable def Ns552p1387 := @Enclosure.Real.IsNear.mulLit_ff qz694 (Zeta.RiemannSiegel.correction qz190) 19109471 67108864 1 67108864 975475088558505 2251799813685248 10918808015691123 676243631547351040000 18640812916031183100855 151115727451828646838272 

noncomputable abbrev qz698 := (@HPow.hPow Real Real Real qz7 qz189 qz9)

noncomputable def Ns552p1388 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz698 1 1 0 1 19109471 67108864 1 67108864 19109471 67108864 1 67108864 

noncomputable def Ns552p1389 := @Enclosure.Real.IsNear.sqrt_image qz189 10207156493741 67108864000 955663 67108864000 413820798 413820838 33554432 (@Enclosure.Real.IsNear.of_eq qz189 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 10207156493741 67108864000 955663 67108864000 (BSN.t_div_two_pi_mk qz188 955663 1000 qz191) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 955663 1000 0 1 10680707 67108864 1 67108864 10207156493741 67108864000 955663 67108864000 (Enclosure.Real.IsNear.const Bool.false 955663 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz786 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 955663 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz699 := qz786

noncomputable abbrev qz504 := qz699

noncomputable abbrev qz197 := qz504

noncomputable def Ns552p1390 := @Enclosure.Real.IsNear.sqrt_image qz197 206910409 16777216 5 8388608 117836844 117836850 33554432 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 827641636 67108864 40 67108864 206910409 16777216 5 8388608 (Ns552p1389 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p1391 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz197) 117836847 33554432 3 33554432 9554735 9554736 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz197) Bool.false 235673694 67108864 6 67108864 117836847 33554432 3 33554432 (Ns552p1390 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p1392 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 19109471 67108864 1 67108864 19109471 67108864 1 67108864 (Ns552p1391 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz505 := (@HMul.hMul Real Real Real qz584 qz582 qz693)

noncomputable abbrev qz198 := (Real.cos qz505)

noncomputable abbrev qz700 := (@HMul.hMul Real Real Real qz742 qz785 qz785)

noncomputable abbrev qz506 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz700 qz693) qz603)

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz506))

noncomputable def Ns552p1393 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz190) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz198) qz199) Bool.false 975475088558505 

noncomputable def Ns552p1394 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz198) qz199 134970345 67108864 1053 

noncomputable abbrev qz200 := (@Neg.neg Real Real.instNeg (Real.cos qz505))

noncomputable def Ns552p1395 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz198) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz200)) Bool.true 134970345 67108864 1053 67108864 (BSN.inv_eq_neg_inv_neg qz198) 

noncomputable def Ns552p1396 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz200) Bool.false 134970345 67108864 1053 67108864 134970345 67108864 

noncomputable def Ns552p1397 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 33367327 67108864 2498438864 644916183040000 33367327 67108864 156152429 40307261440000 

noncomputable abbrev qz201 := qz505

noncomputable def Ns552p1398 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 140336627) qz380) Bool.false 140336627 67108864 253 67108864 Bool.true 33367327 67108864 1 

noncomputable def Ns552p1399 := nat_lit 134930377069202538677693667 

noncomputable def Ns552p1400 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz190 884279719003555 140737488355328 1 500000000000000 5583817 16777216 5 8388608 4937656127727273469435 2361183241434822606848 Ns552p1399 

noncomputable def Ns552p1401 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz1 206910409 16777216 5 8388608 12 1 0 1 5583817 5583817 16777216 5 

noncomputable def Ns552p1402 := @Ns552p1401 8388608 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 827641636 67108864 40 67108864 206910409 16777216 5 8388608 (Ns552p1389 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p1403 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 4937656127727273469435 2361183241434822606848 Ns552p1399 Ns552p495 140336627 67108864 253 67108864 (@Ns552p1400 Ns552p495 RS553to564.d55 (Ns552p1402 rfl rfl) rfl) 

noncomputable def Ns552p1404 := nat_lit 5032829499490879483674624 

noncomputable def Ns552p1405 := nat_lit 26165537999860064432889487629293519461518241 

noncomputable def Ns552p1406 := BSN.sin_dyadic_bound_f 71520808823 137438953472 2 1 67108864 19238770 Ns552p1405 Ns552p1274 Ns552p1405 Ns552p1405 Ns552p1275 Ns552p1405 33367327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 71520808823) qz635 0 1 Ns552p1405 Ns552p1274 Ns552p1405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 71520808823) qz636 0 1 Ns552p1405 Ns552p1275 Ns552p1405 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1407 := @Ns552p1398 9610000 (Ns552p1403 rfl) (Enclosure.sfrac_false_div 140336627 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 140336627) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns552p1404) qz394) 226375608064910080 72057594037927936 Bool.false 33367327 67108864 0 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q1 140336627 67108864 226375608064910080 72057594037927936 0 Ns552p1404 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 33367327 67108864 Ns552p1404 Ns552p114 71520808823 137438953472 19238770 19220000 (Ns552p1406 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1408 := @Enclosure.Real.IsNear.inv_image qz200 33367327 67108864 156152429 40307261440000 67484646 67485699 33554432 (@Enclosure.Real.IsNear.neg qz198 Bool.true 33367327 67108864 156152429 40307261440000 (Ns552p1397 (Ns552p1407 rfl rfl) rfl)) 

noncomputable def Ns552p1409 := Ns552p1395 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz200) Bool.false 134970345 67108864 1053 67108864 (@Ns552p1396 1053 67108864 (Ns552p1408 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1410 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 7227329 33554432 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz355 qz352 qz506)

noncomputable def Ns552p1411 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 29995795)) qz677) Bool.true 29995795 16777216 

noncomputable def Ns552p1412 := nat_lit 70825568494460777345992158445 

noncomputable def Ns552p1413 := nat_lit 39614081257132168796771975168 

noncomputable def Ns552p1414 := nat_lit 942652624154973591145180733369301 

noncomputable def Ns552p1415 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns552p1412 Ns552p1413 Ns552p1414 

noncomputable def Ns552p1416 := nat_lit 151115727451828646838272000000000000000 

noncomputable abbrev qz203 := qz506

noncomputable def Ns552p1417 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 80094077668399 

noncomputable abbrev qz507 := (@HSub.hSub Real Real Real qz588 qz700 qz693)

noncomputable abbrev qz204 := qz507

noncomputable def Ns552p1418 := @Enclosure.Real.IsNear.subLit_tf qz204 qz31 62501891623983 281474976710656 34931075 35184372088832 1 16 

noncomputable abbrev qz508 := qz700

noncomputable abbrev qz205 := qz508

noncomputable def Ns552p1419 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz190 31179012289489 281474976710656 13959555 35184372088832 5583817 16777216 5 8388608 

noncomputable def Ns552p1420 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 5583817 16777216 5 8388608 5583817 16777216 5 8388608 31179012289489 281474976710656 

noncomputable def Ns552p1421 := nat_lit 102038031578138431579287400159943076961911813528346168524590089346410199814707636216483975640625 

noncomputable def Ns552p1422 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600 

noncomputable def Ns552p1423 := nat_lit 530547805026024251968278466170937550342205639531471422908605410783107952015981367431640625 

noncomputable def Ns552p1424 := nat_lit 616533224287176292853054753591830328715767406306310918903232999123151871542427430685829665240625 

noncomputable def Ns552p1425 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600 

noncomputable def Ns552p1426 := BSN.cos_dyadic_bound_t 29995795 16777216 4 3 33554432 9610000 Ns552p1421 Ns552p1422 Ns552p1423 Ns552p1424 Ns552p1425 Ns552p1423 7227329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 29995795) (BSN.cosEvenQ 16777216) 0 3 Ns552p1421 Ns552p1422 Ns552p1423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 29995795) (BSN.cosOddQ 16777216) 0 3 Ns552p1424 Ns552p1425 Ns552p1423 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1427 := @Ns552p1410 4093698864 644916183040000 7227329 33554432 255856179 40307261440000 (@Ns552p1411 419 67108864 Bool.true 7227329 33554432 1 9610000 (@Ns552p1415 Ns552p1416 29995795 16777216 419 67108864 (@Ns552p1417 281474976710656 34931075 35184372088832 Ns552p1412 Ns552p1413 Ns552p1414 Ns552p1416 RS553to564.d55 (@Ns552p1418 0 1 1281505242694384 80094077668399 281474976710656 34931075 35184372088832 (@Ns552p1419 1048607736184153571328 62501891623983 281474976710656 34931075 35184372088832 (@Ns552p1420 13959555 35184372088832 (Ns552p1402 rfl rfl) (Ns552p1402 rfl rfl) rfl) (Ns552p1402 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 29995795 16777216) (BSN.cos_neg_of_bound 29995795 16777216 Bool.true 7227329 33554432 1 9610000 (Ns552p1426 rfl rfl)) rfl rfl) 

noncomputable def Ns552p1428 := @Ns552p1387 417891206823515603299737 Ns552p1171 (Ns552p1388 qz33 (@Enclosure.Real.IsNear.of_eq qz698 (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 19109471 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz189 (BSN.t_div_two_pi_nonneg qz188 955663 1000 qz191)) Ns552p1392) rfl) (@Ns552p1393 2251799813685248 10918808015691123 676243631547351040000 (BSN.correction_mk qz190 (BSN.cos_two_pi_p_ne_zero_mk qz188 955663 1000 12 qz191 rfl rfl (@BSN.floor_sqrt_eq_dec qz188 955663 1000 12 qz191 rfl rfl rfl))) (@Ns552p1394 67108864 7227329 33554432 255856179 40307261440000 975475088558505 2251799813685248 10918808015691123 676243631547351040000 Ns552p1409 (Ns552p1427 rfl) rfl)) 

noncomputable def Ns552p1429 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (hardyZApproximantRS₀ qz188) Bool.false 449076858765585139131465 151115727451828646838272 Ns552p1296 Ns552p1171 (@Eq.refl Real (hardyZApproximantRS₀ qz188)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (@HMul.hMul Real Real Real qz5 qz694 (Zeta.RiemannSiegel.correction qz190))) Bool.false 449076858765585139131465 151115727451828646838272 Ns552p1296 Ns552p1171 (BSN.hardyZApproximantRS₀_eq qz188 12 (@BSN.floor_sqrt_eq_dec qz188 955663 1000 12 qz191 rfl rfl rfl)) (@Ns552p1298 449076858765585139131465 151115727451828646838272 Ns552p1296 Ns552p1171 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12)) Bool.false 830833485 268435456 274759 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (Ns552p1386 (Ns552p1385 rfl rfl rfl rfl) rfl rfl)) (Ns552p1428 rfl) rfl rfl)) 

theorem RS553to564.d68 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz188) Bool.false 449076858765585139131465 151115727451828646838272 Ns552p1296 Ns552p1171 := Ns552p1429 

noncomputable def Ns552p1430 := nat_lit 11676238587174028746020763 

noncomputable def Ns552p1431 := nat_lit 2752189916228331353491860619264 

noncomputable abbrev qz787 := (Enclosure.sfrac Bool.false 956914 1000)

noncomputable abbrev qz701 := qz787

noncomputable abbrev qz509 := qz701

noncomputable abbrev qz206 := qz509

noncomputable abbrev qz788 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 956914 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz702 := qz788

noncomputable abbrev qz510 := qz702

noncomputable abbrev qz207 := qz510

noncomputable abbrev qz789 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 956914 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz703 := qz789

noncomputable abbrev qz511 := qz703

noncomputable abbrev qz208 := qz511

noncomputable abbrev qz704 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz207 qz9))

noncomputable def Ns552p1432 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HMul.hMul Real Real Real qz5 qz704 (Zeta.RiemannSiegel.correction qz208)) 112971963 268435456 68779 67108864 2303011230854587934437 18889465931478580854784 48398403625214450980763 Ns552p86 Ns552p1431 

noncomputable def Ns552p1433 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin BSN.quadSignPos 11 12 956914 1000 287 536870912 268435456 9007199254740992 Bool.false 1033904368681 4557 1334074092 57 154981288 8 

noncomputable def Ns552p1434 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 956914 1000 176 234 536870912 268435456 9007199254740992 Bool.false 1033904368681 4557 

noncomputable def Ns552p1435 := Ns552p1434 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 276810722 221517 Bool.true 600649039 Bool.true 652972451 28296951008113761 1 Bool.false 234486871 Bool.false Bool.false 186379755 Bool.true Bool.true 258855068 

noncomputable def Ns552p1436 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 956914 1000 40 112 536870912 268435456 9007199254740992 Bool.false 1033904368681 4557 

noncomputable def Ns552p1437 := Ns552p1436 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 463344893 180902 Bool.true 653861305 Bool.true 444951791 28296951008113761 1 Bool.false 185545927 Bool.false Bool.false 362801340 Bool.false Bool.true 276810722 

noncomputable def Ns552p1438 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 956914 1000 134 40 536870912 268435456 9007199254740992 Bool.false 1033904368681 4557 

noncomputable def Ns552p1439 := Ns552p1438 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 429753442 134416 Bool.false 402943968 Bool.false 481287101 28296951008113761 1 Bool.false 392624203 Bool.true Bool.false 335207976 Bool.false Bool.true 463344893 

noncomputable def Ns552p1440 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 956914 1000 381 245 536870912 268435456 9007199254740992 Bool.false 1033904368681 4557 

noncomputable def Ns552p1441 := Ns552p1440 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 63322850 79321 Bool.false 407538269 Bool.false 460750535 28296951008113761 1 Bool.false 369511186 Bool.true Bool.false 406237651 Bool.true Bool.true 429753442 

noncomputable def Ns552p1442 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 956914 1000 803 556 536870912 268435456 9007199254740992 Bool.false 1033904368681 4557 

noncomputable def Ns552p1443 := Ns552p1442 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870792 4616 Bool.false 625611504 Bool.false 621014332 28296951008113761 1 Bool.false 493332644 Bool.false Bool.false 216002466 Bool.false Bool.true 63322850 

noncomputable def Ns552p1444 := nat_lit 1872839707527520764789333072055550007149842279836330102587 

noncomputable def Ns552p1445 := nat_lit 972501125120570117445564355836210871901025806057472000 

noncomputable def Ns552p1446 := nat_lit 385128874378862418418667915115520000 

noncomputable def Ns552p1447 := nat_lit 2211211551913425222313809071775292231680 

noncomputable abbrev qz790 := (@Eq.refl Real (Enclosure.sfrac Bool.false 956914 1000))

noncomputable abbrev qz705 := qz790

noncomputable abbrev qz512 := qz705

noncomputable abbrev qz209 := qz512

noncomputable def Ns552p1448 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 956914 1000 3662738613584 16000000 1913828 4000 2000 Ns552p1446 Ns552p1447 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p1449 := nat_lit 38355757210163625262885541315697664146428769891048040500981760 

noncomputable abbrev qz706 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1913828))))

noncomputable abbrev qz513 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 956914 4000) (Real.log (Enclosure.sfrac Bool.false 3662738613584 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz706))

noncomputable abbrev qz707 := (Enclosure.sfrac Bool.false 956914 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz513 qz707) (@HMul.hMul Real Real Real qz355 qz707 (Real.log Real.pi)))

noncomputable def Ns552p1450 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns552p1446 Ns552p1447) 17346038485510709277007 9007199254740992000 66797519229836952239 Ns552p410 Ns552p1446 Ns552p1447 0 1 Ns552p1449 

noncomputable def Ns552p1451 := nat_lit 582036468831452079707100545024000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz359 qz513 qz707)

noncomputable def Ns552p1452 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz707 (Real.log Real.pi)) 22279317774742157226319 9007199254740992000 6030720316792259 1922000000000000000000 18377897475777 33554432000 1435371 268435456000 Ns552p1451 17346038485510709277007 9007199254740992000 

noncomputable def Ns552p1453 := nat_lit 44558635549484314452638000 

noncomputable abbrev qz212 := qz513

noncomputable def Ns552p1454 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz707 26588875308567768035663 9007199254740992000 6030720316792259 1922000000000000000000 956914 2000 0 1 Ns552p1453 22279317774742157226319 9007199254740992000 6030720316792259 1922000000000000000000 

noncomputable def Ns552p1455 := nat_lit 59872824465933190987978766641920999424 

noncomputable def Ns552p1456 := nat_lit 119356114179915920317612032 

noncomputable def Ns552p1457 := nat_lit 89672320026480162238826295485601355406208287433369208928285696905463492645248325430472501450047076544522293141116039661768472372584971045662668749984965172478388962915946530372740710400 

noncomputable def Ns552p1458 := nat_lit 2311696554763926944398291198818624917727457087362083028623527386463618902163573659235871585208794432902852203304864800295805842559529190718200282195847036162257175511568199920637706240 

noncomputable def Ns552p1459 := nat_lit 71820303446090545026869873066928939038832889619765845285895480651177038437074305837907845347357058416576170657517759194069654970372401285781773223582752570202221818345276047360 

noncomputable def Ns552p1460 := BSN.log_dyadic_bound 1565586613584 5759890613584 8 7 Ns552p1457 268435456 76880000 Ns552p1458 Ns552p1459 149687901 7325477227168 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1565586613584) (BSN.artanhQ 5759890613584) 0 7 Ns552p1458 Ns552p1457 Ns552p1459 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz514 := (Real.log (Enclosure.sfrac Bool.false 3662738613584 16000000))

noncomputable def Ns552p1461 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 956914 4000) qz514 956914 4000 0 1 55579521777069159 4503599627370496 12500016337 961000000000000000 26592411250891178607663 9007199254740992000 5980720316552009 1922000000000000000000 (Enclosure.Real.IsNear.const Bool.false 956914 4000) (BSN.isNear_log_sfrac 3662738613584 16000000 55579521777069159 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3662738613584) qz362)) Bool.false Ns552p1456 Ns552p114 1000001306960000 76880000000000000000000 55579521777069159 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3662738613584 16000000 17 7325477227168 4194304000000 149687901 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p1460 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1462 := BSN.arctan_dyadic_bound_f 1000 1913828 1 0 33554432 9610000 0 1 1 0 1 1 17532 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1913828) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1913828) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p1463 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1913828))) 884279719003555 562949953421312 1 2000000000000000 17532 33554432 1 9610000 29661634061700511563776 883985580852643 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p1462 rfl) rfl rfl 

noncomputable abbrev qz515 := (@HMul.hMul Real Real Real qz584 qz589 qz706)

noncomputable abbrev qz213 := qz515

noncomputable abbrev qz516 := qz706

noncomputable abbrev qz214 := qz516

noncomputable def Ns552p1464 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 956914 4000) qz514) qz213 26592411250891178607663 9007199254740992000 5980720316552009 1922000000000000000000 883985580852643 2251799813685248 200000000961 7688000000000000000 Ns552p1455 26588875308567768035663 9007199254740992000 6030720316792259 1922000000000000000000 (Ns552p1461 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz214 1 4 0 1 883985580852643 562949953421312 200000000961 1922000000000000000 883985580852643 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p1463 rfl) 

noncomputable def Ns552p1465 := @Ns552p1450 Ns552p1444 Ns552p1445 66797519229836952239 Ns552p410 (@Ns552p1452 66797519229836952239 Ns552p410 (Ns552p1454 (Ns552p1464 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 956914 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz707 (Real.log Real.pi) 956914 2000 0 1 38410761 33554432 3 268435456 18377897475777 33554432000 1435371 268435456000 (Enclosure.Real.IsNear.const Bool.false 956914 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p1446 Ns552p1447) 

noncomputable def Ns552p1466 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns552p1444 Ns552p1445 66797519229836952239 Ns552p410 129238046085 67108864 285 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz370 qz210 (Enclosure.sfrac Bool.true Ns552p1446 Ns552p1447)) Bool.false Ns552p1444 Ns552p1445 66797519229836952239 Ns552p410 Ns552p1448 (Ns552p1465 rfl rfl)) 

noncomputable def Ns552p1467 := BSN.cos_dyadic_bound_f 90770176 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108849 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 90770176) qz595 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 90770176) qz596 0 0 rfl) rfl rfl 

noncomputable def Ns552p1468 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 129238046085) qz380) Bool.false 129238046085 67108864 285 33554432 Bool.true 67108849 67108864 1 9610000 (Ns552p1466 rfl) (Enclosure.sfrac_false_div 129238046085 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 129238046085) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6387383299987210240000) qz394) 226375608064910080 72057594037927936 Bool.false 67108849 67108864 306 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q2 129238046085 67108864 226375608064910080 72057594037927936 306 6387383299987210240000 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108849 67108864 6387383299987210240000 Ns552p114 90770176 137438953472 19238770 19220000 (Ns552p1467 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1469 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns552p1444 Ns552p1445 66797519229836952239 Ns552p410 1033904368681 536870912 4557 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz370 qz210 (Enclosure.sfrac Bool.true Ns552p1446 Ns552p1447)) Bool.false Ns552p1444 Ns552p1445 66797519229836952239 Ns552p410 Ns552p1448 (Ns552p1465 rfl rfl)) 

noncomputable def Ns552p1470 := Ns552p1443 79321 BSN.abs_quadSignPos (BSN.cos_quad_nat3 803 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 493332644 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 556 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 216002466 536870912) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.true 67108849 67108864 173275277 20153630720000 536870792 536870912 4616 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 67108849 67108864 173275277 20153630720000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 67108849 67108864 2772404432 322458091520000 67108849 67108864 173275277 20153630720000 (Ns552p1468 rfl rfl) rfl)) rfl) (Ns552p1469 rfl) RS553to564.d7 

noncomputable def Ns552p1471 := nat_lit 54896130251865613297662052956646283124513750076980390810936027593168896625097454266016034852290767399618311356416 

noncomputable def Ns552p1472 := nat_lit 3594650848013684448997742539955762368817533244174676006213891234542278376907201704324247587089654235529216 

noncomputable def Ns552p1473 := nat_lit 274377236813456024968251117546186461390715780570029939348981964040677428257193773869094797164592008871622660325376 

noncomputable def Ns552p1474 := BSN.sin_dyadic_bound_f 625611504 536870912 4 3 536870912 268435456 Ns552p1471 Ns552p177 Ns552p1472 Ns552p1473 Ns552p180 Ns552p1472 493332644 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 625611504) qz371 0 3 Ns552p1471 Ns552p177 Ns552p1472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 625611504) qz372 0 3 Ns552p1473 Ns552p180 Ns552p1472 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1475 := nat_lit 20509441840716157987369452394196903291897105094276907100808981500726986945407195581546086238523420765242162937856 

noncomputable def Ns552p1476 := nat_lit 3290178629757115193386486112629374259003018255496829022734866360072500472674486497719164259492940035915776 

noncomputable def Ns552p1477 := nat_lit 124335629054601319869148263096080044789134898141930224856466130950398115378898538552916127620616759767041520435200 

noncomputable def Ns552p1478 := BSN.cos_dyadic_bound_f 621014332 536870912 4 3 536870912 268435456 Ns552p1475 Ns552p151 Ns552p1476 Ns552p1477 Ns552p154 Ns552p1476 216002466 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 621014332) qz373 0 3 Ns552p1475 Ns552p151 Ns552p1476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 621014332) qz374 0 3 Ns552p1477 Ns552p154 Ns552p1476 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1479 := nat_lit 6930787026156571641478783820401063956095673762732568041005167671780276385 

noncomputable def Ns552p1480 := nat_lit 760934319150665437301014686540712325843785276269703362523844013947041 

noncomputable def Ns552p1481 := nat_lit 18150829270083824650307851220129339684103969916709432016236114821497190561 

noncomputable def Ns552p1482 := BSN.sin_dyadic_bound_f 407538269 536870912 3 2 536870912 268435456 Ns552p1479 Ns552p130 Ns552p1480 Ns552p1481 Ns552p133 Ns552p1480 369511186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 407538269) qz371 0 2 Ns552p1479 Ns552p130 Ns552p1480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 407538269) qz372 0 2 Ns552p1481 Ns552p133 Ns552p1480 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1483 := nat_lit 11324070861295081137242116161497587581363027024280414941258544834374930625 

noncomputable def Ns552p1484 := nat_lit 2031078857387171409071674136176921145620811045351331219397624687890625 

noncomputable def Ns552p1485 := nat_lit 29654992413813252320019426283892252459810256131422898881321926031011090625 

noncomputable def Ns552p1486 := BSN.sin_dyadic_bound_f 460750535 536870912 3 2 536870912 268435456 Ns552p1483 Ns552p130 Ns552p1484 Ns552p1485 Ns552p133 Ns552p1484 406237651 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 460750535) qz371 0 2 Ns552p1483 Ns552p130 Ns552p1484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 460750535) qz372 0 2 Ns552p1485 Ns552p133 Ns552p1484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1487 := Ns552p1441 134416 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 381 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 369511186 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 245 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 406237651 536870912) qz209 rfl rfl (Ns552p1470 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p1474 rfl rfl) (Ns552p1478 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p1469 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p1482 rfl rfl) (Ns552p1486 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p1488 := nat_lit 3680013710033659534802894428196535144413843271102260063600252711658848256 

noncomputable def Ns552p1489 := nat_lit 694955939103215839477110685754254327326490370104422580660325660491776 

noncomputable def Ns552p1490 := nat_lit 11038651218222772172729729063218096924586876832566571345639437483655561216 

noncomputable def Ns552p1491 := BSN.cos_dyadic_bound_f 402943968 536870912 3 2 536870912 268435456 Ns552p1488 Ns552p140 Ns552p1489 Ns552p1490 Ns552p143 Ns552p1489 392624203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 402943968) qz373 0 2 Ns552p1488 Ns552p140 Ns552p1489 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 402943968) qz374 0 2 Ns552p1490 Ns552p143 Ns552p1489 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1492 := nat_lit 7491565755597320070074601598203523640970578027315632552619442468405989281 

noncomputable def Ns552p1493 := nat_lit 2878947719086964209801617519058673828025942898193382467730493805776801 

noncomputable def Ns552p1494 := nat_lit 22468939371353786281804201559572453575255682196150510892922866417606414241 

noncomputable def Ns552p1495 := BSN.cos_dyadic_bound_f 481287101 536870912 3 2 536870912 268435456 Ns552p1492 Ns552p140 Ns552p1493 Ns552p1494 Ns552p143 Ns552p1493 335207976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 481287101) qz373 0 2 Ns552p1492 Ns552p140 Ns552p1493 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 481287101) qz374 0 2 Ns552p1494 Ns552p143 Ns552p1493 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1496 := Ns552p1439 180902 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 134 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 392624203 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 335207976 536870912) qz209 rfl rfl (Ns552p1487 rfl rfl) (Ns552p1469 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p1491 rfl rfl) (Ns552p1495 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1497 := nat_lit 25211330691554151183923870068327435886923061645007339750094023093106054102437044301186252442183984327306389390625 

noncomputable def Ns552p1498 := nat_lit 6106996104782861514619751865923813959750108253372315979193912825759026843465988589683952867648613525390625 

noncomputable def Ns552p1499 := nat_lit 152815344189176156738546427246025265259217613386049374230991312797942188207650955539451834952170793663710766990625 

noncomputable def Ns552p1500 := BSN.cos_dyadic_bound_f 653861305 536870912 4 3 536870912 268435456 Ns552p1497 Ns552p151 Ns552p1498 Ns552p1499 Ns552p154 Ns552p1498 185545927 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 653861305) qz373 0 3 Ns552p1497 Ns552p151 Ns552p1498 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 653861305) qz374 0 3 Ns552p1499 Ns552p154 Ns552p1498 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1501 := nat_lit 5472207624748480709870795355448519542866550724703481175858595930123318401 

noncomputable def Ns552p1502 := nat_lit 1536397789682054713858980706274228899227416138932567435424075395413121 

noncomputable def Ns552p1503 := nat_lit 16413550078666078020184668104933010170801197341832578392704939639579128961 

noncomputable def Ns552p1504 := BSN.cos_dyadic_bound_f 444951791 536870912 3 2 536870912 268435456 Ns552p1501 Ns552p140 Ns552p1502 Ns552p1503 Ns552p143 Ns552p1502 362801340 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 444951791) qz373 0 2 Ns552p1501 Ns552p140 Ns552p1502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 444951791) qz374 0 2 Ns552p1503 Ns552p143 Ns552p1502 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1505 := Ns552p1437 221517 BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 185545927 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 362801340 536870912) qz209 rfl rfl (Ns552p1496 rfl) (Ns552p1469 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p1500 rfl rfl) (Ns552p1504 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1506 := nat_lit 17946210163836391366596392708194343092429800793818442151071196323917389004730291972289657097451160441384335233601 

noncomputable def Ns552p1507 := nat_lit 2205207387995773312532837908385847984354439396695751789408345756066404238211976589047378539213616597357121 

noncomputable def Ns552p1508 := nat_lit 108806036667930753430059090008552131820997926871668450920936066125578595545268786296981162761636184571699382899265 

noncomputable def Ns552p1509 := BSN.cos_dyadic_bound_f 600649039 536870912 4 3 536870912 268435456 Ns552p1506 Ns552p151 Ns552p1507 Ns552p1508 Ns552p154 Ns552p1507 234486871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 600649039) qz373 0 3 Ns552p1506 Ns552p151 Ns552p1507 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 600649039) qz374 0 3 Ns552p1508 Ns552p154 Ns552p1507 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1510 := nat_lit 25074343590166010714638091311700241964360065355887012961372139130969452683662449554468715695786340557738159866481 

noncomputable def Ns552p1511 := nat_lit 6008115937707772625259422642796396303796505344246521286729494724207501706262074378548510097748274571084401 

noncomputable def Ns552p1512 := nat_lit 151985733082775163356875820611712305910271702093193633160401713093041240353054173043335834211397265591535133491825 

noncomputable def Ns552p1513 := BSN.cos_dyadic_bound_f 652972451 536870912 4 3 536870912 268435456 Ns552p1510 Ns552p151 Ns552p1511 Ns552p1512 Ns552p154 Ns552p1511 186379755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 652972451) qz373 0 3 Ns552p1510 Ns552p151 Ns552p1511 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 652972451) qz374 0 3 Ns552p1512 Ns552p154 Ns552p1511 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1514 := Ns552p1435 258045 BSN.abs_quadSignPos (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 234486871 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 186379755 536870912) qz209 rfl rfl (Ns552p1505 rfl) (Ns552p1469 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p1509 rfl rfl) (Ns552p1513 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1515 := nat_lit 67368379119762129756080372804831758085087699826273042921274539643927976103934443455099364756857420122234045075456 

noncomputable def Ns552p1516 := nat_lit 6640786739822649631637548631612638251420232083309693789829247051171422062540650525167430493062162825875456 

noncomputable def Ns552p1517 := nat_lit 336686190274063526248830195262053610748144774793837146306889588481133141642281007271689646998437393880491256713216 

noncomputable def Ns552p1518 := BSN.sin_dyadic_bound_f 658443166 536870912 4 3 536870912 268435456 Ns552p1515 Ns552p177 Ns552p1516 Ns552p1517 Ns552p180 Ns552p1516 505353884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 658443166) qz371 0 3 Ns552p1515 Ns552p177 Ns552p1516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 658443166) qz372 0 3 Ns552p1517 Ns552p180 Ns552p1516 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1519 := Ns552p1433 Bool.true 258855068 258045 Bool.true 658443166 28296951008113761 1 Bool.false 505353884 Bool.false Bool.true 112971963 275116 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 505353884 536870912) qz209 rfl (Ns552p1514 rfl) (Ns552p1469 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p1518 rfl rfl) rfl 

noncomputable def Ns552p1520 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) 112971963 536870912 275116 536870912 112971963 536870912 275116 536870912 121302721612480512 112971963 268435456 68779 67108864 (Ns552p1519 rfl rfl rfl rfl) 

noncomputable def Ns552p1521 := @Enclosure.Real.IsNear.mulLit_ff qz704 (Zeta.RiemannSiegel.correction qz208) 9551611 33554432 1 33554432 241112334961567 562949953421312 5051878733037749 338121815773675520000 2303011230854587934437 18889465931478580854784 

noncomputable abbrev qz708 := (@HPow.hPow Real Real Real qz7 qz207 qz9)

noncomputable def Ns552p1522 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz708 1 1 0 1 9551611 33554432 1 33554432 9551611 33554432 1 33554432 

noncomputable def Ns552p1523 := @Enclosure.Real.IsNear.sqrt_image qz207 5110259029099 33554432000 478457 33554432000 414091563 414091603 33554432 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 5110259029099 33554432000 478457 33554432000 (BSN.t_div_two_pi_mk qz206 956914 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 956914 1000 0 1 10680707 67108864 1 67108864 5110259029099 33554432000 478457 33554432000 (Enclosure.Real.IsNear.const Bool.false 956914 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz791 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 956914 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz709 := qz791

noncomputable abbrev qz517 := qz709

noncomputable abbrev qz215 := qz517

noncomputable def Ns552p1524 := @Enclosure.Real.IsNear.sqrt_image qz215 414091583 33554432 5 8388608 117875388 117875395 33554432 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 828183166 67108864 40 67108864 414091583 33554432 5 8388608 (Ns552p1523 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p1525 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 235750783 67108864 7 67108864 9551610 9551612 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 235750783 67108864 7 67108864 235750783 67108864 7 67108864 (Ns552p1524 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p1526 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 19103222 67108864 2 67108864 9551611 33554432 1 33554432 (Ns552p1525 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz511))

noncomputable abbrev qz710 := (@HMul.hMul Real Real Real qz742 qz789 qz789)

noncomputable abbrev qz518 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz710 qz703) qz603)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz518))

noncomputable def Ns552p1527 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 241112334961567 

noncomputable def Ns552p1528 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz216) qz217 124150511 67108864 887 

noncomputable abbrev qz711 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz216))

noncomputable def Ns552p1529 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz216) (@Neg.neg Real Real.instNeg qz711) Bool.true 124150511 67108864 887 67108864 (BSN.inv_eq_neg_inv_neg qz216) 

noncomputable def Ns552p1530 := @Enclosure.Real.IsNear.recentre' qz711 Bool.false 124150511 67108864 887 67108864 124150511 67108864 

noncomputable def Ns552p1531 := @Enclosure.Real.IsNear.recentre' qz216 Bool.true 36275321 67108864 622207216 161229045760000 36275321 67108864 38887951 10076815360000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz355 qz352 qz511)

noncomputable def Ns552p1532 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 143739161) qz380) Bool.false 143739161 67108864 63 16777216 Bool.true 36275321 67108864 1 

noncomputable def Ns552p1533 := nat_lit 134930377069784002087644387 

noncomputable def Ns552p1534 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 11438399 33554432 5 8388608 10114744253570544508445 4722366482869645213696 Ns552p1533 

noncomputable def Ns552p1535 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 414091583 33554432 5 8388608 12 1 0 1 11438399 11438399 33554432 5 

noncomputable def Ns552p1536 := @Ns552p1535 8388608 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 828183166 67108864 40 67108864 414091583 33554432 5 8388608 (Ns552p1523 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p1537 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 10114744253570544508445 4722366482869645213696 Ns552p1533 Ns552p495 143739161 67108864 63 16777216 (@Ns552p1534 Ns552p495 RS553to564.d55 (Ns552p1536 rfl rfl) rfl) 

noncomputable def Ns552p1538 := nat_lit 5523186326835373667254272 

noncomputable def Ns552p1539 := nat_lit 40952082990738424155431849910102713651607327534344173965431400182469807194052026172500130625 

noncomputable def Ns552p1540 := nat_lit 46199975943266144436568348213124696692647303168343434164427665391357367878632476496239452487680 

noncomputable def Ns552p1541 := nat_lit 1440386864285300693087040621841695289548978806797472500251818531194088142091332937890625 

noncomputable def Ns552p1542 := nat_lit 107253123397010839444056513603547934914217064243309450192081830866941847460763349246077090625 

noncomputable def Ns552p1543 := nat_lit 846999558959879314670419717240619439365200558086296293014507198841551744441595402431056628940800 

noncomputable def Ns552p1544 := BSN.sin_dyadic_bound_f 78489198455 137438953472 3 2 67108864 19238770 Ns552p1539 Ns552p1540 Ns552p1541 Ns552p1542 Ns552p1543 Ns552p1541 36275321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 78489198455) qz635 0 2 Ns552p1539 Ns552p1540 Ns552p1541 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 78489198455) qz636 0 2 Ns552p1542 Ns552p1543 Ns552p1541 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1545 := @Ns552p1532 9610000 (Ns552p1537 rfl) (Enclosure.sfrac_false_div 143739161 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 143739161) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns552p1538) qz394) 226375608064910080 72057594037927936 Bool.false 36275321 67108864 0 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q1 143739161 67108864 226375608064910080 72057594037927936 0 Ns552p1538 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 36275321 67108864 Ns552p1538 Ns552p114 78489198455 137438953472 19238770 19220000 (Ns552p1544 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1546 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz216) 36275321 67108864 38887951 10076815360000 62074812 62075699 33554432 (@Enclosure.Real.IsNear.neg qz216 Bool.true 36275321 67108864 38887951 10076815360000 (Ns552p1531 (Ns552p1545 rfl rfl) rfl)) 

noncomputable def Ns552p1547 := Ns552p1529 (@Enclosure.Real.IsNear.neg qz711 Bool.false 124150511 67108864 887 67108864 (@Ns552p1530 887 67108864 (Ns552p1546 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1548 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true 7768388 33554432 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz355 qz352 qz518)

noncomputable def Ns552p1549 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15136673)) qz597) Bool.true 15136673 8388608 

noncomputable def Ns552p1550 := nat_lit 285923671026584299058705994205 

noncomputable def Ns552p1551 := nat_lit 3807144920163726466127087586674619 

noncomputable def Ns552p1552 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns552p1550 Ns552p213 Ns552p1551 

noncomputable abbrev qz220 := qz518

noncomputable def Ns552p1553 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 323340753928831 

noncomputable abbrev qz519 := (@HSub.hSub Real Real Real qz588 qz710 qz703)

noncomputable abbrev qz221 := qz519

noncomputable def Ns552p1554 := @Enclosure.Real.IsNear.subLit_tf qz221 qz31 252972009751167 1125899906842624 141078125 140737488355328 1 16 

noncomputable abbrev qz520 := qz710

noncomputable abbrev qz222 := qz520

noncomputable def Ns552p1555 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 130836971683201 1125899906842624 57192045 140737488355328 11438399 33554432 5 8388608 

noncomputable def Ns552p1556 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 11438399 33554432 5 8388608 11438399 33554432 5 8388608 130836971683201 1125899906842624 

noncomputable def Ns552p1557 := nat_lit 25852408278967474125910886334275507129127466862468293428632201188640424216336207123192931201 

noncomputable def Ns552p1558 := nat_lit 144665558069937791517567774848418875750937874611307841580007506487091891865194963329921 

noncomputable def Ns552p1559 := nat_lit 156181551103645141689127627727196289148080426296008988100694906476172616847362064503575339905 

noncomputable def Ns552p1560 := BSN.cos_dyadic_bound_t 15136673 8388608 4 3 33554432 9610000 Ns552p1557 Ns552p639 Ns552p1558 Ns552p1559 Ns552p642 Ns552p1558 7768388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 15136673) (BSN.cosEvenQ 8388608) 0 3 Ns552p1557 Ns552p639 Ns552p1558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 15136673) (BSN.cosOddQ 8388608) 0 3 Ns552p1559 Ns552p642 Ns552p1558 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1561 := @Ns552p1548 517718608 80614522880000 1942097 8388608 32357413 5038407680000 (@Ns552p1549 53 8388608 Bool.true 7768388 33554432 1 9610000 (@Ns552p1552 Ns552p216 15136673 8388608 53 8388608 (@Ns552p1553 1125899906842624 141078125 140737488355328 Ns552p1550 Ns552p213 Ns552p1551 Ns552p216 RS553to564.d55 (@Ns552p1554 0 1 5173452062861296 323340753928831 1125899906842624 141078125 140737488355328 (@Ns552p1555 8488332099098870022144 252972009751167 1125899906842624 141078125 140737488355328 (@Ns552p1556 57192045 140737488355328 (Ns552p1536 rfl rfl) (Ns552p1536 rfl rfl) rfl) (Ns552p1536 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15136673 8388608) (BSN.cos_neg_of_bound 15136673 8388608 Bool.true 7768388 33554432 1 9610000 (Ns552p1560 rfl rfl)) rfl rfl) 

noncomputable def Ns552p1562 := @Ns552p1521 48398403625214450980763 Ns552p86 (Ns552p1522 qz33 (@Enclosure.Real.IsNear.of_eq qz708 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 9551611 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 956914 1000 qz209)) Ns552p1526) rfl) (@Ns552p1527 562949953421312 5051878733037749 338121815773675520000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 956914 1000 12 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 956914 1000 12 qz209 rfl rfl rfl))) (@Ns552p1528 67108864 1942097 8388608 32357413 5038407680000 241112334961567 562949953421312 5051878733037749 338121815773675520000 Ns552p1547 (Ns552p1561 rfl) rfl)) 

noncomputable def Ns552p1563 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 10252706394450110768869 18889465931478580854784 Ns552p1430 Ns552p86 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HMul.hMul Real Real Real qz5 qz704 (Zeta.RiemannSiegel.correction qz208))) Bool.true 10252706394450110768869 18889465931478580854784 Ns552p1430 Ns552p86 (BSN.hardyZApproximantRS₀_eq qz206 12 (@BSN.floor_sqrt_eq_dec qz206 956914 1000 12 qz209 rfl rfl rfl)) (@Ns552p1432 10252706394450110768869 18889465931478580854784 Ns552p1430 Ns552p86 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12)) Bool.true 112971963 268435456 68779 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (Ns552p1520 (Ns552p1519 rfl rfl rfl rfl) rfl rfl)) (Ns552p1562 rfl) rfl rfl)) 

theorem RS553to564.d69 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 10252706394450110768869 18889465931478580854784 Ns552p1430 Ns552p86 := Ns552p1563 

noncomputable def Ns552p1564 := nat_lit 90763883800754581007237120 

noncomputable def Ns552p1565 := nat_lit 1394700575728384892986858668032 

noncomputable abbrev qz792 := (Enclosure.sfrac Bool.false 958164 1000)

noncomputable abbrev qz712 := qz792

noncomputable abbrev qz521 := qz712

noncomputable abbrev qz223 := qz521

noncomputable abbrev qz793 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 958164 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz713 := qz793

noncomputable abbrev qz522 := qz713

noncomputable abbrev qz224 := qz522

noncomputable abbrev qz794 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 958164 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz714 := qz794

noncomputable abbrev qz523 := qz714

noncomputable abbrev qz225 := qz523

noncomputable abbrev qz715 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz224 qz9))

noncomputable def Ns552p1566 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HMul.hMul Real Real Real qz5 qz715 (Zeta.RiemannSiegel.correction qz225)) 90016859 134217728 137737 134217728 2277417597255305806833 18889465931478580854784 360954837952449240717 Ns552p1564 Ns552p1565 

noncomputable def Ns552p1567 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin BSN.quadSignPos 11 12 958164 1000 287 536870912 268435456 9007199254740992 Bool.false 1035590978976 4562 1334074092 57 154981288 8 

noncomputable def Ns552p1568 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 958164 1000 176 234 536870912 268435456 9007199254740992 Bool.false 1035590978976 4562 

noncomputable def Ns552p1569 := Ns552p1568 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.false 2171985 221805 Bool.true 459277439 Bool.true 575562431 28296951008113761 1 Bool.false 352113828 Bool.false Bool.false 256790002 Bool.true Bool.false 36095063 

noncomputable def Ns552p1570 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 958164 1000 40 112 536870912 268435456 9007199254740992 Bool.false 1035590978976 4562 

noncomputable def Ns552p1571 := Ns552p1570 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 308322006 181137 Bool.true 362740605 Bool.true 232873931 28296951008113761 1 Bool.false 418918336 Bool.false Bool.false 487151975 Bool.false Bool.false 2171985 

noncomputable def Ns552p1572 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 958164 1000 135 41 536870912 268435456 9007199254740992 Bool.false 1035590978976 4562 

noncomputable def Ns552p1573 := Ns552p1572 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 319119361 134591 Bool.false 43809990 Bool.false 18704363 28296951008113761 1 Bool.false 43761384 Bool.false Bool.false 18700579 Bool.true Bool.true 308322006 

noncomputable def Ns552p1574 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 958164 1000 382 246 536870912 268435456 9007199254740992 Bool.false 1035590978976 4562 

noncomputable def Ns552p1575 := Ns552p1574 744261104 56 268435448 8 864060384 56 240095976 8 Bool.false 122389411 79425 Bool.false 320507327 Bool.false 223970493 28296951008113761 1 Bool.false 444008699 Bool.true Bool.false 490826814 Bool.true Bool.true 319119361 

noncomputable def Ns552p1576 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 958164 1000 805 557 536870912 268435456 9007199254740992 Bool.false 1035590978976 4562 

noncomputable def Ns552p1577 := Ns552p1576 372130544 56 379625064 8 589812976 56 309962568 8 Bool.false 536870800 4624 Bool.false 160428906 Bool.false 727043551 28296951008113761 1 Bool.false 158051969 Bool.true Bool.false 524329481 Bool.true Bool.false 122389411 

noncomputable def Ns552p1578 := nat_lit 205148183682988401300812498362097874209154531671194083 

noncomputable def Ns552p1579 := nat_lit 106352889031472841032818785581370932547333128192000 

noncomputable def Ns552p1580 := nat_lit 387650889528313476608686363115520000 

noncomputable def Ns552p1581 := nat_lit 2228599044688175360894224304315490631680 

noncomputable abbrev qz795 := (@Eq.refl Real (Enclosure.sfrac Bool.false 958164 1000))

noncomputable abbrev qz716 := qz795

noncomputable abbrev qz524 := qz716

noncomputable abbrev qz226 := qz524

noncomputable def Ns552p1582 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 958164 1000 3672314003584 16000000 1916328 4000 2000 Ns552p1580 Ns552p1581 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p1583 := nat_lit 19360211566821592129416068965428162649206457998148860609822720 

noncomputable abbrev qz717 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1916328))))

noncomputable abbrev qz525 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 958164 4000) (Real.log (Enclosure.sfrac Bool.false 3672314003584 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz717))

noncomputable abbrev qz718 := (Enclosure.sfrac Bool.false 958164 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz525 qz718) (@HMul.hMul Real Real Real qz355 qz718 (Real.log Real.pi)))

noncomputable def Ns552p1584 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns552p1580 Ns552p1581) 8687167554338993556579 4503599627370496000 33442254066371828307 Ns552p102 Ns552p1580 Ns552p1581 0 1 Ns552p1583 

noncomputable def Ns552p1585 := nat_lit 29149297297467406424266820812800 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz359 qz525 qz718)

noncomputable def Ns552p1586 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz718 (Real.log Real.pi)) 2231405865424964882247 900719925474099200 1509633206750721 480500000000000000000 9200952100701 16777216000 718623 134217728000 Ns552p1585 8687167554338993556579 4503599627370496000 

noncomputable def Ns552p1587 := nat_lit 22314058654249648822470000 

noncomputable abbrev qz229 := qz525

noncomputable def Ns552p1588 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz718 13314622843804736375907 4503599627370496000 1509633206750721 480500000000000000000 958164 2000 0 1 Ns552p1587 2231405865424964882247 900719925474099200 1509633206750721 480500000000000000000 

noncomputable def Ns552p1589 := nat_lit 29981865238968852254253188297508519936 

noncomputable def Ns552p1590 := nat_lit 119381364890249067176656896 

noncomputable def Ns552p1591 := nat_lit 91782052568097920985341601016127649668884967724507528787070230756607610240044195213097004298725728535236789481690426466971342961882612021348510436437888482494067058630410281974916710400 

noncomputable def Ns552p1592 := nat_lit 2388177234926722007961554711301857117988350564937183758935021248304007475392133688173675653214440474438204118827211017024786641200346289013782965262599087757246088707574560245143306240 

noncomputable def Ns552p1593 := nat_lit 78220578841936823227755383028051727872291855090915335684177382336685740972038390874702223795421182942738898982081349309037109061424914674403912269493296026574048779918754447360 

noncomputable def Ns552p1594 := BSN.log_dyadic_bound 1575162003584 5769466003584 8 7 Ns552p1591 268435456 76880000 Ns552p1592 Ns552p1593 150388749 7344628007168 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1575162003584) (BSN.artanhQ 5769466003584) 0 7 Ns552p1592 Ns552p1591 Ns552p1593 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz526 := (Real.log (Enclosure.sfrac Bool.false 3672314003584 16000000))

noncomputable def Ns552p1595 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 958164 4000) qz526 958164 4000 0 1 55591280055348327 4503599627370496 12500016337 961000000000000000 13316390815738193597907 4503599627370496000 2994266413381317 961000000000000000000 (Enclosure.Real.IsNear.const Bool.false 958164 4000) (BSN.isNear_log_sfrac 3672314003584 16000000 55591280055348327 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3672314003584) qz362)) Bool.false Ns552p1590 Ns552p114 1000001306960000 76880000000000000000000 55591280055348327 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3672314003584 16000000 17 7344628007168 4194304000000 150388749 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p1594 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1596 := BSN.arctan_dyadic_bound_f 1000 1916328 1 0 33554432 9610000 0 1 1 0 1 1 17509 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1916328) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1916328) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p1597 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1916328))) 884279719003555 562949953421312 1 2000000000000000 17509 33554432 1 9610000 29661647009549440253952 883985966728611 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p1596 rfl) rfl rfl 

noncomputable abbrev qz527 := (@HMul.hMul Real Real Real qz584 qz589 qz717)

noncomputable abbrev qz230 := qz527

noncomputable abbrev qz528 := qz717

noncomputable abbrev qz231 := qz528

noncomputable def Ns552p1598 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 958164 4000) qz526) qz230 13316390815738193597907 4503599627370496000 2994266413381317 961000000000000000000 883985966728611 2251799813685248 200000000961 7688000000000000000 Ns552p1589 13314622843804736375907 4503599627370496000 1509633206750721 480500000000000000000 (Ns552p1595 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz231 1 4 0 1 883985966728611 562949953421312 200000000961 1922000000000000000 883985966728611 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p1597 rfl) 

noncomputable def Ns552p1599 := @Ns552p1584 Ns552p1578 Ns552p1579 33442254066371828307 Ns552p102 (@Ns552p1586 33442254066371828307 Ns552p102 (Ns552p1588 (Ns552p1598 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 958164 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz718 (Real.log Real.pi) 958164 2000 0 1 38410761 33554432 3 268435456 9200952100701 16777216000 718623 134217728000 (Enclosure.Real.IsNear.const Bool.false 958164 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p1580 Ns552p1581) 

noncomputable def Ns552p1600 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns552p1578 Ns552p1579 33442254066371828307 Ns552p102 32362218093 16777216 571 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz370 qz227 (Enclosure.sfrac Bool.true Ns552p1580 Ns552p1581)) Bool.false Ns552p1578 Ns552p1579 33442254066371828307 Ns552p102 Ns552p1582 (Ns552p1599 rfl rfl)) 

noncomputable def Ns552p1601 := BSN.cos_dyadic_bound_f 85799407 137438953472 1 0 67108864 19238770 0 1 1 0 1 1 67108850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 85799407) qz595 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 85799407) qz596 0 0 rfl) rfl rfl 

noncomputable def Ns552p1602 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 32362218093) qz677) Bool.false 32362218093 16777216 571 67108864 Bool.false 67108850 67108864 1 9610000 (Ns552p1600 rfl) (Enclosure.sfrac_false_div 32362218093 16777216) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 32362218093) qz677) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1509399137161897312256) (@Nat.cast Real Real.instNatCast Ns552p1081)) 226375608064910080 72057594037927936 Bool.false 67108850 67108864 307 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q0 32362218093 16777216 226375608064910080 72057594037927936 307 1509399137161897312256 Ns552p1081 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108850 67108864 1509399137161897312256 Ns552p1081 85799407 137438953472 19238770 19220000 (Ns552p1601 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1603 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns552p1578 Ns552p1579 33442254066371828307 Ns552p102 1035590978976 536870912 4562 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz370 qz227 (Enclosure.sfrac Bool.true Ns552p1580 Ns552p1581)) Bool.false Ns552p1578 Ns552p1579 33442254066371828307 Ns552p102 Ns552p1582 (Ns552p1599 rfl rfl)) 

noncomputable def Ns552p1604 := Ns552p1577 79425 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 805 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 158051969 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 557 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 524329481 536870912) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 33554425 33554432 347151179 40307261440000 536870800 536870912 4624 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 33554425 33554432 347151179 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 67108850 67108864 5554418864 644916183040000 33554425 33554432 347151179 40307261440000 (Ns552p1602 rfl rfl) rfl)) rfl) (Ns552p1603 rfl) RS553to564.d7 

noncomputable def Ns552p1605 := nat_lit 662415502745739940312134691930896 

noncomputable def Ns552p1606 := BSN.sin_dyadic_bound_f 160428906 536870912 2 1 536870912 268435456 Ns552p1605 Ns552p283 Ns552p1605 Ns552p1605 Ns552p284 Ns552p1605 158051969 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 160428906) qz371 0 1 Ns552p1605 Ns552p283 Ns552p1605 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 160428906) qz372 0 1 Ns552p1605 Ns552p284 Ns552p1605 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1607 := nat_lit 100180366513548725693009432780577909167148928186328548871796246293981779810768847367236268757054257967527420912001 

noncomputable def Ns552p1608 := nat_lit 21813488154329909549835061339301485479323302757161263171200272598808963227383864381147590564481050246537601 

noncomputable def Ns552p1609 := nat_lit 500557738991210096961032815608110176684729090941359134892876014157821688150472302704978687047922035030106010444161 

noncomputable def Ns552p1610 := BSN.sin_dyadic_bound_f 727043551 536870912 4 3 536870912 268435456 Ns552p1607 Ns552p177 Ns552p1608 Ns552p1609 Ns552p180 Ns552p1608 524329481 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 727043551) qz371 0 3 Ns552p1607 Ns552p177 Ns552p1608 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 727043551) qz372 0 3 Ns552p1609 Ns552p180 Ns552p1608 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1611 := nat_lit 1472900678220527430767237769063755246523732745522665717481473984555471361 

noncomputable def Ns552p1612 := nat_lit 111353455292509914216574012503851584678788242647228003201789659271681 

noncomputable def Ns552p1613 := nat_lit 4418479327750997272473280159166258036401840660082702696438018374347870721 

noncomputable def Ns552p1614 := BSN.cos_dyadic_bound_f 320507327 536870912 3 2 536870912 268435456 Ns552p1611 Ns552p140 Ns552p1612 Ns552p1613 Ns552p143 Ns552p1612 444008699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 320507327) qz373 0 2 Ns552p1611 Ns552p140 Ns552p1612 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 320507327) qz374 0 2 Ns552p1613 Ns552p143 Ns552p1612 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1615 := nat_lit 351204306374209409349123304152833635272126644347521504061172979745765281 

noncomputable def Ns552p1616 := nat_lit 6331789199105363556352295132107114753475965221079089588352488912801 

noncomputable def Ns552p1617 := nat_lit 1053600255544230017320257207868236691586872981112122354004342234259470241 

noncomputable def Ns552p1618 := BSN.cos_dyadic_bound_f 223970493 536870912 3 2 536870912 268435456 Ns552p1615 Ns552p140 Ns552p1616 Ns552p1617 Ns552p143 Ns552p1616 490826814 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 223970493) qz373 0 2 Ns552p1615 Ns552p140 Ns552p1616 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 223970493) qz374 0 2 Ns552p1617 Ns552p143 Ns552p1616 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1619 := Ns552p1575 134591 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 382 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 444008699 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 246 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 490826814 536870912) qz226 rfl rfl (Ns552p1604 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p1606 rfl rfl) (Ns552p1610 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p1603 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p1614 rfl rfl) (Ns552p1618 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p1620 := nat_lit 3683770928310827949484760010000 

noncomputable def Ns552p1621 := BSN.sin_dyadic_bound_f 43809990 536870912 2 1 536870912 268435456 Ns552p1620 Ns552p283 Ns552p1620 Ns552p1620 Ns552p284 Ns552p1620 43761384 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 43809990) qz371 0 1 Ns552p1620 Ns552p283 Ns552p1620 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 43809990) qz372 0 1 Ns552p1620 Ns552p284 Ns552p1620 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1622 := BSN.sin_dyadic_bound_f 18704363 536870912 1 0 536870912 268435456 0 1 1 0 1 1 18700579 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 18704363) qz371 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 18704363) qz372 0 0 rfl) rfl rfl 

noncomputable def Ns552p1623 := Ns552p1573 181137 BSN.abs_quadSignPos (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 43761384 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 18700579 536870912) qz226 rfl rfl (Ns552p1619 rfl rfl) (Ns552p1603 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p1621 rfl rfl) (Ns552p1622 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1624 := nat_lit 2416725594653106672304314535257049997747036625352540607598800263252190625 

noncomputable def Ns552p1625 := nat_lit 299757034793260563046813064084745034449397111606773032328170375390625 

noncomputable def Ns552p1626 := nat_lit 7249577269889733495786849979642980503172211081834408276731744449005790625 

noncomputable def Ns552p1627 := BSN.cos_dyadic_bound_f 362740605 536870912 3 2 536870912 268435456 Ns552p1624 Ns552p140 Ns552p1625 Ns552p1626 Ns552p143 Ns552p1625 418918336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 362740605) qz373 0 2 Ns552p1624 Ns552p140 Ns552p1625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 362740605) qz374 0 2 Ns552p1626 Ns552p143 Ns552p1625 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1628 := nat_lit 410470005381256039581269983562831236996744733709723585675359533391418721 

noncomputable def Ns552p1629 := nat_lit 8649021851798671360260324417111857750928713409355690181777856140641 

noncomputable def Ns552p1630 := nat_lit 1231392718100064521401089430039659487274732343702352045645715044461974881 

noncomputable def Ns552p1631 := BSN.cos_dyadic_bound_f 232873931 536870912 3 2 536870912 268435456 Ns552p1628 Ns552p140 Ns552p1629 Ns552p1630 Ns552p143 Ns552p1629 487151975 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 232873931) qz373 0 2 Ns552p1628 Ns552p140 Ns552p1629 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 232873931) qz374 0 2 Ns552p1630 Ns552p143 Ns552p1629 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1632 := Ns552p1571 221805 BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 418918336 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 487151975 536870912) qz226 rfl rfl (Ns552p1623 rfl) (Ns552p1603 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p1627 rfl rfl) (Ns552p1631 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1633 := nat_lit 6211945779220418610100919764288030205391436882796541003766301849025960961 

noncomputable def Ns552p1634 := nat_lit 1979706902923488178170278368866463939558249297888674200416781409377281 

noncomputable def Ns552p1635 := nat_lit 18631877923855408853946418736126357688295194149793845662898071984259128321 

noncomputable def Ns552p1636 := BSN.cos_dyadic_bound_f 459277439 536870912 3 2 536870912 268435456 Ns552p1633 Ns552p140 Ns552p1634 Ns552p1635 Ns552p143 Ns552p1634 352113828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 459277439) qz373 0 2 Ns552p1633 Ns552p140 Ns552p1634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 459277439) qz374 0 2 Ns552p1635 Ns552p143 Ns552p1634 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1637 := nat_lit 15128499428271298788417206391221861662387205316763555334282886291078673748427381147224099977105106010294806019841 

noncomputable def Ns552p1638 := nat_lit 1321628085088963407825796709336477100079245730637835095925667184816185090738971327917381177521464208162561 

noncomputable def Ns552p1639 := nat_lit 91731484266506991052355648544573746612165175804774963113109657924011515365581042006889790845032352681075085311745 

noncomputable def Ns552p1640 := BSN.cos_dyadic_bound_f 575562431 536870912 4 3 536870912 268435456 Ns552p1637 Ns552p151 Ns552p1638 Ns552p1639 Ns552p154 Ns552p1638 256790002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 575562431) qz373 0 3 Ns552p1637 Ns552p151 Ns552p1638 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 575562431) qz374 0 3 Ns552p1639 Ns552p154 Ns552p1638 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1641 := Ns552p1569 258381 BSN.abs_quadSignPos (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 352113828 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 256790002 536870912) qz226 rfl rfl (Ns552p1632 rfl) (Ns552p1603 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p1636 rfl rfl) (Ns552p1640 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1642 := nat_lit 59911026547939557393531840900006694187378766323989325589473724025702612373617054274463256493957132502152527876096 

noncomputable def Ns552p1643 := nat_lit 4671746908560810740373860423779272676707251488705864731589451289866783989546560027085155156872141959991296 

noncomputable def Ns552p1644 := nat_lit 299431973088362190761282441232277151105075139652812026356199224582700259476436980918031966396104819061041739206656 

noncomputable def Ns552p1645 := BSN.sin_dyadic_bound_f 639425486 536870912 4 3 536870912 268435456 Ns552p1642 Ns552p177 Ns552p1643 Ns552p1644 Ns552p180 Ns552p1643 498618112 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 639425486) qz371 0 3 Ns552p1642 Ns552p177 Ns552p1643 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 639425486) qz372 0 3 Ns552p1644 Ns552p180 Ns552p1643 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1646 := Ns552p1567 Bool.false 36095063 258381 Bool.true 639425486 28296951008113761 1 Bool.false 498618112 Bool.false Bool.false 180033718 275474 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 498618112 536870912) qz226 rfl (Ns552p1641 rfl) (Ns552p1603 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p1645 rfl rfl) rfl 

noncomputable def Ns552p1647 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) 180033718 536870912 275474 536870912 180033718 536870912 275474 536870912 193309732746821632 90016859 134217728 137737 134217728 (Ns552p1646 rfl rfl rfl rfl) 

noncomputable def Ns552p1648 := @Enclosure.Real.IsNear.mulLit_ff qz715 (Zeta.RiemannSiegel.correction qz225) 19096989 67108864 1 67108864 119255323300197 281474976710656 47177829611367 3381218157736755200 2277417597255305806833 18889465931478580854784 

noncomputable abbrev qz719 := (@HPow.hPow Real Real Real qz7 qz224 qz9)

noncomputable def Ns552p1649 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz719 1 1 0 1 19096989 67108864 1 67108864 19096989 67108864 1 67108864 

noncomputable def Ns552p1650 := @Enclosure.Real.IsNear.sqrt_image qz224 2558467235487 16777216000 239541 16777216000 414361935 414361975 33554432 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 2558467235487 16777216000 239541 16777216000 (BSN.t_div_two_pi_mk qz223 958164 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 958164 1000 0 1 10680707 67108864 1 67108864 2558467235487 16777216000 239541 16777216000 (Enclosure.Real.IsNear.const Bool.false 958164 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz796 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 958164 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz720 := qz796

noncomputable abbrev qz529 := qz720

noncomputable abbrev qz232 := qz529

noncomputable def Ns552p1651 := @Enclosure.Real.IsNear.sqrt_image qz232 414361955 33554432 5 8388608 117913864 117913870 33554432 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 828723910 67108864 40 67108864 414361955 33554432 5 8388608 (Ns552p1650 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p1652 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 117913867 33554432 3 33554432 9548494 9548495 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 235827734 67108864 6 67108864 117913867 33554432 3 33554432 (Ns552p1651 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p1653 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 19096989 67108864 1 67108864 19096989 67108864 1 67108864 (Ns552p1652 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz523))

noncomputable abbrev qz721 := (@HMul.hMul Real Real Real qz742 qz794 qz794)

noncomputable abbrev qz530 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz721 qz714) qz603)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz530))

noncomputable def Ns552p1654 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 119255323300197 

noncomputable def Ns552p1655 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz233) qz234 14402829 8388608 3 

noncomputable abbrev qz722 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz233))

noncomputable def Ns552p1656 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz233) (@Neg.neg Real Real.instNeg qz722) Bool.true 14402829 8388608 3 262144 (BSN.inv_eq_neg_inv_neg qz233) 

noncomputable def Ns552p1657 := @Enclosure.Real.IsNear.recentre' qz722 Bool.false 115222632 67108864 768 67108864 14402829 8388608 

noncomputable def Ns552p1658 := @Enclosure.Real.IsNear.recentre' qz233 Bool.true 39086068 67108864 2498438864 644916183040000 9771517 16777216 156152429 40307261440000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz355 qz352 qz523)

noncomputable def Ns552p1659 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 147136755) qz380) Bool.false 147136755 67108864 253 67108864 Bool.true 39086068 67108864 1 

noncomputable def Ns552p1660 := nat_lit 134930377070364621536521443 

noncomputable def Ns552p1661 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 11708771 33554432 5 8388608 10353828729756973680905 4722366482869645213696 Ns552p1660 

noncomputable def Ns552p1662 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 414361955 33554432 5 8388608 12 1 0 1 11708771 11708771 33554432 5 

noncomputable def Ns552p1663 := @Ns552p1662 8388608 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 828723910 67108864 40 67108864 414361955 33554432 5 8388608 (Ns552p1650 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p1664 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 10353828729756973680905 4722366482869645213696 Ns552p1660 Ns552p495 147136755 67108864 253 67108864 (@Ns552p1661 Ns552p495 RS553to564.d55 (Ns552p1663 rfl rfl) rfl) 

noncomputable def Ns552p1665 := nat_lit 6012831225150773122826240 

noncomputable def Ns552p1666 := nat_lit 57522725323932077056987510369492065448160918359772985191178864884308781785192213547043142465 

noncomputable def Ns552p1667 := nat_lit 2841801280873084590562236819208026561582933695304923254534342641811393831473453531282241 

noncomputable def Ns552p1668 := nat_lit 150650155789176883488487331155724310797416985240089229434484923856531495752157221317490916161 

noncomputable def Ns552p1669 := BSN.sin_dyadic_bound_f 85447470967 137438953472 3 2 67108864 19238770 Ns552p1666 Ns552p1540 Ns552p1667 Ns552p1668 Ns552p1543 Ns552p1667 39086068 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 85447470967) qz635 0 2 Ns552p1666 Ns552p1540 Ns552p1667 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 85447470967) qz636 0 2 Ns552p1668 Ns552p1543 Ns552p1667 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1670 := @Ns552p1659 9610000 (Ns552p1664 rfl) (Enclosure.sfrac_false_div 147136755 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 147136755) qz380) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns552p1665) qz394) 226375608064910080 72057594037927936 Bool.false 39086068 67108864 0 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q1 147136755 67108864 226375608064910080 72057594037927936 0 Ns552p1665 Ns552p114 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 39086068 67108864 Ns552p1665 Ns552p114 85447470967 137438953472 19238770 19220000 (Ns552p1669 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1671 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz233) 9771517 16777216 156152429 40307261440000 57610932 57611700 33554432 (@Enclosure.Real.IsNear.neg qz233 Bool.true 9771517 16777216 156152429 40307261440000 (Ns552p1658 (Ns552p1670 rfl rfl) rfl)) 

noncomputable def Ns552p1672 := Ns552p1656 (@Enclosure.Real.IsNear.neg qz722 Bool.false 14402829 8388608 3 262144 (@Ns552p1657 3 262144 (Ns552p1671 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1673 := @Enclosure.Real.IsNear.recentre' qz234 Bool.true 8279993 33554432 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz355 qz352 qz530)

noncomputable def Ns552p1674 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7634199)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true 7634199 4194304 

noncomputable def Ns552p1675 := nat_lit 288411885810389228300940398725 

noncomputable def Ns552p1676 := nat_lit 153745052642768723151179674807743 

noncomputable def Ns552p1677 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns552p1675 Ns552p213 Ns552p1676 

noncomputable def Ns552p1678 := nat_lit 24178516392292583494123520000000000000 

noncomputable abbrev qz237 := qz530

noncomputable def Ns552p1679 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 326154586170295 

noncomputable abbrev qz531 := (@HSub.hSub Real Real Real qz588 qz721 qz714)

noncomputable abbrev qz238 := qz531

noncomputable def Ns552p1680 := @Enclosure.Real.IsNear.subLit_tf qz238 qz31 255785841992631 1125899906842624 142429985 140737488355328 1 16 

noncomputable abbrev qz532 := qz721

noncomputable abbrev qz239 := qz532

noncomputable def Ns552p1681 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 137095318330441 1125899906842624 58543905 140737488355328 11708771 33554432 5 8388608 

noncomputable def Ns552p1682 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 11708771 33554432 5 8388608 11708771 33554432 5 8388608 137095318330441 1125899906842624 

noncomputable def Ns552p1683 := nat_lit 6535659798478874741326288319991393693189285702647574877246436795206023934437857238589281 

noncomputable def Ns552p1684 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600 

noncomputable def Ns552p1685 := nat_lit 39188777673151593585843422863425768258295428279376756467869338601598630647184629601 

noncomputable def Ns552p1686 := nat_lit 39477908237923745672903724416230558122675573472116528620481923462050465319387558150283105 

noncomputable def Ns552p1687 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600 

noncomputable def Ns552p1688 := BSN.cos_dyadic_bound_t 7634199 4194304 4 3 33554432 9610000 Ns552p1683 Ns552p1684 Ns552p1685 Ns552p1686 Ns552p1687 Ns552p1685 8279993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 7634199) (BSN.cosEvenQ 4194304) 0 3 Ns552p1683 Ns552p1684 Ns552p1685 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 7634199) (BSN.cosOddQ 4194304) 0 3 Ns552p1686 Ns552p1687 Ns552p1685 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1689 := @Ns552p1673 1045047216 161229045760000 8279993 33554432 65315451 10076815360000 (@Ns552p1674 107 16777216 Bool.true 8279993 33554432 1 9610000 (@Ns552p1677 Ns552p1678 7634199 4194304 107 16777216 (@Ns552p1679 1125899906842624 142429985 140737488355328 Ns552p1675 Ns552p213 Ns552p1676 Ns552p1678 RS553to564.d55 (@Ns552p1680 0 1 5218473378724720 326154586170295 1125899906842624 142429985 140737488355328 (@Ns552p1681 8582748641704481390592 255785841992631 1125899906842624 142429985 140737488355328 (@Ns552p1682 58543905 140737488355328 (Ns552p1663 rfl rfl) (Ns552p1663 rfl rfl) rfl) (Ns552p1663 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7634199 4194304) (BSN.cos_neg_of_bound 7634199 4194304 Bool.true 8279993 33554432 1 9610000 (Ns552p1688 rfl rfl)) rfl rfl) 

noncomputable def Ns552p1690 := @Ns552p1648 360954837952449240717 Ns552p1564 (Ns552p1649 qz33 (@Enclosure.Real.IsNear.of_eq qz719 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 19096989 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 958164 1000 qz226)) Ns552p1653) rfl) (@Ns552p1654 281474976710656 47177829611367 3381218157736755200 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 958164 1000 12 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 958164 1000 12 qz226 rfl rfl rfl))) (@Ns552p1655 262144 8279993 33554432 65315451 10076815360000 119255323300197 281474976710656 47177829611367 3381218157736755200 Ns552p1672 (Ns552p1689 rfl) rfl)) 

noncomputable def Ns552p1691 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 10391329048040396667919 18889465931478580854784 93504723916389939437197 Ns552p1564 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HMul.hMul Real Real Real qz5 qz715 (Zeta.RiemannSiegel.correction qz225))) Bool.false 10391329048040396667919 18889465931478580854784 93504723916389939437197 Ns552p1564 (BSN.hardyZApproximantRS₀_eq qz223 12 (@BSN.floor_sqrt_eq_dec qz223 958164 1000 12 qz226 rfl rfl rfl)) (@Ns552p1566 10391329048040396667919 18889465931478580854784 93504723916389939437197 Ns552p1564 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12)) Bool.false 90016859 134217728 137737 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (Ns552p1647 (Ns552p1646 rfl rfl rfl rfl) rfl rfl)) (Ns552p1690 rfl) rfl rfl)) 

theorem RS553to564.d70 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 10391329048040396667919 18889465931478580854784 93504723916389939437197 Ns552p1564 := Ns552p1691 

noncomputable def Ns552p1692 := nat_lit 46801229190271269388393263 

noncomputable def Ns552p1693 := nat_lit 1409925142726552627535534882816 

noncomputable abbrev qz797 := (Enclosure.sfrac Bool.false 959413 1000)

noncomputable abbrev qz723 := qz797

noncomputable abbrev qz533 := qz723

noncomputable abbrev qz240 := qz533

noncomputable abbrev qz798 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 959413 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz724 := qz798

noncomputable abbrev qz534 := qz724

noncomputable abbrev qz241 := qz534

noncomputable abbrev qz799 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 959413 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz725 := qz799

noncomputable abbrev qz535 := qz725

noncomputable abbrev qz242 := qz535

noncomputable abbrev qz726 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz241 qz9))

noncomputable def Ns552p1694 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HMul.hMul Real Real Real qz5 qz726 (Zeta.RiemannSiegel.correction qz242)) 10654901 67108864 68957 67108864 9013169779709642783145 75557863725914323419136 169497089660583723113263 Ns552p394 Ns552p1693 

noncomputable def Ns552p1695 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin BSN.quadSignPos 11 12 959413 1000 287 536870912 268435456 9007199254740992 Bool.false 1037276676864 4568 1334074092 57 154981288 8 

noncomputable def Ns552p1696 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 9 10 11 959413 1000 176 234 536870912 268435456 9007199254740992 Bool.false 1037276676864 4568 

noncomputable def Ns552p1697 := Ns552p1696 1236190956 57 169773496 8 1287360220 57 161872664 8 Bool.true 228171731 222089 Bool.true 317582055 Bool.true 497777458 28296951008113761 1 Bool.false 445646561 Bool.false Bool.false 322170841 Bool.true Bool.true 184384069 

noncomputable def Ns552p1698 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 959413 1000 40 112 536870912 268435456 9007199254740992 Bool.false 1037276676864 4568 

noncomputable def Ns552p1699 := Ns552p1698 1116391676 57 189812536 8 1179625948 57 178956968 8 Bool.true 595133529 181368 Bool.true 71415920 Bool.true 20528852 28296951008113761 1 Bool.false 532127949 Bool.false Bool.false 536478469 Bool.false Bool.true 228171731 

noncomputable def Ns552p1700 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 959413 1000 135 41 536870912 268435456 9007199254740992 Bool.false 1037276676864 4568 

noncomputable def Ns552p1701 := Ns552p1700 961943533 57 219176632 8 1044702541 57 202918136 8 Bool.true 640130046 134761 Bool.false 528040405 Bool.false 399568777 28296951008113761 1 Bool.false 446929258 Bool.false Bool.false 363689169 Bool.true Bool.true 595133529 

noncomputable def Ns552p1702 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 959413 1000 383 246 536870912 268435456 9007199254740992 Bool.false 1037276676864 4568 

noncomputable def Ns552p1703 := Ns552p1702 744261104 56 268435448 8 864060384 56 240095976 8 Bool.true 747397284 79523 Bool.false 233308240 Bool.false 830456962 28296951008113761 1 Bool.false 226033835 Bool.false Bool.false 12856665 Bool.true Bool.true 640130046 

noncomputable def Ns552p1704 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 959413 1000 806 558 536870912 268435456 9007199254740992 Bool.false 1037276676864 4568 

noncomputable def Ns552p1705 := Ns552p1704 372130544 56 379625064 8 589812976 56 309962568 8 Bool.true 536870576 4624 Bool.false 538020888 Bool.false 832750175 28296951008113761 1 Bool.false 289104255 Bool.true Bool.false 10563999 Bool.true Bool.true 747397284 

noncomputable def Ns552p1706 := nat_lit 244298590251336276529943595432517322416154273719564811276659 

noncomputable def Ns552p1707 := nat_lit 126443416567543311239777211519860618100831122519752704000 

noncomputable def Ns552p1708 := nat_lit 390184066278932616886880698380640000 

noncomputable def Ns552p1709 := nat_lit 2246086278168905025860930129508485785920 

noncomputable abbrev qz800 := (@Eq.refl Real (Enclosure.sfrac Bool.false 959413 1000))

noncomputable abbrev qz727 := qz800

noncomputable abbrev qz536 := qz727

noncomputable abbrev qz243 := qz536

noncomputable def Ns552p1710 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 959413 1000 3681894218276 16000000 1918826 4000 2000 Ns552p1708 Ns552p1709 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns552p1711 := nat_lit 78175548880427608489581950538405543173169367590260739608530880 

noncomputable abbrev qz728 := (@HSub.hSub Real Real Real qz746 qz747 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz748 (@Nat.cast Real Real.instNatCast 1918826))))

noncomputable abbrev qz537 := (@HSub.hSub Real Real Real qz588 (@HMul.hMul Real Real Real qz584 (Enclosure.sfrac Bool.false 959413 4000) (Real.log (Enclosure.sfrac Bool.false 3681894218276 16000000))) (@HMul.hMul Real Real Real qz584 qz589 qz728))

noncomputable abbrev qz729 := (Enclosure.sfrac Bool.false 959413 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz537 qz729) (@HMul.hMul Real Real Real qz355 qz729 (Real.log Real.pi)))

noncomputable def Ns552p1712 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns552p1708 Ns552p1709) 34805232848441849451539 18014398509481984000 133942854889056071251 Ns552p244 Ns552p1708 Ns552p1709 0 1 Ns552p1711 

noncomputable def Ns552p1713 := nat_lit 2335739637714416686751805341696000 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz359 qz537 qz729)

noncomputable def Ns552p1714 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz729 (Real.log Real.pi)) 44697558141455456048147 18014398509481984000 12092678174410681 3844000000000000000000 36851783443293 67108864000 2878239 536870912000 Ns552p1713 34805232848441849451539 18014398509481984000 

noncomputable def Ns552p1715 := nat_lit 89395116282910912096294000 

noncomputable abbrev qz246 := qz537

noncomputable def Ns552p1716 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz729 53339182200044275405843 18014398509481984000 12092678174410681 3844000000000000000000 959413 2000 0 1 Ns552p1715 44697558141455456048147 18014398509481984000 12092678174410681 3844000000000000000000 

noncomputable def Ns552p1717 := nat_lit 120109160540183195874813706140662104064 

noncomputable def Ns552p1718 := nat_lit 119406562494135408082812928 

noncomputable def Ns552p1719 := nat_lit 93938896432268646782334682914642160057818925709173213411004818747273072023611960961668266677865781739838178542366340177873245313485380005718413445115073775794716745637906280293492326400 

noncomputable def Ns552p1720 := nat_lit 2466966349340719298058110494539281904292773077365638605710456838335139897135869523397584758054161918786970011856728789562839493905529460029303394038573137566952691638668286804979875840 

noncomputable def Ns552p1721 := nat_lit 85150781148230799419744172821302758098821139532114575626286480406387690240998663726334228346178889435976588408672699364164610444428076127958267719652422436345876685499672821760 

noncomputable def Ns552p1722 := BSN.log_dyadic_bound 1584742218276 5779046218276 8 7 Ns552p1719 268435456 76880000 Ns552p1720 Ns552p1721 151088123 7363788436552 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1584742218276) (BSN.artanhQ 5779046218276) 0 7 Ns552p1720 Ns552p1719 Ns552p1721 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz538 := (Real.log (Enclosure.sfrac Bool.false 3681894218276 16000000))

noncomputable def Ns552p1723 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 959413 4000) qz538 959413 4000 0 1 55603013604011111 4503599627370496 12500016337 961000000000000000 53346254090865112037843 18014398509481984000 11992678173930181 3844000000000000000000 (Enclosure.Real.IsNear.const Bool.false 959413 4000) (BSN.isNear_log_sfrac 3681894218276 16000000 55603013604011111 4503599627370496 12500016337 961000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3681894218276) qz362)) Bool.false Ns552p1718 Ns552p114 1000001306960000 76880000000000000000000 55603013604011111 4503599627370496 12500016337 961000000000000000 (BSN.log_rat_reduce_isNear 3681894218276 16000000 17 7363788436552 4194304000000 151088123 268435456 24973259072661432 36028797018963968 76880000 1000000000000000 rfl rfl rfl rfl (Ns552p1722 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1724 := BSN.arctan_dyadic_bound_f 1000 1918826 1 0 33554432 9610000 0 1 1 0 1 1 17486 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1918826) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1918826) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns552p1725 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1918826))) 884279719003555 562949953421312 1 2000000000000000 17486 33554432 1 9610000 29661659957398368944128 883986352604579 562949953421312 200000000961 1922000000000000000 qz17 (Ns552p1724 rfl) rfl rfl 

noncomputable abbrev qz539 := (@HMul.hMul Real Real Real qz584 qz589 qz728)

noncomputable abbrev qz247 := qz539

noncomputable abbrev qz540 := qz728

noncomputable abbrev qz248 := qz540

noncomputable def Ns552p1726 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 959413 4000) qz538) qz247 53346254090865112037843 18014398509481984000 11992678173930181 3844000000000000000000 883986352604579 2251799813685248 200000000961 7688000000000000000 Ns552p1717 53339182200044275405843 18014398509481984000 12092678174410681 3844000000000000000000 (Ns552p1723 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz248 1 4 0 1 883986352604579 562949953421312 200000000961 1922000000000000000 883986352604579 2251799813685248 200000000961 7688000000000000000 qz369 Ns552p1725 rfl) 

noncomputable def Ns552p1727 := @Ns552p1712 Ns552p1706 Ns552p1707 133942854889056071251 Ns552p244 (@Ns552p1714 133942854889056071251 Ns552p244 (Ns552p1716 (Ns552p1726 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 959413 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz729 (Real.log Real.pi) 959413 2000 0 1 38410761 33554432 3 268435456 36851783443293 67108864000 2878239 536870912000 (Enclosure.Real.IsNear.const Bool.false 959413 2000) RS553to564.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns552p1708 Ns552p1709) 

noncomputable def Ns552p1728 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns552p1706 Ns552p1707 133942854889056071251 Ns552p244 4051862019 2097152 571 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz370 qz244 (Enclosure.sfrac Bool.true Ns552p1708 Ns552p1709)) Bool.false Ns552p1706 Ns552p1707 133942854889056071251 Ns552p244 Ns552p1710 (Ns552p1727 rfl rfl)) 

noncomputable def Ns552p1729 := nat_lit 14339645564434808976720949102368567046583825529163944266362970891231219443196111757028660139525406781594399825422504225316963440825272138034081 

noncomputable def Ns552p1730 := nat_lit 10164077646254256925687554113803996313638384904851784431785840877441296268612799765320847635354978023018972399384807435839037786008677281 

noncomputable def Ns552p1731 := nat_lit 71609385416142981215742411210998239838554402730712082133571362524878358588928395473874480276252591970864511200782838477026400440695384377486241 

noncomputable def Ns552p1732 := BSN.sin_dyadic_bound_f 215735855463 137438953472 4 3 67108864 19238770 Ns552p1729 Ns552p566 Ns552p1730 Ns552p1731 Ns552p569 Ns552p1730 67108822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215735855463) qz635 0 3 Ns552p1729 Ns552p566 Ns552p1730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215735855463) qz636 0 3 Ns552p1731 Ns552p569 Ns552p1730 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1733 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4051862019) (@Nat.cast Real Real.instNatCast 2097152)) Bool.false 4051862019 2097152 571 67108864 Bool.true 67108822 67108864 1 9610000 (Ns552p1728 rfl) (Enclosure.sfrac_false_div 4051862019 2097152) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 4051862019) (@Nat.cast Real Real.instNatCast 2097152)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 474408163219606945660928) (@Nat.cast Real Real.instNatCast 302231454903657293676544)) 226375608064910080 72057594037927936 Bool.false 67108822 67108864 307 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q1 4051862019 2097152 226375608064910080 72057594037927936 307 474408163219606945660928 302231454903657293676544 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108822 67108864 474408163219606945660928 302231454903657293676544 215735855463 137438953472 19238770 19220000 (Ns552p1732 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1734 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns552p1706 Ns552p1707 133942854889056071251 Ns552p244 1037276676864 536870912 4568 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz370 qz244 (Enclosure.sfrac Bool.true Ns552p1708 Ns552p1709)) Bool.false Ns552p1706 Ns552p1707 133942854889056071251 Ns552p244 Ns552p1710 (Ns552p1727 rfl rfl)) 

noncomputable def Ns552p1735 := Ns552p1705 79523 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 806 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 289104255 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 558 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 10563999 536870912) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 33554411 33554432 347151179 40307261440000 536870576 536870912 4624 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 33554411 33554432 347151179 40307261440000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 67108822 67108864 5554418864 644916183040000 33554411 33554432 347151179 40307261440000 (Ns552p1733 rfl rfl) rfl)) rfl) (Ns552p1734 rfl) RS553to564.d7 

noncomputable def Ns552p1736 := nat_lit 11548935044567762791643623876441329409933983789276949404694651257612307005850375648958378240480015997557104705536 

noncomputable def Ns552p1737 := nat_lit 588287530849602829897781428315920999278902019491599172989759965047926674834895365241111096534156082937856 

noncomputable def Ns552p1738 := nat_lit 70035511142194956860739291624069690454077018074723353637461443633312006222718618857467492293337932592671421890560 

noncomputable def Ns552p1739 := BSN.cos_dyadic_bound_f 538020888 536870912 4 3 536870912 268435456 Ns552p1736 Ns552p151 Ns552p1737 Ns552p1738 Ns552p154 Ns552p1737 289104255 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 538020888) qz373 0 3 Ns552p1736 Ns552p151 Ns552p1737 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 538020888) qz374 0 3 Ns552p1738 Ns552p154 Ns552p1737 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1740 := nat_lit 66471920220096929802587710395082825578194852045270720829540411536462194159126311575909946814660540226576962890625 

noncomputable def Ns552p1741 := nat_lit 111218438047021254130420379439986705381127239292076907141777841796184276583665430960252714216709136962890625 

noncomputable def Ns552p1742 := nat_lit 402339268313959238314438316018978598760564067834452549700189670328413290320184487461727887140490766048272962890625 

noncomputable def Ns552p1743 := BSN.cos_dyadic_bound_f 832750175 536870912 4 3 536870912 268435456 Ns552p1740 Ns552p151 Ns552p1741 Ns552p1742 Ns552p154 Ns552p1741 10563999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 832750175) qz373 0 3 Ns552p1740 Ns552p151 Ns552p1741 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 832750175) qz374 0 3 Ns552p1742 Ns552p154 Ns552p1741 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1744 := nat_lit 744366322294297238931141626910225897813355568642760908969815457136640000 

noncomputable def Ns552p1745 := nat_lit 8778910472593238150184194190739206219104572069052790970777600000000 

noncomputable def Ns552p1746 := nat_lit 1949516630630013331957889677021901868891576510471500104687944938291200000 

noncomputable def Ns552p1747 := BSN.sin_dyadic_bound_f 233308240 536870912 3 2 536870912 268435456 Ns552p1744 Ns552p130 Ns552p1745 Ns552p1746 Ns552p133 Ns552p1745 226033835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 233308240) qz371 0 2 Ns552p1744 Ns552p130 Ns552p1745 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 233308240) qz372 0 2 Ns552p1746 Ns552p133 Ns552p1745 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1748 := nat_lit 65740263462286777246037508806710968817472486375521113292973454097015806231205822243338447971084746668787016667136 

noncomputable def Ns552p1749 := nat_lit 107598338073403970454450407628437576772814459596705503138956020937806602950456673085694287484304142615187456 

noncomputable def Ns552p1750 := nat_lit 397920711306734409101740455191944561138263526179868064326537608412416592194761278456286211456292278186257666805760 

noncomputable def Ns552p1751 := BSN.cos_dyadic_bound_f 830456962 536870912 4 3 536870912 268435456 Ns552p1748 Ns552p151 Ns552p1749 Ns552p1750 Ns552p154 Ns552p1749 12856665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 830456962) qz373 0 3 Ns552p1748 Ns552p151 Ns552p1749 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 830456962) qz374 0 3 Ns552p1750 Ns552p154 Ns552p1749 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1752 := Ns552p1703 134761 BSN.abs_quadSignPos (BSN.cos_quad_nat3 383 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 226033835 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 246 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12856665 536870912) qz243 rfl rfl (Ns552p1735 RS553to564.d9 RS553to564.d11 RS553to564.d13 RS553to564.d17 (Ns552p1739 rfl rfl) (Ns552p1743 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns552p1734 rfl) RS553to564.d19 RS553to564.d21 RS553to564.d23 RS553to564.d25 RS553to564.d17 (Ns552p1747 rfl rfl) (Ns552p1751 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns552p1753 := nat_lit 19537288185800180518778899285518957411896739870669289950977919553462230625 

noncomputable def Ns552p1754 := nat_lit 6044177973709153994560431731149625686540154845296417401215295250390625 

noncomputable def Ns552p1755 := nat_lit 51159302293709705585572590763080170018141825124860517576768774066757590625 

noncomputable def Ns552p1756 := BSN.sin_dyadic_bound_f 528040405 536870912 3 2 536870912 268435456 Ns552p1753 Ns552p130 Ns552p1754 Ns552p1755 Ns552p133 Ns552p1754 446929258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 528040405) qz371 0 2 Ns552p1753 Ns552p130 Ns552p1754 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 528040405) qz372 0 2 Ns552p1755 Ns552p133 Ns552p1754 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1757 := nat_lit 6404297875834086491535033557532438444042341077622101874154280855085085505 

noncomputable def Ns552p1758 := nat_lit 649729154582976100946151495190896157433469990836536330094212385436481 

noncomputable def Ns552p1759 := nat_lit 16772109160934235040333079833973696378713143870929864802060106848027374401 

noncomputable def Ns552p1760 := BSN.sin_dyadic_bound_f 399568777 536870912 3 2 536870912 268435456 Ns552p1757 Ns552p130 Ns552p1758 Ns552p1759 Ns552p133 Ns552p1758 363689169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 399568777) qz371 0 2 Ns552p1757 Ns552p130 Ns552p1758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 399568777) qz372 0 2 Ns552p1759 Ns552p133 Ns552p1758 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1761 := Ns552p1701 181368 BSN.abs_quadSignPos (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 446929258 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 41 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 363689169 536870912) qz243 rfl rfl (Ns552p1752 rfl rfl) (Ns552p1734 rfl) RS553to564.d27 RS553to564.d29 RS553to564.d31 RS553to564.d33 RS553to564.d17 (Ns552p1756 rfl rfl) (Ns552p1760 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1762 := nat_lit 26012383074935998225170472960000 

noncomputable def Ns552p1763 := BSN.cos_dyadic_bound_f 71415920 536870912 2 1 536870912 268435456 Ns552p1762 Ns552p157 Ns552p1762 Ns552p1762 Ns552p158 Ns552p1762 532127949 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 71415920) qz373 0 1 Ns552p1762 Ns552p157 Ns552p1762 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 71415920) qz374 0 1 Ns552p1762 Ns552p158 Ns552p1762 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1764 := nat_lit 177606417808302758173071913216 

noncomputable def Ns552p1765 := BSN.cos_dyadic_bound_f 20528852 536870912 2 1 536870912 268435456 Ns552p1764 Ns552p157 Ns552p1764 Ns552p1764 Ns552p158 Ns552p1764 536478469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 20528852) qz373 0 1 Ns552p1764 Ns552p157 Ns552p1764 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 20528852) qz374 0 1 Ns552p1764 Ns552p158 Ns552p1764 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1766 := Ns552p1699 222089 BSN.abs_quadSignPos (BSN.cos_quad_nat0 40 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 532127949 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536478469 536870912) qz243 rfl rfl (Ns552p1761 rfl) (Ns552p1734 rfl) RS553to564.d35 RS553to564.d37 RS553to564.d39 RS553to564.d41 RS553to564.d17 (Ns552p1763 rfl rfl) (Ns552p1765 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1767 := nat_lit 1419855831019076287075634133935513266395906316544320470261560721272690625 

noncomputable def Ns552p1768 := nat_lit 103477907230208716599529217247346748196214927587234198268310187890625 

noncomputable def Ns552p1769 := nat_lit 4259360537242768443793703343372045105691326519777786942388145543442290625 

noncomputable def Ns552p1770 := BSN.cos_dyadic_bound_f 317582055 536870912 3 2 536870912 268435456 Ns552p1767 Ns552p140 Ns552p1768 Ns552p1769 Ns552p143 Ns552p1768 445646561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 317582055) qz373 0 2 Ns552p1767 Ns552p140 Ns552p1768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 317582055) qz374 0 2 Ns552p1769 Ns552p143 Ns552p1768 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1771 := nat_lit 8572760370841885055447432338550299696951504740600066118322093697969930496 

noncomputable def Ns552p1772 := nat_lit 3769483134354420428962032906527360513714341666736839582794255001436416 

noncomputable def Ns552p1773 := nat_lit 25710742146256946325484372949837844369827085538466724675800692583906918656 

noncomputable def Ns552p1774 := BSN.cos_dyadic_bound_f 497777458 536870912 3 2 536870912 268435456 Ns552p1771 Ns552p140 Ns552p1772 Ns552p1773 Ns552p143 Ns552p1772 322170841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 497777458) qz373 0 2 Ns552p1771 Ns552p140 Ns552p1772 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 497777458) qz374 0 2 Ns552p1773 Ns552p143 Ns552p1772 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1775 := Ns552p1697 258712 BSN.abs_quadSignPos (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 445646561 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 234 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 322170841 536870912) qz243 rfl rfl (Ns552p1766 rfl) (Ns552p1734 rfl) RS553to564.d43 RS553to564.d45 RS553to564.d47 RS553to564.d49 RS553to564.d17 (Ns552p1770 rfl rfl) (Ns552p1774 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns552p1776 := nat_lit 52946999516729111599821937734518966337375692707827780580494758359944947503911117877051691483314082950838385504721 

noncomputable def Ns552p1777 := nat_lit 3225401334295346284251273721609044284238122656386305196148927046484528326847969597616814400257675341459921 

noncomputable def Ns552p1778 := nat_lit 264638792704477861113324791647439410027297534250615596702349780986560585652476678574562138682449199117781397795281 

noncomputable def Ns552p1779 := BSN.sin_dyadic_bound_f 619986139 536870912 4 3 536870912 268435456 Ns552p1776 Ns552p177 Ns552p1777 Ns552p1778 Ns552p180 Ns552p1777 491086499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 619986139) qz371 0 3 Ns552p1776 Ns552p177 Ns552p1777 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 619986139) qz372 0 3 Ns552p1778 Ns552p180 Ns552p1777 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1780 := Ns552p1695 Bool.true 184384069 258712 Bool.true 619986139 28296951008113761 1 Bool.false 491086499 Bool.false Bool.true 42619604 275828 BSN.abs_quadSignPos qz375 (BSN.sfrac_eq_quadSignPos_mul Bool.false 491086499 536870912) qz243 rfl (Ns552p1775 rfl) (Ns552p1734 rfl) RS553to564.d51 RS553to564.d53 RS553to564.d17 (Ns552p1779 rfl rfl) rfl 

noncomputable def Ns552p1781 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) 42619604 536870912 275828 536870912 42619604 536870912 275828 536870912 45762451337117696 10654901 67108864 68957 67108864 (Ns552p1780 rfl rfl rfl rfl) 

noncomputable def Ns552p1782 := @Enclosure.Real.IsNear.mulLit_ff qz726 (Zeta.RiemannSiegel.correction qz242) 19090771 67108864 1 67108864 472121832046995 1125899906842624 8863629060428279 676243631547351040000 9013169779709642783145 75557863725914323419136 

noncomputable abbrev qz730 := (@HPow.hPow Real Real Real qz7 qz241 qz9)

noncomputable def Ns552p1783 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz730 1 1 0 1 19090771 67108864 1 67108864 19090771 67108864 1 67108864 

noncomputable def Ns552p1784 := @Enclosure.Real.IsNear.sqrt_image qz241 10247209144991 67108864000 959413 67108864000 414631915 414631955 33554432 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 10247209144991 67108864000 959413 67108864000 (BSN.t_div_two_pi_mk qz240 959413 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 959413 1000 0 1 10680707 67108864 1 67108864 10247209144991 67108864000 959413 67108864000 (Enclosure.Real.IsNear.const Bool.false 959413 1000) RS553to564.d56 rfl)) 

noncomputable abbrev qz801 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 959413 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz731 := qz801

noncomputable abbrev qz541 := qz731

noncomputable abbrev qz249 := qz541

noncomputable def Ns552p1785 := @Enclosure.Real.IsNear.sqrt_image qz249 414631935 33554432 5 8388608 117952271 117952278 33554432 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 829263870 67108864 40 67108864 414631935 33554432 5 8388608 (Ns552p1784 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns552p1786 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 235904549 67108864 7 67108864 9545385 9545386 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 235904549 67108864 7 67108864 235904549 67108864 7 67108864 (Ns552p1785 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns552p1787 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 19090771 67108864 1 67108864 19090771 67108864 1 67108864 (Ns552p1786 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz535))

noncomputable abbrev qz732 := (@HMul.hMul Real Real Real qz742 qz799 qz799)

noncomputable abbrev qz542 := (@HSub.hSub Real Real Real qz588 (@HSub.hSub Real Real Real qz588 qz732 qz725) qz603)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz542))

noncomputable def Ns552p1788 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 472121832046995 

noncomputable def Ns552p1789 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz250) qz251 107760185 67108864 669 

noncomputable abbrev qz733 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz250))

noncomputable def Ns552p1790 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz250) (@Neg.neg Real Real.instNeg qz733) Bool.true 107760185 67108864 669 67108864 (BSN.inv_eq_neg_inv_neg qz250) 

noncomputable def Ns552p1791 := @Enclosure.Real.IsNear.recentre' qz733 Bool.false 107760185 67108864 669 67108864 107760185 67108864 

noncomputable def Ns552p1792 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 41792798 67108864 622207216 161229045760000 20896399 33554432 38887951 10076815360000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz355 qz352 qz535)

noncomputable def Ns552p1793 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9408089) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false 9408089 4194304 63 16777216 Bool.true 41792798 67108864 1 

noncomputable def Ns552p1794 := nat_lit 134930377070944399171808483 

noncomputable def Ns552p1795 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 11978751 33554432 5 8388608 10592566568293553459805 4722366482869645213696 Ns552p1794 

noncomputable def Ns552p1796 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 414631935 33554432 5 8388608 12 1 0 1 11978751 11978751 33554432 5 

noncomputable def Ns552p1797 := @Ns552p1796 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 829263870 67108864 40 67108864 414631935 33554432 5 8388608 (Ns552p1784 rfl rfl rfl rfl rfl rfl) rfl) qz381 

noncomputable def Ns552p1798 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 10592566568293553459805 4722366482869645213696 Ns552p1794 Ns552p495 9408089 4194304 63 16777216 (@Ns552p1795 Ns552p495 RS553to564.d55 (Ns552p1797 rfl rfl) rfl) 

noncomputable def Ns552p1799 := nat_lit 78642391403620755889092525668037481208890391285551712415776091850202771385083005080224725825 

noncomputable def Ns552p1800 := nat_lit 5311442284064872075454300963516654650932836419709000799786964676247277751846014113610561 

noncomputable def Ns552p1801 := nat_lit 205959568483880160392834450738538185725278085917479717944785347379150477082666786425357007681 

noncomputable def Ns552p1802 := BSN.sin_dyadic_bound_f 92395657079 137438953472 3 2 67108864 19238770 Ns552p1799 Ns552p1540 Ns552p1800 Ns552p1801 Ns552p1543 Ns552p1800 41792798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 92395657079) qz635 0 2 Ns552p1799 Ns552p1540 Ns552p1800 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 92395657079) qz636 0 2 Ns552p1801 Ns552p1543 Ns552p1800 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1803 := @Ns552p1793 9610000 (Ns552p1798 rfl) (Enclosure.sfrac_false_div 9408089 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9408089) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 406360397260306186764288) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 41792798 67108864 0 1000000000000000 19220000 9610000 (BSN.sin_reduce_arg_pos_rat_q1 9408089 4194304 226375608064910080 72057594037927936 0 406360397260306186764288 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 41792798 67108864 406360397260306186764288 604462909807314587353088 92395657079 137438953472 19238770 19220000 (Ns552p1802 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns552p1804 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz250) 20896399 33554432 38887951 10076815360000 53879758 53880427 33554432 (@Enclosure.Real.IsNear.neg qz250 Bool.true 20896399 33554432 38887951 10076815360000 (Ns552p1792 (Ns552p1803 rfl rfl) rfl)) 

noncomputable def Ns552p1805 := Ns552p1790 (@Enclosure.Real.IsNear.neg qz733 Bool.false 107760185 67108864 669 67108864 (@Ns552p1791 669 67108864 (Ns552p1804 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns552p1806 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true 8762454 33554432 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz355 qz352 qz542)

noncomputable def Ns552p1807 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 61572411)) qz627) Bool.true 61572411 33554432 

noncomputable def Ns552p1808 := nat_lit 290767490576824192687166597725 

noncomputable def Ns552p1809 := nat_lit 155202192770669877704524779306803 

noncomputable def Ns552p1810 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns552p1808 Ns552p213 Ns552p1809 

noncomputable abbrev qz254 := qz542

noncomputable def Ns552p1811 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 328818454532095 

noncomputable abbrev qz543 := (@HSub.hSub Real Real Real qz588 qz732 qz725)

noncomputable abbrev qz255 := qz543

noncomputable def Ns552p1812 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 258449710354431 1125899906842624 143779885 140737488355328 1 16 

noncomputable abbrev qz544 := qz732

noncomputable abbrev qz256 := qz544

noncomputable def Ns552p1813 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 143490475520001 1125899906842624 59893805 140737488355328 11978751 33554432 5 8388608 

noncomputable def Ns552p1814 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 11978751 33554432 5 8388608 11978751 33554432 5 8388608 143490475520001 1125899906842624 

noncomputable def Ns552p1815 := nat_lit 464080643768838313658033817186217429303247549994786927595398152902497873933834837454534972196325201 

noncomputable def Ns552p1816 := nat_lit 2969162151596886451816247010838699596437442869624001072487815483582299646860022709671945373521 

noncomputable def Ns552p1817 := nat_lit 2802825109001463325655831188644949555124698331671294596039907512239860709925174247609473051129087825 

noncomputable def Ns552p1818 := BSN.cos_dyadic_bound_t 61572411 33554432 4 3 33554432 9610000 Ns552p1815 Ns552p501 Ns552p1816 Ns552p1817 Ns552p504 Ns552p1816 8762454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 61572411) (BSN.cosEvenQ 33554432) 0 3 Ns552p1815 Ns552p501 Ns552p1816 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 61572411) (BSN.cosOddQ 33554432) 0 3 Ns552p1817 Ns552p504 Ns552p1816 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns552p1819 := @Ns552p1806 263664304 40307261440000 4381227 16777216 16479019 2519203840000 (@Ns552p1807 27 4194304 Bool.true 8762454 33554432 1 9610000 (@Ns552p1810 Ns552p1678 61572411 33554432 27 4194304 (@Ns552p1811 1125899906842624 143779885 140737488355328 Ns552p1808 Ns552p213 Ns552p1809 Ns552p1678 RS553to564.d55 (@Ns552p1812 0 1 5261095272513520 328818454532095 1125899906842624 143779885 140737488355328 (@Ns552p1813 8672133231507450888192 258449710354431 1125899906842624 143779885 140737488355328 (@Ns552p1814 59893805 140737488355328 (Ns552p1797 rfl rfl) (Ns552p1797 rfl rfl) rfl) (Ns552p1797 rfl rfl) rfl rfl) qz385 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 61572411 33554432) (BSN.cos_neg_of_bound 61572411 33554432 Bool.true 8762454 33554432 1 9610000 (Ns552p1818 rfl rfl)) rfl rfl) 

noncomputable def Ns552p1820 := @Ns552p1782 169497089660583723113263 Ns552p394 (Ns552p1783 qz33 (@Enclosure.Real.IsNear.of_eq qz730 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 19090771 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 959413 1000 qz243)) Ns552p1787) rfl) (@Ns552p1788 1125899906842624 8863629060428279 676243631547351040000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 959413 1000 12 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 959413 1000 12 qz243 rfl rfl rfl))) (@Ns552p1789 67108864 4381227 16777216 16479019 2519203840000 472121832046995 1125899906842624 8863629060428279 676243631547351040000 Ns552p1805 (Ns552p1819 rfl) rfl)) 

noncomputable def Ns552p1821 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 21009521823027024083369 75557863725914323419136 Ns552p1692 Ns552p394 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HMul.hMul Real Real Real qz5 qz726 (Zeta.RiemannSiegel.correction qz242))) Bool.true 21009521823027024083369 75557863725914323419136 Ns552p1692 Ns552p394 (BSN.hardyZApproximantRS₀_eq qz240 12 (@BSN.floor_sqrt_eq_dec qz240 959413 1000 12 qz243 rfl rfl rfl)) (@Ns552p1694 21009521823027024083369 75557863725914323419136 Ns552p1692 Ns552p394 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12)) Bool.true 10654901 67108864 68957 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (Ns552p1781 (Ns552p1780 rfl rfl rfl rfl) rfl rfl)) (Ns552p1820 rfl) rfl rfl)) 

theorem RS553to564.d71 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 21009521823027024083369 75557863725914323419136 Ns552p1692 Ns552p394 := Ns552p1821 

noncomputable def RS553to564.d72 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz545 := (RS553to564.d3 qz583 qz605 (@Enclosure.dec_le_dec qz583 qz605 944396 1000 945649 1000 (@Eq.refl Real qz583) qz609 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns552p1822 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 24255089534174053974781 18889465931478580854784 Ns552p85 Ns552p86 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz583 qz605 944396 1000 945649 1000 (@Eq.refl Real qz583) qz609 rfl rfl rfl)

noncomputable abbrev qz258 := qz546

noncomputable def Ns552p1823 := @Enclosure.Real.IsNear.neg_val qz257 24255089534174053974781 18889465931478580854784 Ns552p85 Ns552p86 (Ns552p1822 (RS553to564.d4 qz4 qz35 qz258) RS553to564.d57) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns552p1824 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 20959099428357097758057 18889465931478580854784 Ns552p228 Ns552p86 

noncomputable def Ns552p1825 := @Enclosure.Real.IsNear.pos_val qz259 20959099428357097758057 18889465931478580854784 Ns552p228 Ns552p86 (Ns552p1824 (RS553to564.d58 qz4 qz35 qz258) RS553to564.d59) rfl 

noncomputable def Ns552p1826 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 944396 1000 944396 1000 

noncomputable def Ns552p1827 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 24255089534174053974781 18889465931478580854784 Ns552p85 

noncomputable def Ns552p1828 := @Ns552p1827 Ns552p86 90537321 2147483648 1213 10737418240 (Ns552p1822 (RS553to564.d4 qz4 qz35 qz258) RS553to564.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1829 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 944396 1000 945649 1000 

noncomputable def Ns552p1830 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 20959099428357097758057 18889465931478580854784 Ns552p228 

noncomputable def Ns552p1831 := @Ns552p1830 Ns552p86 90537321 2147483648 1213 10737418240 (Ns552p1824 (RS553to564.d58 qz4 qz35 qz258) RS553to564.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz545

noncomputable def Ns552p1832 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 944396 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns552p1823 rfl rfl) (Ns552p1825 rfl rfl)) (Ns552p1826 qz11 qz11 rfl rfl rfl rfl (Ns552p1828 rfl)) (Ns552p1829 qz11 qz38 rfl rfl rfl rfl (Ns552p1831 rfl)) 

noncomputable abbrev qz547 := (RS553to564.d3 qz605 qz617 (@Enclosure.dec_le_dec qz605 qz617 945649 1000 946902 1000 qz609 qz621 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns552p1833 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 20959099428357097758057 18889465931478580854784 Ns552p228 Ns552p86 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz605 qz617 945649 1000 946902 1000 qz609 qz621 rfl rfl rfl)

noncomputable abbrev qz262 := qz548

noncomputable def Ns552p1834 := @Enclosure.Real.IsNear.pos_val qz261 20959099428357097758057 18889465931478580854784 Ns552p228 Ns552p86 (Ns552p1833 (RS553to564.d4 qz35 qz62 qz262) RS553to564.d59) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns552p1835 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 752505934595492699979 9444732965739290427392 Ns552p393 Ns552p394 

noncomputable def Ns552p1836 := @Enclosure.Real.IsNear.neg_val qz263 752505934595492699979 9444732965739290427392 Ns552p393 Ns552p394 (Ns552p1835 (RS553to564.d58 qz35 qz62 qz262) RS553to564.d61) rfl 

noncomputable def Ns552p1837 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 944396 1000 945649 1000 

noncomputable def Ns552p1838 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 20959099428357097758057 18889465931478580854784 Ns552p228 

noncomputable def Ns552p1839 := @Ns552p1838 Ns552p86 90537321 2147483648 1213 10737418240 (Ns552p1833 (RS553to564.d4 qz35 qz62 qz262) RS553to564.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1840 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 944396 1000 946902 1000 

noncomputable def Ns552p1841 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 752505934595492699979 9444732965739290427392 Ns552p393 

noncomputable def Ns552p1842 := @Ns552p1841 Ns552p394 90537321 2147483648 1213 10737418240 (Ns552p1835 (RS553to564.d58 qz35 qz62 qz262) RS553to564.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz547

noncomputable def Ns552p1843 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 945649 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns552p1834 rfl rfl) (Ns552p1836 rfl rfl)) (Ns552p1837 qz11 qz38 rfl rfl rfl rfl (Ns552p1839 rfl)) (Ns552p1840 qz11 qz65 rfl rfl rfl rfl (Ns552p1842 rfl)) 

noncomputable abbrev qz549 := (RS553to564.d3 qz617 qz628 (@Enclosure.dec_le_dec qz617 qz628 946902 1000 948154 1000 qz621 qz632 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns552p1844 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 752505934595492699979 9444732965739290427392 Ns552p393 Ns552p394 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz617 qz628 946902 1000 948154 1000 qz621 qz632 rfl rfl rfl)

noncomputable abbrev qz266 := qz550

noncomputable def Ns552p1845 := @Enclosure.Real.IsNear.neg_val qz265 752505934595492699979 9444732965739290427392 Ns552p393 Ns552p394 (Ns552p1844 (RS553to564.d4 qz62 qz80 qz266) RS553to564.d61) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns552p1846 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 55568419368416487535211 75557863725914323419136 Ns552p526 Ns552p527 

noncomputable def Ns552p1847 := @Enclosure.Real.IsNear.pos_val qz267 55568419368416487535211 75557863725914323419136 Ns552p526 Ns552p527 (Ns552p1846 (RS553to564.d58 qz62 qz80 qz266) RS553to564.d62) rfl 

noncomputable def Ns552p1848 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 944396 1000 946902 1000 

noncomputable def Ns552p1849 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 752505934595492699979 9444732965739290427392 Ns552p393 

noncomputable def Ns552p1850 := @Ns552p1849 Ns552p394 90537321 2147483648 1213 10737418240 (Ns552p1844 (RS553to564.d4 qz62 qz80 qz266) RS553to564.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1851 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 944396 1000 948154 1000 

noncomputable def Ns552p1852 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 55568419368416487535211 75557863725914323419136 Ns552p526 

noncomputable def Ns552p1853 := @Ns552p1852 Ns552p527 90537321 2147483648 1213 10737418240 (Ns552p1846 (RS553to564.d58 qz62 qz80 qz266) RS553to564.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz549

noncomputable def Ns552p1854 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 946902 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns552p1845 rfl rfl) (Ns552p1847 rfl rfl)) (Ns552p1848 qz11 qz65 rfl rfl rfl rfl (Ns552p1850 rfl)) (Ns552p1851 qz11 qz83 rfl rfl rfl rfl (Ns552p1853 rfl)) 

noncomputable abbrev qz551 := (RS553to564.d3 qz628 qz640 (@Enclosure.dec_le_dec qz628 qz640 948154 1000 949407 1000 qz632 qz644 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns552p1855 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 55568419368416487535211 75557863725914323419136 Ns552p526 Ns552p527 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz628 qz640 948154 1000 949407 1000 qz632 qz644 rfl rfl rfl)

noncomputable abbrev qz270 := qz552

noncomputable def Ns552p1856 := @Enclosure.Real.IsNear.pos_val qz269 55568419368416487535211 75557863725914323419136 Ns552p526 Ns552p527 (Ns552p1855 (RS553to564.d4 qz80 qz98 qz270) RS553to564.d62) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns552p1857 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 70823066506776545297535 18889465931478580854784 Ns552p666 Ns552p667 

noncomputable def Ns552p1858 := @Enclosure.Real.IsNear.neg_val qz271 70823066506776545297535 18889465931478580854784 Ns552p666 Ns552p667 (Ns552p1857 (RS553to564.d58 qz80 qz98 qz270) RS553to564.d63) rfl 

noncomputable def Ns552p1859 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 944396 1000 948154 1000 

noncomputable def Ns552p1860 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 55568419368416487535211 75557863725914323419136 Ns552p526 

noncomputable def Ns552p1861 := @Ns552p1860 Ns552p527 90537321 2147483648 1213 10737418240 (Ns552p1855 (RS553to564.d4 qz80 qz98 qz270) RS553to564.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1862 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 944396 1000 949407 1000 

noncomputable def Ns552p1863 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 70823066506776545297535 18889465931478580854784 Ns552p666 

noncomputable def Ns552p1864 := @Ns552p1863 Ns552p667 90537321 2147483648 1213 10737418240 (Ns552p1857 (RS553to564.d58 qz80 qz98 qz270) RS553to564.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz551

noncomputable def Ns552p1865 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 948154 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns552p1856 rfl rfl) (Ns552p1858 rfl rfl)) (Ns552p1859 qz11 qz83 rfl rfl rfl rfl (Ns552p1861 rfl)) (Ns552p1862 qz11 qz101 rfl rfl rfl rfl (Ns552p1864 rfl)) 

noncomputable abbrev qz553 := (RS553to564.d3 qz640 qz650 (@Enclosure.dec_le_dec qz640 qz650 949407 1000 950659 1000 qz644 qz654 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns552p1866 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 70823066506776545297535 18889465931478580854784 Ns552p666 Ns552p667 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz640 qz650 949407 1000 950659 1000 qz644 qz654 rfl rfl rfl)

noncomputable abbrev qz274 := qz554

noncomputable def Ns552p1867 := @Enclosure.Real.IsNear.neg_val qz273 70823066506776545297535 18889465931478580854784 Ns552p666 Ns552p667 (Ns552p1866 (RS553to564.d4 qz98 qz116 qz274) RS553to564.d63) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns552p1868 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 25450515602722977295573 18889465931478580854784 145426995959353101853391 Ns552p790 

noncomputable def Ns552p1869 := @Enclosure.Real.IsNear.pos_val qz275 25450515602722977295573 18889465931478580854784 145426995959353101853391 Ns552p790 (Ns552p1868 (RS553to564.d58 qz98 qz116 qz274) RS553to564.d64) rfl 

noncomputable def Ns552p1870 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 944396 1000 949407 1000 

noncomputable def Ns552p1871 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 70823066506776545297535 18889465931478580854784 Ns552p666 

noncomputable def Ns552p1872 := @Ns552p1871 Ns552p667 90537321 2147483648 1213 10737418240 (Ns552p1866 (RS553to564.d4 qz98 qz116 qz274) RS553to564.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1873 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 944396 1000 950659 1000 

noncomputable def Ns552p1874 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 25450515602722977295573 18889465931478580854784 145426995959353101853391 

noncomputable def Ns552p1875 := @Ns552p1874 Ns552p790 90537321 2147483648 1213 10737418240 (Ns552p1868 (RS553to564.d58 qz98 qz116 qz274) RS553to564.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz553

noncomputable def Ns552p1876 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 949407 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns552p1867 rfl rfl) (Ns552p1869 rfl rfl)) (Ns552p1870 qz11 qz101 rfl rfl rfl rfl (Ns552p1872 rfl)) (Ns552p1873 qz11 qz119 rfl rfl rfl rfl (Ns552p1875 rfl)) 

noncomputable abbrev qz555 := (RS553to564.d3 qz650 qz660 (@Enclosure.dec_le_dec qz650 qz660 950659 1000 951910 1000 qz654 qz664 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns552p1877 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 25450515602722977295573 18889465931478580854784 145426995959353101853391 Ns552p790 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz650 qz660 950659 1000 951910 1000 qz654 qz664 rfl rfl rfl)

noncomputable abbrev qz278 := qz556

noncomputable def Ns552p1878 := @Enclosure.Real.IsNear.pos_val qz277 25450515602722977295573 18889465931478580854784 145426995959353101853391 Ns552p790 (Ns552p1877 (RS553to564.d4 qz116 qz134 qz278) RS553to564.d64) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns552p1879 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 318505755791326701065179 75557863725914323419136 Ns552p913 Ns552p527 

noncomputable def Ns552p1880 := @Enclosure.Real.IsNear.neg_val qz279 318505755791326701065179 75557863725914323419136 Ns552p913 Ns552p527 (Ns552p1879 (RS553to564.d58 qz116 qz134 qz278) RS553to564.d65) rfl 

noncomputable def Ns552p1881 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 944396 1000 950659 1000 

noncomputable def Ns552p1882 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 25450515602722977295573 18889465931478580854784 145426995959353101853391 

noncomputable def Ns552p1883 := @Ns552p1882 Ns552p790 90537321 2147483648 1213 10737418240 (Ns552p1877 (RS553to564.d4 qz116 qz134 qz278) RS553to564.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1884 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 944396 1000 951910 1000 

noncomputable def Ns552p1885 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 318505755791326701065179 75557863725914323419136 Ns552p913 

noncomputable def Ns552p1886 := @Ns552p1885 Ns552p527 90537321 2147483648 1213 10737418240 (Ns552p1879 (RS553to564.d58 qz116 qz134 qz278) RS553to564.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz555

noncomputable def Ns552p1887 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 950659 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns552p1878 rfl rfl) (Ns552p1880 rfl rfl)) (Ns552p1881 qz11 qz119 rfl rfl rfl rfl (Ns552p1883 rfl)) (Ns552p1884 qz11 qz137 rfl rfl rfl rfl (Ns552p1886 rfl)) 

noncomputable abbrev qz557 := (RS553to564.d3 qz660 qz670 (@Enclosure.dec_le_dec qz660 qz670 951910 1000 953162 1000 qz664 qz674 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns552p1888 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 318505755791326701065179 75557863725914323419136 Ns552p913 Ns552p527 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz660 qz670 951910 1000 953162 1000 qz664 qz674 rfl rfl rfl)

noncomputable abbrev qz282 := qz558

noncomputable def Ns552p1889 := @Enclosure.Real.IsNear.neg_val qz281 318505755791326701065179 75557863725914323419136 Ns552p913 Ns552p527 (Ns552p1888 (RS553to564.d4 qz134 qz152 qz282) RS553to564.d65) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns552p1890 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz152) Bool.false 42986602887218256690519 18889465931478580854784 232915009649860452692853 Ns552p1044 

noncomputable def Ns552p1891 := @Enclosure.Real.IsNear.pos_val qz283 42986602887218256690519 18889465931478580854784 232915009649860452692853 Ns552p1044 (Ns552p1890 (RS553to564.d58 qz134 qz152 qz282) RS553to564.d66) rfl 

noncomputable def Ns552p1892 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 944396 1000 951910 1000 

noncomputable def Ns552p1893 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 318505755791326701065179 75557863725914323419136 Ns552p913 

noncomputable def Ns552p1894 := @Ns552p1893 Ns552p527 90537321 2147483648 1213 10737418240 (Ns552p1888 (RS553to564.d4 qz134 qz152 qz282) RS553to564.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1895 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz152 944396 1000 953162 1000 

noncomputable def Ns552p1896 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 42986602887218256690519 18889465931478580854784 232915009649860452692853 

noncomputable def Ns552p1897 := @Ns552p1896 Ns552p1044 90537321 2147483648 1213 10737418240 (Ns552p1890 (RS553to564.d58 qz134 qz152 qz282) RS553to564.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz557

noncomputable def Ns552p1898 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 951910 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns552p1889 rfl rfl) (Ns552p1891 rfl rfl)) (Ns552p1892 qz11 qz137 rfl rfl rfl rfl (Ns552p1894 rfl)) (Ns552p1895 qz11 qz155 rfl rfl rfl rfl (Ns552p1897 rfl)) 

noncomputable abbrev qz559 := (RS553to564.d3 qz670 qz681 (@Enclosure.dec_le_dec qz670 qz681 953162 1000 954413 1000 qz674 qz685 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns552p1899 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz152) Bool.false 42986602887218256690519 18889465931478580854784 232915009649860452692853 Ns552p1044 

noncomputable abbrev qz560 := (@Enclosure.dec_le_dec qz670 qz681 953162 1000 954413 1000 qz674 qz685 rfl rfl rfl)

noncomputable abbrev qz286 := qz560

noncomputable def Ns552p1900 := @Enclosure.Real.IsNear.pos_val qz285 42986602887218256690519 18889465931478580854784 232915009649860452692853 Ns552p1044 (Ns552p1899 (RS553to564.d4 qz152 qz170 qz286) RS553to564.d66) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns552p1901 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 96243326520388967310159 151115727451828646838272 Ns552p1170 Ns552p1171 

noncomputable def Ns552p1902 := @Enclosure.Real.IsNear.neg_val qz287 96243326520388967310159 151115727451828646838272 Ns552p1170 Ns552p1171 (Ns552p1901 (RS553to564.d58 qz152 qz170 qz286) RS553to564.d67) rfl 

noncomputable def Ns552p1903 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz152 944396 1000 953162 1000 

noncomputable def Ns552p1904 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 42986602887218256690519 18889465931478580854784 232915009649860452692853 

noncomputable def Ns552p1905 := @Ns552p1904 Ns552p1044 90537321 2147483648 1213 10737418240 (Ns552p1899 (RS553to564.d4 qz152 qz170 qz286) RS553to564.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1906 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 944396 1000 954413 1000 

noncomputable def Ns552p1907 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 96243326520388967310159 151115727451828646838272 Ns552p1170 

noncomputable def Ns552p1908 := @Ns552p1907 Ns552p1171 90537321 2147483648 1213 10737418240 (Ns552p1901 (RS553to564.d58 qz152 qz170 qz286) RS553to564.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz559

noncomputable def Ns552p1909 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz152 953162 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns552p1900 rfl rfl) (Ns552p1902 rfl rfl)) (Ns552p1903 qz11 qz155 rfl rfl rfl rfl (Ns552p1905 rfl)) (Ns552p1906 qz11 qz173 rfl rfl rfl rfl (Ns552p1908 rfl)) 

noncomputable abbrev qz734 := (@Enclosure.dec_le_dec qz779 qz783 954413 1000 955663 1000 (@Eq.refl Real qz779) (@Eq.refl Real qz783) rfl rfl rfl)

noncomputable abbrev qz561 := (RS553to564.d3 qz681 qz691 qz734)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns552p1910 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 96243326520388967310159 151115727451828646838272 Ns552p1170 Ns552p1171 

noncomputable abbrev qz562 := qz734

noncomputable abbrev qz290 := qz562

noncomputable def Ns552p1911 := @Enclosure.Real.IsNear.neg_val qz289 96243326520388967310159 151115727451828646838272 Ns552p1170 Ns552p1171 (Ns552p1910 (RS553to564.d4 qz170 qz188 qz290) RS553to564.d67) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns552p1912 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz188) Bool.false 449076858765585139131465 151115727451828646838272 Ns552p1296 Ns552p1171 

noncomputable def Ns552p1913 := @Enclosure.Real.IsNear.pos_val qz291 449076858765585139131465 151115727451828646838272 Ns552p1296 Ns552p1171 (Ns552p1912 (RS553to564.d58 qz170 qz188 qz290) RS553to564.d68) rfl 

noncomputable def Ns552p1914 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 944396 1000 954413 1000 

noncomputable def Ns552p1915 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 96243326520388967310159 151115727451828646838272 Ns552p1170 

noncomputable def Ns552p1916 := @Ns552p1915 Ns552p1171 90537321 2147483648 1213 10737418240 (Ns552p1910 (RS553to564.d4 qz170 qz188 qz290) RS553to564.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1917 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz188 944396 1000 955663 1000 

noncomputable def Ns552p1918 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 449076858765585139131465 151115727451828646838272 Ns552p1296 

noncomputable def Ns552p1919 := @Ns552p1918 Ns552p1171 90537321 2147483648 1213 10737418240 (Ns552p1912 (RS553to564.d58 qz170 qz188 qz290) RS553to564.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz561

noncomputable def Ns552p1920 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 954413 1000 qz173 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns552p1911 rfl rfl) (Ns552p1913 rfl rfl)) (Ns552p1914 qz11 qz173 rfl rfl rfl rfl (Ns552p1916 rfl)) (Ns552p1917 qz11 qz191 rfl rfl rfl rfl (Ns552p1919 rfl)) 

noncomputable abbrev qz735 := (@Enclosure.dec_le_dec qz783 qz787 955663 1000 956914 1000 (@Eq.refl Real qz783) qz790 rfl rfl rfl)

noncomputable abbrev qz563 := (RS553to564.d3 qz691 qz701 qz735)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns552p1921 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz188) Bool.false 449076858765585139131465 151115727451828646838272 Ns552p1296 Ns552p1171 

noncomputable abbrev qz564 := qz735

noncomputable abbrev qz294 := qz564

noncomputable def Ns552p1922 := @Enclosure.Real.IsNear.pos_val qz293 449076858765585139131465 151115727451828646838272 Ns552p1296 Ns552p1171 (Ns552p1921 (RS553to564.d4 qz188 qz206 qz294) RS553to564.d68) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns552p1923 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz206) Bool.true 10252706394450110768869 18889465931478580854784 Ns552p1430 Ns552p86 

noncomputable def Ns552p1924 := @Enclosure.Real.IsNear.neg_val qz295 10252706394450110768869 18889465931478580854784 Ns552p1430 Ns552p86 (Ns552p1923 (RS553to564.d58 qz188 qz206 qz294) RS553to564.d69) rfl 

noncomputable def Ns552p1925 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz188 944396 1000 955663 1000 

noncomputable def Ns552p1926 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 449076858765585139131465 151115727451828646838272 Ns552p1296 

noncomputable def Ns552p1927 := @Ns552p1926 Ns552p1171 90537321 2147483648 1213 10737418240 (Ns552p1921 (RS553to564.d4 qz188 qz206 qz294) RS553to564.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1928 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz206 944396 1000 956914 1000 

noncomputable def Ns552p1929 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 10252706394450110768869 18889465931478580854784 Ns552p1430 

noncomputable def Ns552p1930 := @Ns552p1929 Ns552p86 90537321 2147483648 1213 10737418240 (Ns552p1923 (RS553to564.d58 qz188 qz206 qz294) RS553to564.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz563

noncomputable def Ns552p1931 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz188 955663 1000 qz191 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns552p1922 rfl rfl) (Ns552p1924 rfl rfl)) (Ns552p1925 qz11 qz191 rfl rfl rfl rfl (Ns552p1927 rfl)) (Ns552p1928 qz11 qz209 rfl rfl rfl rfl (Ns552p1930 rfl)) 

noncomputable abbrev qz736 := (@Enclosure.dec_le_dec qz787 qz792 956914 1000 958164 1000 qz790 qz795 rfl rfl rfl)

noncomputable abbrev qz565 := (RS553to564.d3 qz701 qz712 qz736)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns552p1932 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz206) Bool.true 10252706394450110768869 18889465931478580854784 Ns552p1430 Ns552p86 

noncomputable abbrev qz566 := qz736

noncomputable abbrev qz298 := qz566

noncomputable def Ns552p1933 := @Enclosure.Real.IsNear.neg_val qz297 10252706394450110768869 18889465931478580854784 Ns552p1430 Ns552p86 (Ns552p1932 (RS553to564.d4 qz206 qz223 qz298) RS553to564.d69) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns552p1934 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 10391329048040396667919 18889465931478580854784 93504723916389939437197 Ns552p1564 

noncomputable def Ns552p1935 := @Enclosure.Real.IsNear.pos_val qz299 10391329048040396667919 18889465931478580854784 93504723916389939437197 Ns552p1564 (Ns552p1934 (RS553to564.d58 qz206 qz223 qz298) RS553to564.d70) rfl 

noncomputable def Ns552p1936 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz206 944396 1000 956914 1000 

noncomputable def Ns552p1937 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 10252706394450110768869 18889465931478580854784 Ns552p1430 

noncomputable def Ns552p1938 := @Ns552p1937 Ns552p86 90537321 2147483648 1213 10737418240 (Ns552p1932 (RS553to564.d4 qz206 qz223 qz298) RS553to564.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1939 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 944396 1000 958164 1000 

noncomputable def Ns552p1940 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 10391329048040396667919 18889465931478580854784 93504723916389939437197 

noncomputable def Ns552p1941 := @Ns552p1940 Ns552p1564 90537321 2147483648 1213 10737418240 (Ns552p1934 (RS553to564.d58 qz206 qz223 qz298) RS553to564.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz565

noncomputable def Ns552p1942 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz206 956914 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns552p1933 rfl rfl) (Ns552p1935 rfl rfl)) (Ns552p1936 qz11 qz209 rfl rfl rfl rfl (Ns552p1938 rfl)) (Ns552p1939 qz11 qz226 rfl rfl rfl rfl (Ns552p1941 rfl)) 

noncomputable abbrev qz802 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 958164 1000) (Enclosure.sfrac Bool.false 959413 1000) 958164 1000 959413 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 958164 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 959413 1000)) rfl rfl rfl)

noncomputable abbrev qz737 := qz802

noncomputable abbrev qz567 := (RS553to564.d3 qz712 qz723 qz737)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz567)

noncomputable def Ns552p1943 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 10391329048040396667919 18889465931478580854784 93504723916389939437197 Ns552p1564 

noncomputable abbrev qz568 := qz737

noncomputable abbrev qz302 := qz568

noncomputable def Ns552p1944 := @Enclosure.Real.IsNear.pos_val qz301 10391329048040396667919 18889465931478580854784 93504723916389939437197 Ns552p1564 (Ns552p1943 (RS553to564.d4 qz223 qz240 qz302) RS553to564.d70) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz567)

noncomputable def Ns552p1945 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 21009521823027024083369 75557863725914323419136 Ns552p1692 Ns552p394 

noncomputable def Ns552p1946 := @Enclosure.Real.IsNear.neg_val qz303 21009521823027024083369 75557863725914323419136 Ns552p1692 Ns552p394 (Ns552p1945 (RS553to564.d58 qz223 qz240 qz302) RS553to564.d71) rfl 

noncomputable def Ns552p1947 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 944396 1000 958164 1000 

noncomputable def Ns552p1948 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 10391329048040396667919 18889465931478580854784 93504723916389939437197 

noncomputable def Ns552p1949 := @Ns552p1948 Ns552p1564 90537321 2147483648 1213 10737418240 (Ns552p1943 (RS553to564.d4 qz223 qz240 qz302) RS553to564.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable def Ns552p1950 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 944396 1000 959413 1000 

noncomputable def Ns552p1951 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 21009521823027024083369 75557863725914323419136 Ns552p1692 

noncomputable def Ns552p1952 := @Ns552p1951 Ns552p394 90537321 2147483648 1213 10737418240 (Ns552p1945 (RS553to564.d58 qz223 qz240 qz302) RS553to564.d71) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 90537321 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS553to564.d60) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz567

noncomputable def Ns552p1953 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 958164 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns552p1944 rfl rfl) (Ns552p1946 rfl rfl)) (Ns552p1947 qz11 qz226 rfl rfl rfl rfl (Ns552p1949 rfl)) (Ns552p1950 qz11 qz243 rfl rfl rfl rfl (Ns552p1952 rfl)) 

noncomputable def Ns552p1954 := @List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns552p1942)) (@List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns552p1953)) (@List.nil RS553to564.d0)) 

noncomputable def Ns552p1955 := @List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns552p1920)) (@List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns552p1931)) Ns552p1954) 

noncomputable def Ns552p1956 := @List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns552p1898)) (@List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns552p1909)) Ns552p1955) 

noncomputable def Ns552p1957 := @List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns552p1876)) (@List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns552p1887)) Ns552p1956) 

noncomputable def Ns552p1958 := @List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns552p1854)) (@List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns552p1865)) Ns552p1957) 

noncomputable def Ns552p1959 := @List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns552p1832)) (@List.cons RS553to564.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns552p1843)) Ns552p1958) 

noncomputable abbrev qz569 := (RS553to564.d2 qz681 qz691 qz734)

noncomputable abbrev qz738 := (RS553to564.d2 qz787 qz792 (@Enclosure.dec_le_dec qz787 qz792 956914 1000 958164 1000 qz790 qz795 rfl rfl rfl))

noncomputable abbrev qz739 := (@List.cons RS553to564.d1 (RS553to564.d2 qz792 qz797 qz802) (@List.nil RS553to564.d1))

noncomputable abbrev qz570 := (@List.cons RS553to564.d1 (RS553to564.d2 qz691 qz701 qz735) (@List.cons RS553to564.d1 qz738 qz739))

noncomputable abbrev qz305 := (@List.cons RS553to564.d1 (RS553to564.d2 qz470 qz483 qz560) (@List.cons RS553to564.d1 qz569 qz570))

noncomputable def Ns552p1960 := @List.cons RS553to564.d1 (RS553to564.d2 qz116 qz134 qz278) (@List.cons RS553to564.d1 (RS553to564.d2 qz134 qz152 qz282) qz305) 

noncomputable abbrev qz306 := (RS553to564.d2 qz431 qz444 qz554)

noncomputable def Ns552p1961 := @List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 qz306 (RS553to564.d2 qz116 qz134 qz278) (@List.cons RS553to564.d1 (RS553to564.d2 qz134 qz152 qz282) qz305) 

noncomputable def Ns552p1962 := @List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 (RS553to564.d2 qz116 qz134 qz278) (RS553to564.d2 qz134 qz152 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 951910 1000 951910 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS553to564.d2 qz470 qz483 qz560)

noncomputable abbrev qz308 := qz569

noncomputable abbrev qz309 := qz570

noncomputable abbrev qz571 := (RS553to564.d2 qz691 qz701 qz735)

noncomputable abbrev qz310 := qz571

noncomputable abbrev qz572 := (@List.cons RS553to564.d1 qz738 qz739)

noncomputable abbrev qz311 := qz572

noncomputable abbrev qz573 := qz738

noncomputable abbrev qz312 := qz573

noncomputable abbrev qz574 := qz739

noncomputable abbrev qz313 := qz574

noncomputable abbrev qz740 := (RS553to564.d2 qz792 qz797 qz802)

noncomputable abbrev qz575 := qz740

noncomputable abbrev qz314 := qz575

noncomputable def Ns552p1963 := @List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 954413 1000 954413 1000 qz173 qz173 rfl rfl rfl) (@List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz188 qz188 955663 1000 955663 1000 qz191 qz191 rfl rfl rfl) (@List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz206 qz206 956914 1000 956914 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 qz312 qz314 (@List.nil RS553to564.d1) (@Enclosure.dec_le_dec qz223 qz223 958164 1000 958164 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS553to564.d1 RS553to564.d72 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS553to564.d1 qz569 qz570)

noncomputable def Ns552p1964 := @List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 (RS553to564.d2 qz134 qz152 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz152 qz152 953162 1000 953162 1000 qz155 qz155 rfl rfl rfl) Ns552p1963 

noncomputable def Ns552p1965 := @List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 (RS553to564.d2 qz4 qz35 qz258) (RS553to564.d2 qz35 qz62 qz262) (@List.cons RS553to564.d1 (RS553to564.d2 qz62 qz80 qz266) (@List.cons RS553to564.d1 (RS553to564.d2 qz80 qz98 qz270) (@List.cons RS553to564.d1 qz306 Ns552p1960))) (@Enclosure.dec_le_dec qz35 qz35 945649 1000 945649 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 (RS553to564.d2 qz35 qz62 qz262) (RS553to564.d2 qz62 qz80 qz266) (@List.cons RS553to564.d1 (RS553to564.d2 qz80 qz98 qz270) (@List.cons RS553to564.d1 qz306 Ns552p1960)) (@Enclosure.dec_le_dec qz62 qz62 946902 1000 946902 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 (RS553to564.d2 qz62 qz80 qz266) (RS553to564.d2 qz80 qz98 qz270) (@List.cons RS553to564.d1 qz306 Ns552p1960) (@Enclosure.dec_le_dec qz80 qz80 948154 1000 948154 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS553to564.d1 RS553to564.d72 (RS553to564.d2 qz80 qz98 qz270) qz306 Ns552p1960 (@Enclosure.dec_le_dec qz98 qz98 949407 1000 949407 1000 qz101 qz101 rfl rfl rfl) (Ns552p1961 (@Enclosure.dec_le_dec qz116 qz116 950659 1000 950659 1000 qz119 qz119 rfl rfl rfl) (Ns552p1962 Ns552p1964))))) 

noncomputable abbrev qz576 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz577 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns552p1959 Ns552p1965)

noncomputable abbrev qz578 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns552p1959 Ns552p1965))

theorem RS553to564.d73 : Zeta.Certificates.BatchSpec 12 944396 1000 959413 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz577 (@And.intro (@Eq Nat (@List.length qz576 qz578) 12) (And (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 qz578)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 qz578)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz576 qz578)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz576 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz576 qz578)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 944396 1000 959413 1000 := RS553to564.d73
#print axioms solution
#check solution
