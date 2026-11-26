-- Prove2me | solution 1 for RHHeight1000.rs_main_0529_0540
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:25:54.002233+00:00
-- url     : https://prove2.me/submissions/4a2633fa-8d98-40b1-80c2-1164e33efb3f

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

noncomputable def RS529to540.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS529to540.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS529to540.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS529to540.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS529to540.d2 a b h 

theorem RS529to540.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS529to540.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS529to540.d3 a b h)) 

noncomputable def Ns528p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns528p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns528p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns528p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns528p0 Ns528p1 Ns528p2 Ns528p1 614572177 536870912 1 144000000 614572177 536870912 1 144000000 307286088 268435456 3 268435456 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns528p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns528p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns528p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns528p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns528p8 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625 

noncomputable def Ns528p9 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575 

noncomputable def Ns528p10 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375 

noncomputable def Ns528p11 := BSN.log_dyadic_bound Ns528p6 Ns528p7 16 15 Ns528p8 536870912 144000000 Ns528p9 Ns528p10 614572177 Ns528p4 Ns528p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns528p6) (BSN.artanhQ Ns528p7) 0 15 Ns528p9 Ns528p8 Ns528p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns528p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns528p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns528p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns528p15 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625 

noncomputable def Ns528p16 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575 

noncomputable def Ns528p17 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375 

noncomputable def Ns528p18 := BSN.log_dyadic_bound Ns528p13 Ns528p14 16 15 Ns528p15 536870912 144000000 Ns528p16 Ns528p17 614572177 Ns528p12 Ns528p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns528p13) (BSN.artanhQ Ns528p14) 0 15 Ns528p16 Ns528p15 Ns528p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns528p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 307286088 268435456 3 268435456 38410761 33554432 3 268435456 (Ns528p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns528p0 Ns528p1 614572177 536870912 1 144000000 Bool.false (BSN.logfrac_isNear Ns528p4 Ns528p5 1 Ns528p0 Ns528p1 614572177 536870912 144000000 rfl rfl rfl (Ns528p11 rfl))) (BSN.isNear_log_sfrac Ns528p2 Ns528p1 614572177 536870912 1 144000000 Bool.false (BSN.logfrac_isNear Ns528p12 Ns528p5 1 Ns528p2 Ns528p1 614572177 536870912 144000000 rfl rfl rfl (Ns528p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS529to540.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 3 268435456 := Ns528p19 

noncomputable def Ns528p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 33554432 9000000 385100712855 135135 23258159 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz316 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz0 := qz316

theorem RS529to540.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 23258159 33554432 1 9000000 := BSN.isNear_log_sfrac 2 1 23258159 33554432 1 9000000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 23258159 33554432 9000000 rfl rfl rfl (Ns528p20 rfl)) 

theorem RS529to540.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 372130544 536870912 60 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 23258159 33554432 1 9000000 372130544 536870912 60 536870912 RS529to540.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz575 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz575

noncomputable def Ns528p21 := @Enclosure.Real.IsNear.inv_image qz317 94906265 67108864 1 67108864 23726566 23726567 33554432 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 94906265 67108864 1 67108864 (BSN.sqrt_enclosure 2 1 47453132 47453133 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS529to540.d8 : Enclosure.Real.IsNear qz320 Bool.false 47453133 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 47453133 67108864 1 67108864 (Ns528p21 rfl rfl) rfl 

theorem RS529to540.d9 : Enclosure.Real.IsNear qz320 Bool.false 379625064 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 379625064 536870912 8 536870912 RS529to540.d8 rfl 

noncomputable def Ns528p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 33554432 9000000 13079757671720842725 316234143225 36863311 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS529to540.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 9000000 := BSN.isNear_log_sfrac 3 1 36863311 33554432 1 9000000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 36863311 33554432 9000000 rfl rfl rfl (Ns528p22 rfl)) 

theorem RS529to540.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 589812976 536870912 60 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 9000000 589812976 536870912 60 536870912 RS529to540.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns528p23 := @Enclosure.Real.IsNear.inv_image qz321 116235963 67108864 1 67108864 19372660 19372661 33554432 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 116235963 67108864 1 67108864 (BSN.sqrt_enclosure 3 1 58117981 58117982 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS529to540.d12 : Enclosure.Real.IsNear qz323 Bool.false 38745321 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 38745321 67108864 1 67108864 (Ns528p23 rfl rfl) rfl 

theorem RS529to540.d13 : Enclosure.Real.IsNear qz323 Bool.false 309962568 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 309962568 536870912 8 536870912 RS529to540.d12 rfl 

noncomputable def Ns528p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns528p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns528p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns528p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns528p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns528p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns528p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns528p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns528p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns528p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns528p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns528p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns528p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns528p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns528p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns528p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns528p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns528p25 Ns528p26 Ns528p27 Ns528p28 200200021673987500790625 Ns528p29 Ns528p30 Ns528p31 Ns528p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns528p32 Ns528p33 151412625 Ns528p34 Ns528p35 1322214852783825 Ns528p27 Ns528p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns528p32 Ns528p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns528p34 Ns528p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns528p36 Ns528p37 1267389585 Ns528p38 Ns528p39 1927077560082675 Ns528p29 Ns528p30 Ns528p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns528p36 Ns528p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns528p38 Ns528p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS529to540.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns528p24 Ns528p25 1 Ns528p26 := Ns528p40 rfl rfl rfl 

noncomputable def Ns528p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns528p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns528p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns528p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns528p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns528p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns528p25 Ns528p26 Ns528p42 Ns528p43 9945 Ns528p44 Ns528p45 65835 Ns528p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns528p42 Ns528p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns528p44 Ns528p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS529to540.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns528p41 Ns528p25 1 Ns528p26 := Ns528p46 rfl 

noncomputable def Ns528p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns528p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS529to540.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns528p47 Ns528p25 1 Ns528p48 := BSN.pi_combine Ns528p24 Ns528p41 Ns528p25 Ns528p26 Ns528p48 Ns528p47 rfl rfl rfl rfl RS529to540.d14 RS529to540.d15 

theorem RS529to540.d17 : Enclosure.Real.IsNear Real.pi Bool.false 28296951008113761 9007199254740992 1 9007199254740992 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns528p47 Ns528p25 1 Ns528p48 28296951008113761 9007199254740992 1 9007199254740992 RS529to540.d16 rfl 

noncomputable def Ns528p49 := nat_lit 129013261453190219981479458510875701904296875 

noncomputable def Ns528p50 := nat_lit 20028702544022979302942508184499384445755625 

noncomputable def Ns528p51 := nat_lit 105610919306899072369715234453255625 

noncomputable def Ns528p52 := nat_lit 11743816085855617508865225 

noncomputable def Ns528p53 := nat_lit 24536140990734100341796875 

noncomputable def Ns528p54 := BSN.log_dyadic_bound 3 5 18 17 Ns528p49 33554432 9000000 Ns528p50 Ns528p51 46516319 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 3) (BSN.artanhQ 5) 0 17 8 816252149187356400 5258090972900390625 87256779635025 Ns528p52 Ns528p53 1210346287688420415225 Ns528p50 Ns528p49 Ns528p51 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 3) (BSN.artanhQ 5) 0 8 816252149187356400 5258090972900390625 87256779635025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 3) (BSN.artanhQ 5) 8 17 Ns528p52 Ns528p53 1210346287688420415225 rfl rfl rfl rfl)) rfl rfl 

theorem RS529to540.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 9000000 := BSN.isNear_log_sfrac 4 1 46516319 33554432 1 9000000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 46516319 33554432 9000000 rfl rfl rfl (Ns528p54 rfl rfl)) 

theorem RS529to540.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 744261104 536870912 60 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 9000000 744261104 536870912 60 536870912 RS529to540.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns528p55 := @Enclosure.Real.IsNear.inv_image qz325 134217729 67108864 1 67108864 16777215 16777216 33554432 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 134217729 67108864 1 67108864 (BSN.sqrt_enclosure 4 1 67108864 67108865 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS529to540.d20 : Enclosure.Real.IsNear qz327 Bool.false 33554431 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 33554431 67108864 1 67108864 (Ns528p55 rfl rfl) rfl 

theorem RS529to540.d21 : Enclosure.Real.IsNear qz327 Bool.false 268435448 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 268435448 536870912 8 536870912 RS529to540.d20 rfl 

noncomputable def Ns528p56 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns528p57 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns528p58 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns528p59 := nat_lit 885951608314392539099884620 

noncomputable def Ns528p60 := nat_lit 1286943652057122751813246125 

noncomputable def Ns528p61 := BSN.log_dyadic_bound 2 3 22 21 Ns528p56 33554432 9000000 Ns528p57 Ns528p58 54003774 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns528p59 Ns528p60 84004523356416638976000 Ns528p57 Ns528p56 Ns528p58 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns528p59 Ns528p60 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS529to540.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 9000000 := BSN.isNear_log_sfrac 5 1 54003774 33554432 1 9000000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 9000000 rfl rfl rfl (Ns528p61 rfl rfl)) 

theorem RS529to540.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 864060384 536870912 60 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 9000000 864060384 536870912 60 536870912 RS529to540.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns528p62 := @Enclosure.Real.IsNear.inv_image qz328 150059981 67108864 1 67108864 15005998 15005999 33554432 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 150059981 67108864 1 67108864 (BSN.sqrt_enclosure 5 1 75029990 75029991 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS529to540.d24 : Enclosure.Real.IsNear qz329 Bool.false 30011997 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 30011997 67108864 1 67108864 (Ns528p62 rfl rfl) rfl 

theorem RS529to540.d25 : Enclosure.Real.IsNear qz329 Bool.false 240095976 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 240095976 536870912 8 536870912 RS529to540.d24 rfl 

noncomputable def Ns528p63 := nat_lit 2166104270535356806332416 

noncomputable def Ns528p64 := nat_lit 1208925819614629174706176 

noncomputable def Ns528p65 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 33554432 9000000 1420244935680 967680 13605151 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz575)

theorem RS529to540.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 500000009 4500000000000000 := BSN.isNear_log_sfrac 6 1 4034683612241143 2251799813685248 500000009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false Ns528p63 Ns528p64 1000000018000000 9000000000000000000000 4034683612241143 2251799813685248 500000009 4500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 13605151 33554432 24973259072661432 36028797018963968 9000000 1000000000000000 rfl rfl rfl rfl (Ns528p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS529to540.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 961943533 536870912 61 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 500000009 4500000000000000 961943533 536870912 61 536870912 RS529to540.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns528p66 := @Enclosure.Real.IsNear.inv_image qz331 164382475 67108864 1 67108864 13698539 13698540 33554432 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 164382475 67108864 1 67108864 (BSN.sqrt_enclosure 6 1 82191237 82191238 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS529to540.d28 : Enclosure.Real.IsNear qz332 Bool.false 27397079 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 27397079 67108864 1 67108864 (Ns528p66 rfl rfl) rfl 

theorem RS529to540.d29 : Enclosure.Real.IsNear qz332 Bool.false 219176632 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 219176632 536870912 8 536870912 RS529to540.d28 rfl 

noncomputable def Ns528p67 := nat_lit 2352460989330532755046400 

noncomputable def Ns528p68 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 33554432 9000000 11010900719820672 5524329195 18777589 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz575)

theorem RS529to540.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 500000009 4500000000000000 := BSN.isNear_log_sfrac 7 1 4381800050531575 2251799813685248 500000009 4500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false Ns528p67 Ns528p64 1000000018000000 9000000000000000000000 4381800050531575 2251799813685248 500000009 4500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 18777589 33554432 24973259072661432 36028797018963968 9000000 1000000000000000 rfl rfl rfl rfl (Ns528p68 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS529to540.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 1044702541 536870912 61 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 500000009 4500000000000000 1044702541 536870912 61 536870912 RS529to540.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns528p69 := @Enclosure.Real.IsNear.inv_image qz334 177553365 67108864 1 67108864 12682383 12682384 33554432 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 177553365 67108864 1 67108864 (BSN.sqrt_enclosure 7 1 88776682 88776683 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS529to540.d32 : Enclosure.Real.IsNear qz335 Bool.false 25364767 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 25364767 67108864 1 67108864 (Ns528p69 rfl rfl) rfl 

theorem RS529to540.d33 : Enclosure.Real.IsNear qz335 Bool.false 202918136 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 202918136 536870912 8 536870912 RS529to540.d32 rfl 

noncomputable def Ns528p70 := nat_lit 2513890570116003237199872 

noncomputable def Ns528p71 := BSN.log_dyadic_bound 0 16 1 0 1 33554432 9000000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz575)

theorem RS529to540.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 1000000027 9000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns528p70 Ns528p64 1000000027000000 9000000000000000000000 9364972152248037 4503599627370496 1000000027 9000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 33554432 24973259072661432 36028797018963968 9000000 1000000000000000 rfl rfl rfl rfl (Ns528p71 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS529to540.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 1116391676 536870912 61 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 1000000027 9000000000000000 1116391676 536870912 61 536870912 RS529to540.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns528p72 := @Enclosure.Real.IsNear.inv_image qz337 189812531 67108864 1 67108864 11863283 11863284 33554432 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 189812531 67108864 1 67108864 (BSN.sqrt_enclosure 8 1 94906265 94906266 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS529to540.d36 : Enclosure.Real.IsNear qz338 Bool.false 23726567 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 23726567 67108864 1 67108864 (Ns528p72 rfl rfl) rfl 

theorem RS529to540.d37 : Enclosure.Real.IsNear qz338 Bool.false 189812536 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 189812536 536870912 8 536870912 RS529to540.d36 rfl 

noncomputable def Ns528p73 := nat_lit 2656281492024125531619328 

noncomputable def Ns528p74 := BSN.log_dyadic_bound 1 17 3 2 1252815 33554432 9000000 1448 3 3952142 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz575)

theorem RS529to540.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 1000000027 9000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 1000000027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns528p73 Ns528p64 1000000027000000 9000000000000000000000 9895419672221413 4503599627370496 1000000027 9000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 3952142 33554432 24973259072661432 36028797018963968 9000000 1000000000000000 rfl rfl rfl rfl (Ns528p74 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS529to540.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 1179625948 536870912 61 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 1000000027 9000000000000000 1179625948 536870912 61 536870912 RS529to540.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns528p75 := @Enclosure.Real.IsNear.inv_image qz340 201326593 67108864 1 67108864 11184810 11184811 33554432 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 201326593 67108864 1 67108864 (BSN.sqrt_enclosure 9 1 100663296 100663297 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS529to540.d40 : Enclosure.Real.IsNear qz341 Bool.false 22369621 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 22369621 67108864 1 67108864 (Ns528p75 rfl rfl) rfl 

theorem RS529to540.d41 : Enclosure.Real.IsNear qz341 Bool.false 178956968 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 178956968 536870912 8 536870912 RS529to540.d40 rfl 

noncomputable def Ns528p76 := nat_lit 2783654566499630094221312 

noncomputable def Ns528p77 := BSN.log_dyadic_bound 2 18 4 3 3571283520 33554432 9000000 14806464 960 7487455 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz575)

theorem RS529to540.d42 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 1000000027 9000000000000000 := BSN.isNear_log_sfrac 10 1 10369921350850277 4503599627370496 1000000027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false Ns528p76 Ns528p64 1000000027000000 9000000000000000000000 10369921350850277 4503599627370496 1000000027 9000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 7487455 33554432 24973259072661432 36028797018963968 9000000 1000000000000000 rfl rfl rfl rfl (Ns528p77 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS529to540.d43 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 1236190956 536870912 61 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 1000000027 9000000000000000 1236190956 536870912 61 536870912 RS529to540.d42 rfl 

noncomputable abbrev qz343 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns528p78 := @Enclosure.Real.IsNear.inv_image qz343 212216861 67108864 1 67108864 10610843 10610844 33554432 (@Enclosure.Real.IsNear.of_eq qz343 (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 212216861 67108864 1 67108864 (BSN.sqrt_enclosure 10 1 106108430 106108431 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz344 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS529to540.d44 : Enclosure.Real.IsNear qz344 Bool.false 21221687 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 21221687 67108864 1 67108864 (Ns528p78 rfl rfl) rfl 

theorem RS529to540.d45 : Enclosure.Real.IsNear qz344 Bool.false 169773496 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 169773496 536870912 8 536870912 RS529to540.d44 rfl 

noncomputable def Ns528p79 := nat_lit 2898877505641241362038784 

noncomputable def Ns528p80 := BSN.log_dyadic_bound 3 19 5 4 16049467073745 33554432 9000000 135406373544 688905 10685534 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 19) 0 4 135406373544 16049467073745 688905 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11) qz575)

theorem RS529to540.d46 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 1000000027 9000000000000000 := BSN.isNear_log_sfrac 11 1 10799160248194789 4503599627370496 1000000027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false Ns528p79 Ns528p64 1000000027000000 9000000000000000000000 10799160248194789 4503599627370496 1000000027 9000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 10685534 33554432 24973259072661432 36028797018963968 9000000 1000000000000000 rfl rfl rfl rfl (Ns528p80 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS529to540.d47 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 1287360220 536870912 61 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 1000000027 9000000000000000 1287360220 536870912 61 536870912 RS529to540.d46 rfl 

noncomputable abbrev qz346 := (Real.sqrt (@Nat.cast Real Real.instNatCast 11))

noncomputable def Ns528p81 := @Enclosure.Real.IsNear.inv_image qz346 222574921 67108864 1 67108864 10117041 10117042 33554432 (@Enclosure.Real.IsNear.of_eq qz346 (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 222574921 67108864 1 67108864 (BSN.sqrt_enclosure 11 1 111287460 111287461 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

theorem RS529to540.d48 : Enclosure.Real.IsNear qz347 Bool.false 20234083 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 20234083 67108864 1 67108864 (Ns528p81 rfl rfl) rfl 

theorem RS529to540.d49 : Enclosure.Real.IsNear qz347 Bool.false 161872664 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 161872664 536870912 8 536870912 RS529to540.d48 rfl 

noncomputable def Ns528p82 := nat_lit 3004067793907357885399040 

noncomputable def Ns528p83 := BSN.log_dyadic_bound 4 20 6 5 106444800000000000 33554432 9000000 1454330814136320 990904320 13605151 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 20) 0 5 1454330814136320 106444800000000000 990904320 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz712 := (Enclosure.sfrac Bool.false 12 1)

noncomputable abbrev qz576 := qz712

noncomputable abbrev qz348 := qz576

noncomputable abbrev qz1 := qz348

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12) qz575)

theorem RS529to540.d50 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 11191024608564965 4503599627370496 1000000027 9000000000000000 := BSN.isNear_log_sfrac 12 1 11191024608564965 4503599627370496 1000000027 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false Ns528p82 Ns528p64 1000000027000000 9000000000000000000000 11191024608564965 4503599627370496 1000000027 9000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 13605151 33554432 24973259072661432 36028797018963968 9000000 1000000000000000 rfl rfl rfl rfl (Ns528p83 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS529to540.d51 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 1334074092 536870912 61 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 11191024608564965 4503599627370496 1000000027 9000000000000000 1334074092 536870912 61 536870912 RS529to540.d50 rfl 

noncomputable abbrev qz350 := (Real.sqrt (@Nat.cast Real Real.instNatCast 12))

noncomputable def Ns528p84 := @Enclosure.Real.IsNear.inv_image qz350 232471925 67108864 1 67108864 9686330 9686331 33554432 (@Enclosure.Real.IsNear.of_eq qz350 (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 232471925 67108864 1 67108864 (BSN.sqrt_enclosure 12 1 116235962 116235963 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz351 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

theorem RS529to540.d52 : Enclosure.Real.IsNear qz351 Bool.false 19372661 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 19372661 67108864 1 67108864 (Ns528p84 rfl rfl) rfl 

theorem RS529to540.d53 : Enclosure.Real.IsNear qz351 Bool.false 154981288 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 154981288 536870912 8 536870912 RS529to540.d52 rfl 

theorem RS529to540.d54 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz713 := (@instHMul Real Real.instMul)

noncomputable abbrev qz577 := qz713

noncomputable abbrev qz352 := (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz2 := qz352

theorem RS529to540.d55 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS529to540.d54 rfl 

noncomputable abbrev qz353 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 2 1) Real.pi))

noncomputable abbrev qz3 := qz353

theorem RS529to540.d56 : Enclosure.Real.IsNear qz3 Bool.false 10680707 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 10680707 67108864 1 67108864 10680707 67108864 1 67108864 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 5340353 5340354 33554432 RS529to540.d55 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns528p85 := nat_lit 11112501361557416580342049 

noncomputable def Ns528p86 := nat_lit 10625324586456701730816000000 

noncomputable def Ns528p87 := nat_lit 69606909186727574551354627063808 

noncomputable abbrev qz714 := (Enclosure.sfrac Bool.false 913584 1000)

noncomputable abbrev qz578 := qz714

noncomputable abbrev qz354 := qz578

noncomputable abbrev qz4 := qz354

noncomputable abbrev qz355 := qz577

noncomputable abbrev qz5 := qz355

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12)

noncomputable abbrev qz356 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz715 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 913584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz579 := qz715

noncomputable abbrev qz357 := qz579

noncomputable abbrev qz358 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz7 := (@HPow.hPow Real Real Real qz356 qz357 qz358)

noncomputable abbrev qz716 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 913584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz580 := qz716

noncomputable abbrev qz359 := qz580

noncomputable abbrev qz8 := qz359

noncomputable def Ns528p88 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8)) 859958423 268435456 17509 16777216 17249166413178252990255 75557863725914323419136 23724285296945796342049 Ns528p86 Ns528p87 

noncomputable def Ns528p89 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos BSN.quadSignPos 11 12 913584 1000 288 536870912 268435456 9007199254740992 Bool.false 975714721773 4460 1334074092 61 154981288 8 

noncomputable def Ns528p90 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 913584 1000 182 237 536870912 268435456 9007199254740992 Bool.false 975714721773 4460 

noncomputable def Ns528p91 := Ns528p90 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.true 707374520 225559 Bool.true 166252684 Bool.true 531356457 28296951008113761 1 Bool.false 511334250 Bool.true Bool.false 448758043 Bool.true Bool.true 1004378250 

noncomputable def Ns528p92 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 913584 1000 52 120 536870912 268435456 9007199254740992 Bool.false 975714721773 4460 

noncomputable def Ns528p93 := Ns528p92 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.true 880904383 184197 Bool.true 350478614 Bool.true 774887520 28296951008113761 1 Bool.false 426477182 Bool.false Bool.false 68242220 Bool.false Bool.true 707374520 

noncomputable def Ns528p94 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 913584 1000 114 25 536870912 268435456 9007199254740992 Bool.false 975714721773 4460 

noncomputable def Ns528p95 := Ns528p94 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.true 770494649 136856 Bool.false 760607476 Bool.false 208324142 28296951008113761 1 Bool.false 82380622 Bool.true Bool.false 203135452 Bool.true Bool.true 880904383 

noncomputable def Ns528p96 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 913584 1000 350 220 536870912 268435456 9007199254740992 Bool.false 975714721773 4460 

noncomputable def Ns528p97 := Ns528p96 744261104 60 268435448 8 864060384 60 240095976 8 Bool.true 679393227 80690 Bool.false 609485549 Bool.false 793711479 28296951008113761 1 Bool.false 226506363 Bool.true Bool.false 49532833 Bool.false Bool.true 770494649 

noncomputable def Ns528p98 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 913584 1000 753 518 536870912 268435456 9007199254740992 Bool.false 975714721773 4460 

noncomputable def Ns528p99 := Ns528p98 372130544 60 379625064 8 589812976 60 309962568 8 Bool.false 567240 4532 Bool.false 726123894 Bool.false 33928223 28296951008113761 1 Bool.false 524131093 Bool.true Bool.false 535799200 Bool.true Bool.true 679393227 

noncomputable def Ns528p100 := nat_lit 290458519146923852983474170521573031728470324596511257 

noncomputable def Ns528p101 := nat_lit 159820003319313787008537704899601802073949077504000 

noncomputable def Ns528p102 := nat_lit 305480851023403423422597599723520000 

noncomputable def Ns528p103 := nat_lit 1674494740871973432457120325528569774080 

noncomputable abbrev qz360 := (@Eq.refl Real qz578)

noncomputable abbrev qz9 := qz360

noncomputable def Ns528p104 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 913584 1000 3338543900224 16000000 1827168 4000 2000 Ns528p102 Ns528p103 qz9 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p105 := nat_lit 3426388111946304293242493383074325837324265614696253112975360 

noncomputable abbrev qz717 := (@instHSub Real Real.instSub)

noncomputable abbrev qz581 := qz717

noncomputable abbrev qz361 := qz581

noncomputable abbrev qz582 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz718 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz719 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz583 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1827168))))

noncomputable abbrev qz362 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 913584 4000) (Real.log (Enclosure.sfrac Bool.false 3338543900224 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz583))

noncomputable abbrev qz584 := (Enclosure.sfrac Bool.false 913584 2000)

noncomputable abbrev qz10 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz362 qz584) (@HMul.hMul Real Real Real qz355 qz584 (Real.log Real.pi)))

noncomputable def Ns528p106 := @Enclosure.Real.IsNear.addLit_ft_p qz10 (Enclosure.sfrac Bool.true Ns528p102 Ns528p103) 2046222285596976275217 1125899906842624000 76538850005113237 9216000000000000000000 Ns528p102 Ns528p103 0 1 Ns528p105 

noncomputable def Ns528p107 := nat_lit 8582478317368539979047763968000 

noncomputable abbrev qz11 := (@HSub.hSub Real Real Real qz361 qz362 qz584)

noncomputable def Ns528p108 := @Enclosure.Real.IsNear.subLit_ff_p qz11 (@HMul.hMul Real Real Real qz5 qz584 (Real.log Real.pi)) 2634959234028761046801 1125899906842624000 28799534945713 9000000000000000000 2193216042339 4194304000 171297 33554432000 Ns528p107 2046222285596976275217 1125899906842624000 

noncomputable def Ns528p109 := nat_lit 5269918468057522093602000 

noncomputable abbrev qz12 := qz362

noncomputable def Ns528p110 := @Enclosure.Real.IsNear.subLit_ff_p qz12 qz584 3149261304275216949009 1125899906842624000 28799534945713 9000000000000000000 913584 2000 0 1 Ns528p109 2634959234028761046801 1125899906842624000 28799534945713 9000000000000000000 

noncomputable def Ns528p111 := nat_lit 7091506018213094636544880599191519232 

noncomputable def Ns528p112 := nat_lit 118459803350534610871123968 

noncomputable def Ns528p113 := nat_lit 9671406556917033397649408 

noncomputable def Ns528p114 := nat_lit 89914487212917812509736270325469901706433542938399872395337269655866556214064625636865920721637135145735496894246482061271022720152376146465492277219043573760 

noncomputable def Ns528p115 := nat_lit 1614023314204966481883472158493708770303649859355968110239521528594170445910860228622919686412805282447038324094872869825011057459025820055093084151896604672 

noncomputable def Ns528p116 := nat_lit 139229538115350476424089358743957627142126869525138690640197767202878680524919733581214285494944944019112008329271034620944568090947771671275655659520 

noncomputable def Ns528p117 := BSN.log_dyadic_bound 1241391900224 5435695900224 7 6 Ns528p114 268435456 72000000 Ns528p115 Ns528p116 124810278 6677087800448 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1241391900224) (BSN.artanhQ 5435695900224) 0 6 Ns528p115 Ns528p114 Ns528p116 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz363 := (Real.log (Enclosure.sfrac Bool.false 3338543900224 16000000))

noncomputable abbrev qz364 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns528p118 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 913584 4000) qz363 913584 4000 0 1 55162144522431591 4503599627370496 125000153 9000000000000000 3149703290086321414509 1125899906842624000 2379127912049 750000000000000000 (Enclosure.Real.IsNear.const Bool.false 913584 4000) (BSN.isNear_log_sfrac 3338543900224 16000000 55162144522431591 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3338543900224) qz364)) Bool.false Ns528p112 Ns528p113 1000001224000000 72000000000000000000000 55162144522431591 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3338543900224 16000000 17 6677087800448 4194304000000 124810278 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p117 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p119 := BSN.arctan_dyadic_bound_f 1000 1827168 1 0 33554432 9000000 0 1 1 0 1 1 18364 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1827168) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1827168) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz585 := qz718

noncomputable abbrev qz365 := qz585

noncomputable abbrev qz13 := qz365

noncomputable abbrev qz586 := qz719

noncomputable abbrev qz366 := qz586

noncomputable abbrev qz14 := qz366

noncomputable abbrev qz720 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz587 := qz720

noncomputable abbrev qz367 := qz587

noncomputable abbrev qz15 := (@Enclosure.Real.IsNear.mulLit_ff qz367 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 1827168)

noncomputable def Ns528p120 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz368)) 884279719003555 562949953421312 1 2000000000000000 18364 33554432 1 9000000 29661165687339265032192 883971622208931 562949953421312 2000000009 18000000000000000 qz15 (Ns528p119 rfl) rfl rfl 

noncomputable abbrev qz369 := (@HMul.hMul Real Real Real qz577 qz582 qz583)

noncomputable abbrev qz16 := qz369

noncomputable abbrev qz370 := qz582

noncomputable abbrev qz17 := qz370

noncomputable abbrev qz371 := qz583

noncomputable abbrev qz18 := qz371

noncomputable abbrev qz372 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns528p121 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 913584 4000) qz363) qz16 3149703290086321414509 1125899906842624000 2379127912049 750000000000000000 883971622208931 2251799813685248 2000000009 72000000000000000 Ns528p111 3149261304275216949009 1125899906842624000 28799534945713 9000000000000000000 (Ns528p118 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz18 1 4 0 1 883971622208931 562949953421312 2000000009 18000000000000000 883971622208931 2251799813685248 2000000009 72000000000000000 qz372 Ns528p120 rfl) 

noncomputable def Ns528p122 := @Ns528p106 Ns528p100 Ns528p101 76538850005113237 9216000000000000000000 (@Ns528p108 76538850005113237 9216000000000000000000 (Ns528p110 (Ns528p121 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 913584 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz584 (Real.log Real.pi) 913584 2000 0 1 38410761 33554432 3 268435456 2193216042339 4194304000 171297 33554432000 (Enclosure.Real.IsNear.const Bool.false 913584 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p102 Ns528p103) 

noncomputable abbrev qz373 := (@instHAdd Real Real.instAdd)

noncomputable def Ns528p123 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns528p100 Ns528p101 76538850005113237 9216000000000000000000 121964340221 67108864 559 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz373 qz10 (Enclosure.sfrac Bool.true Ns528p102 Ns528p103)) Bool.false Ns528p100 Ns528p101 76538850005113237 9216000000000000000000 Ns528p104 (Ns528p122 rfl rfl)) 

noncomputable def Ns528p124 := nat_lit 15181591402659015391444992 

noncomputable def Ns528p125 := nat_lit 5524869052725798132221380393475860431791602912195008617019459987476698728122360902412430421403801030980831386732319152464499718782007803641856 

noncomputable def Ns528p126 := nat_lit 21759806992472160846509436431027924547665573599712653161483140986990306751823661669370177199848368120331884066839754328502985489716814125465600 

noncomputable def Ns528p127 := nat_lit 10168338076972414478622406858218520506353281037340186933308553802120772435989999084446186731784608675687226500221792780758459173805490176 

noncomputable def Ns528p128 := nat_lit 33437020984329174162525422566776522940367930584247316698119961391745756451409121546290976953773229977696238219777938245824574014150004734689280 

noncomputable def Ns528p129 := nat_lit 1980142436314966637032358715223541133837567197573851437694965829816117914415953211912686125186201498950201450082417643893771679564230085417369600 

noncomputable abbrev qz588 := (BSN.cosEvenQ 137438953472)

noncomputable abbrev qz589 := (BSN.cosOddQ 137438953472)

noncomputable def Ns528p130 := BSN.cos_dyadic_bound_f 215743389768 137438953472 4 3 67108864 18017579 Ns528p125 Ns528p126 Ns528p127 Ns528p128 Ns528p129 Ns528p127 70905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 215743389768) qz588 0 3 Ns528p125 Ns528p126 Ns528p127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 215743389768) qz589 0 3 Ns528p128 Ns528p129 Ns528p127 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 67108864)

noncomputable abbrev qz374 := (@Nat.cast Real Real.instNatCast Ns528p113)

noncomputable def Ns528p131 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 121964340221) qz19) Bool.false 121964340221 67108864 559 67108864 Bool.false 70905 67108864 1 9000000 (Ns528p123 rfl) (Enclosure.sfrac_false_div 121964340221 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 121964340221) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns528p124) qz374) 226375608064910080 72057594037927936 Bool.false 70905 67108864 289 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q0 121964340221 67108864 226375608064910080 72057594037927936 289 Ns528p124 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 70905 67108864 Ns528p124 Ns528p113 215743389768 137438953472 18017579 18000000 (Ns528p130 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p132 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns528p100 Ns528p101 76538850005113237 9216000000000000000000 975714721773 536870912 4460 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz373 qz10 (Enclosure.sfrac Bool.true Ns528p102 Ns528p103)) Bool.false Ns528p100 Ns528p101 76538850005113237 9216000000000000000000 Ns528p104 (Ns528p122 rfl rfl)) 

noncomputable def Ns528p133 := Ns528p99 80690 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 753 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 524131093 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 518 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535799200 536870912) qz9 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.false 70905 67108864 79657951 9437184000000 567240 536870912 4532 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.false 70905 67108864 79657951 9437184000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.false 70905 67108864 5098108864 603979776000000 70905 67108864 79657951 9437184000000 (Ns528p131 rfl rfl) rfl)) rfl) (Ns528p132 rfl) RS529to540.d7 

noncomputable def Ns528p134 := nat_lit 99673884627722735495269072772458576249434427209176034904121949345193350471588702008424021850164802118865109979136 

noncomputable def Ns528p135 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800 

noncomputable def Ns528p136 := nat_lit 21484672396279588074264031400859262825438332101212963210032945257595079634513453778898504420807237577281536 

noncomputable def Ns528p137 := nat_lit 498028796647417709322179246566201980309105892867887009082389177911330830516002102122850013569134546078416078442496 

noncomputable def Ns528p138 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000 

noncomputable abbrev qz375 := (BSN.sinEvenQ 536870912)

noncomputable abbrev qz376 := (BSN.sinOddQ 536870912)

noncomputable def Ns528p139 := BSN.sin_dyadic_bound_f 726123894 536870912 4 3 536870912 268435456 Ns528p134 Ns528p135 Ns528p136 Ns528p137 Ns528p138 Ns528p136 524131093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 726123894) qz375 0 3 Ns528p134 Ns528p135 Ns528p136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 726123894) qz376 0 3 Ns528p137 Ns528p138 Ns528p136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p140 := nat_lit 1325087190743104531440605677441 

noncomputable def Ns528p141 := nat_lit 1993841993677373809355710590420516864 

noncomputable def Ns528p142 := nat_lit 29907629905160607140335658856307752960 

noncomputable abbrev qz20 := (BSN.cosEvenQ 536870912)

noncomputable abbrev qz377 := (BSN.cosOddQ 536870912)

noncomputable def Ns528p143 := BSN.cos_dyadic_bound_f 33928223 536870912 2 1 536870912 268435456 Ns528p140 Ns528p141 Ns528p140 Ns528p140 Ns528p142 Ns528p140 535799200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 33928223) qz20 0 1 Ns528p140 Ns528p141 Ns528p140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 33928223) qz377 0 1 Ns528p140 Ns528p142 Ns528p140 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p144 := nat_lit 19026881048857956433111048122259582739822733355597190731773654403961543943915802764034186608903314490588944850481 

noncomputable def Ns528p145 := nat_lit 274647376664257459544000446540783031995164976078897331880025758552119769180746491160307949742358795015190845849600 

noncomputable def Ns528p146 := nat_lit 2627610294081785872131936452476801772172147790940631050660938572666618736701156516033157886204639908388401 

noncomputable def Ns528p147 := nat_lit 115353723224741911884647879814384541350990983024251133136815841533279254586572408914712004999354721660375469579825 

noncomputable def Ns528p148 := nat_lit 24992911276447428818504040635211255911560012823179657201082344028242898995447930695588023426554650346382366972313600 

noncomputable def Ns528p149 := BSN.cos_dyadic_bound_f 609485549 536870912 4 3 536870912 268435456 Ns528p144 Ns528p145 Ns528p146 Ns528p147 Ns528p148 Ns528p146 226506363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 609485549) qz20 0 3 Ns528p144 Ns528p145 Ns528p146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 609485549) qz377 0 3 Ns528p147 Ns528p148 Ns528p146 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p150 := nat_lit 54823788734730526897748703090229310062468133410802309763745163307547657422105100096359544316673749073325232119521 

noncomputable def Ns528p151 := nat_lit 62510350737063200274140472029587246122826564969167246054068969575452193709630494688726646143812342020988641 

noncomputable def Ns528p152 := nat_lit 331968616637015833353678571361672792422022431012728985982198235202066820547522398187876024027291472285196583329505 

noncomputable def Ns528p153 := BSN.cos_dyadic_bound_f 793711479 536870912 4 3 536870912 268435456 Ns528p150 Ns528p145 Ns528p151 Ns528p152 Ns528p148 Ns528p151 49532833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 793711479) qz20 0 3 Ns528p150 Ns528p145 Ns528p151 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 793711479) qz377 0 3 Ns528p152 Ns528p148 Ns528p151 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p154 := Ns528p97 136856 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 350 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 226506363 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 220 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 49532833 536870912) qz9 rfl rfl (Ns528p133 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p139 rfl rfl) (Ns528p143 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p132 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p149 rfl rfl) (Ns528p153 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p155 := nat_lit 46213368964002026903027133883613493475459710254172790665033854106011973856624909100471841439529560762146573254656 

noncomputable def Ns528p156 := nat_lit 37491004550006543555413375914198483669440358071615270016379959409162282629405342409993364995940608771096576 

noncomputable def Ns528p157 := nat_lit 279913779204360528360157806244970451801779308038513005755668544393840435491260651252213001924633695373694389452800 

noncomputable def Ns528p158 := BSN.cos_dyadic_bound_f 760607476 536870912 4 3 536870912 268435456 Ns528p155 Ns528p145 Ns528p156 Ns528p157 Ns528p148 Ns528p156 82380622 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 760607476) qz20 0 3 Ns528p155 Ns528p145 Ns528p156 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 760607476) qz377 0 3 Ns528p157 Ns528p148 Ns528p156 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p159 := nat_lit 1883468699661548418721071227834896 

noncomputable def Ns528p160 := nat_lit 9969209968386869046778552952102584320 

noncomputable def Ns528p161 := nat_lit 69784469778708083327449870664718090240 

noncomputable def Ns528p162 := BSN.sin_dyadic_bound_f 208324142 536870912 2 1 536870912 268435456 Ns528p159 Ns528p160 Ns528p159 Ns528p159 Ns528p161 Ns528p159 203135452 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 208324142) qz375 0 1 Ns528p159 Ns528p160 Ns528p159 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 208324142) qz376 0 1 Ns528p159 Ns528p161 Ns528p159 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p163 := Ns528p95 184197 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 82380622 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 203135452 536870912) qz9 rfl rfl (Ns528p154 rfl rfl) (Ns528p132 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p158 rfl rfl) (Ns528p162 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p164 := nat_lit 2106113722093997776039510217734955037404288149726794377788411266940231936 

noncomputable def Ns528p165 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720 

noncomputable def Ns528p166 := nat_lit 227662857055321769578086909424435898165290224055859944527895747584256 

noncomputable def Ns528p167 := nat_lit 6317885840567882684579374479386016240416533868732271413476178009325527296 

noncomputable def Ns528p168 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400 

noncomputable def Ns528p169 := BSN.cos_dyadic_bound_f 350478614 536870912 3 2 536870912 268435456 Ns528p164 Ns528p165 Ns528p166 Ns528p167 Ns528p168 Ns528p166 426477182 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 350478614) qz20 0 2 Ns528p164 Ns528p165 Ns528p166 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 350478614) qz377 0 2 Ns528p167 Ns528p168 Ns528p166 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p170 := nat_lit 49792076015049951986235827843506160657934044906253079589657898071351957115840628770819577118793938264653824000000 

noncomputable def Ns528p171 := nat_lit 46866659192543160252581530127560933197838392184166894567957225249624208825623571305857963524096000000000000 

noncomputable def Ns528p172 := nat_lit 301552813698268969407132110598130000507931552392389457099941203624247596447677459876901210294542438808263065600000 

noncomputable def Ns528p173 := BSN.cos_dyadic_bound_f 774887520 536870912 4 3 536870912 268435456 Ns528p170 Ns528p145 Ns528p171 Ns528p172 Ns528p148 Ns528p171 68242220 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 774887520) qz20 0 3 Ns528p170 Ns528p145 Ns528p171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 774887520) qz377 0 3 Ns528p172 Ns528p148 Ns528p171 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p174 := Ns528p93 225559 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 426477182 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 68242220 536870912) qz9 rfl rfl (Ns528p163 rfl) (Ns528p132 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p169 rfl rfl) (Ns528p173 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p175 := nat_lit 106626662895940760169246073409543029242365215732745233543354597968510976 

noncomputable def Ns528p176 := nat_lit 583645743527870640083049946156682409396040588855313353520091037696 

noncomputable def Ns528p177 := nat_lit 319878821396335224766458054128736774362276855117057990003356753723457536 

noncomputable def Ns528p178 := BSN.cos_dyadic_bound_f 166252684 536870912 3 2 536870912 268435456 Ns528p175 Ns528p165 Ns528p176 Ns528p177 Ns528p168 Ns528p176 511334250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 166252684) qz20 0 2 Ns528p175 Ns528p165 Ns528p176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 166252684) qz377 0 2 Ns528p177 Ns528p168 Ns528p176 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p179 := nat_lit 20032858222497588985528490271190197554658135164828249963631369904967833665 

noncomputable def Ns528p180 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480 

noncomputable def Ns528p181 := nat_lit 6354592409513597766503829314514039112208258899134883674505920354113601 

noncomputable def Ns528p182 := nat_lit 52456721242640187232381230224703208960780112060142055331180578261009094721 

noncomputable def Ns528p183 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800 

noncomputable def Ns528p184 := BSN.sin_dyadic_bound_f 531356457 536870912 3 2 536870912 268435456 Ns528p179 Ns528p180 Ns528p181 Ns528p182 Ns528p183 Ns528p181 448758043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 531356457) qz375 0 2 Ns528p179 Ns528p180 Ns528p181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 531356457) qz376 0 2 Ns528p182 Ns528p183 Ns528p181 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz590 := (BSN.cos_quad_nat1 237 rfl)

noncomputable def Ns528p185 := Ns528p91 262759 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 511334250 536870912) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 448758043 536870912) qz9 rfl rfl (Ns528p174 rfl) (Ns528p132 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p178 rfl rfl) (Ns528p184 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p186 := nat_lit 220400935650898744087506639475363372406647530171578633215583692372068961 

noncomputable def Ns528p187 := nat_lit 2493672883445823322897054823970565596403377166937872824669755165281 

noncomputable def Ns528p188 := nat_lit 661197819606929340615874124316442176088749783760402023901101737605876321 

noncomputable def Ns528p189 := BSN.cos_dyadic_bound_f 199344811 536870912 3 2 536870912 268435456 Ns528p186 Ns528p165 Ns528p187 Ns528p188 Ns528p168 Ns528p187 500284942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 199344811) qz20 0 2 Ns528p186 Ns528p165 Ns528p187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 199344811) qz377 0 2 Ns528p188 Ns528p168 Ns528p187 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz378 := (BSN.cos_quad_nat0 288 rfl)

noncomputable def Ns528p190 := Ns528p89 Bool.true 1004378250 262759 Bool.true 199344811 28296951008113761 1 Bool.false 500284942 Bool.false Bool.true 859958423 280144 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 500284942 536870912) qz9 rfl (Ns528p185 rfl) (Ns528p132 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p189 rfl rfl) rfl 

noncomputable def Ns528p191 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) 859958423 536870912 280144 536870912 859958423 536870912 280144 536870912 923373325676183552 859958423 268435456 17509 16777216 (Ns528p190 rfl rfl rfl rfl) 

noncomputable def Ns528p192 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8) 19325811 67108864 1 67108864 892545539909205 1125899906842624 1221101140816027 158329674399744000000 17249166413178252990255 75557863725914323419136 

noncomputable def Ns528p193 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz7 1 1 0 1 19325811 67108864 1 67108864 19325811 67108864 1 67108864 

noncomputable abbrev qz21 := qz357

noncomputable abbrev qz22 := (@Enclosure.Real.IsNear.of_eq qz357 (@HMul.hMul Real Real Real qz355 qz354 qz353) Bool.false 609857688993 4194304000 57099 4194304000 (BSN.t_div_two_pi_mk qz354 913584 1000 qz360) (@Enclosure.Real.IsNear.mulLit_ff qz354 qz353 913584 1000 0 1 10680707 67108864 1 67108864 609857688993 4194304000 57099 4194304000 (Enclosure.Real.IsNear.const Bool.false 913584 1000) RS529to540.d56 rfl))

noncomputable def Ns528p194 := @Enclosure.Real.IsNear.sqrt_image qz21 609857688993 4194304000 57099 4194304000 404607725 404607764 33554432 qz22 

noncomputable abbrev qz721 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 913584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz591 := qz721

noncomputable abbrev qz379 := qz591

noncomputable abbrev qz23 := qz379

noncomputable def Ns528p195 := @Enclosure.Real.IsNear.sqrt_image qz23 809215489 67108864 39 67108864 116517734 116517740 33554432 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 809215489 67108864 39 67108864 809215489 67108864 39 67108864 (Ns528p194 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz592 := (Real.sqrt qz721)

noncomputable abbrev qz380 := qz592

noncomputable abbrev qz24 := qz380

noncomputable def Ns528p196 := @Enclosure.Real.IsNear.inv_image qz24 116517737 33554432 3 33554432 9662905 9662906 33554432 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 233035474 67108864 6 67108864 116517737 33554432 3 33554432 (Ns528p195 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p197 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz24) Bool.false 19325811 67108864 1 67108864 19325811 67108864 1 67108864 (Ns528p196 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz359))

noncomputable abbrev qz593 := (@HMul.hMul Real Real Real qz713 qz716 qz716)

noncomputable abbrev qz594 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz381 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz593 qz580) qz594)

noncomputable abbrev qz26 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz381))

noncomputable def Ns528p198 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz8) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz25) qz26) Bool.false 892545539909205 

noncomputable def Ns528p199 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz25) qz26 35934483 33554432 73 

noncomputable def Ns528p200 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz25) Bool.false 71868966 67108864 292 67108864 35934483 33554432 73 

noncomputable def Ns528p201 := @Enclosure.Real.IsNear.recentre' qz25 Bool.false 31332019 33554432 1140554432 301989888000000 31332019 33554432 17821163 4718592000000 

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz355 qz352 qz359)

noncomputable def Ns528p202 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 24561731) qz19) Bool.false 24561731 67108864 123 33554432 Bool.false 31332019 33554432 1 

noncomputable def Ns528p203 := nat_lit 210491388197259373290760669 

noncomputable def Ns528p204 := nat_lit 57646075230342348800000000000000 

noncomputable def Ns528p205 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz8 884279719003555 140737488355328 1 500000000000000 3909121 67108864 39 67108864 3456756419430895925155 9444732965739290427392 Ns528p203 

noncomputable def Ns528p206 := @Enclosure.Real.IsNear.subLit_ff_p qz23 qz1 809215489 67108864 39 67108864 12 1 0 1 3909121 3909121 67108864 39 

noncomputable abbrev qz382 := (Enclosure.Real.IsNear.const Bool.false 12 1)

noncomputable def Ns528p207 := @Ns528p206 67108864 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 809215489 67108864 39 67108864 809215489 67108864 39 67108864 (Ns528p194 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p208 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 3456756419430895925155 9444732965739290427392 Ns528p203 Ns528p204 24561731 67108864 123 33554432 (@Ns528p205 Ns528p204 RS529to540.d55 (Ns528p207 rfl rfl) rfl) 

noncomputable def Ns528p209 := nat_lit 363945105072450205411311082321 

noncomputable def Ns528p210 := nat_lit 486777830487640090174734030864384 

noncomputable def Ns528p211 := nat_lit 7301667457314601352621010462965760 

noncomputable abbrev qz383 := (BSN.cosEvenQ 67108864)

noncomputable def Ns528p212 := BSN.cos_dyadic_bound_f 24561731 67108864 2 1 33554432 9000000 Ns528p209 Ns528p210 Ns528p209 Ns528p209 Ns528p211 Ns528p209 31332019 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 24561731) qz383 0 1 Ns528p209 Ns528p210 Ns528p209 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 24561731) (BSN.cosOddQ 67108864) 0 1 Ns528p209 Ns528p211 Ns528p209 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p213 := @Enclosure.Real.IsNear.inv_image qz25 31332019 33554432 17821163 4718592000000 35934337 35934629 33554432 (Ns528p201 (@Ns528p202 9000000 (Ns528p208 rfl) (Enclosure.sfrac_false_div 24561731 67108864) (Ns528p212 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p214 := @Enclosure.Real.IsNear.recentre' qz26 Bool.false 24838135 33554432 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz355 qz352 qz381)

noncomputable def Ns528p215 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 49484589)) qz19) Bool.true 49484589 67108864 

noncomputable def Ns528p216 := nat_lit 467368730633863904257413617245 

noncomputable def Ns528p217 := nat_lit 633825300114114700748351602688 

noncomputable def Ns528p218 := nat_lit 78857593825560764434417489829368313 

noncomputable def Ns528p219 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns528p216 Ns528p217 Ns528p218 

noncomputable def Ns528p220 := nat_lit 19342813113834066795298816000000000000000 

noncomputable abbrev qz29 := qz381

noncomputable def Ns528p221 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 528530419266559 

noncomputable abbrev qz384 := (@HSub.hSub Real Real Real qz581 qz593 qz580)

noncomputable abbrev qz30 := qz384

noncomputable abbrev qz385 := qz594

noncomputable abbrev qz31 := qz385

noncomputable def Ns528p222 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 247055442555903 4503599627370496 2922158655 4503599627370496 1 16 

noncomputable abbrev qz386 := qz593

noncomputable abbrev qz32 := qz386

noncomputable def Ns528p223 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz8 15281226992641 4503599627370496 304912959 4503599627370496 3909121 67108864 39 67108864 

noncomputable def Ns528p224 := @Enclosure.Real.IsNear.mulLit_ff qz8 qz8 3909121 67108864 39 67108864 3909121 67108864 39 67108864 15281226992641 4503599627370496 

noncomputable def Ns528p225 := nat_lit 204354929894174435549782758058495190152739749037856525791141584161 

noncomputable def Ns528p226 := nat_lit 16586685937797756904922089360178093090225977525586485022553978961920 

noncomputable def Ns528p227 := nat_lit 35955037021200439731008411260745013722050673122679921891106081 

noncomputable def Ns528p228 := nat_lit 612992879608480905769886257352964080430775145767324217529642540321 

noncomputable def Ns528p229 := nat_lit 746400867200899060721494021208014189060168988651391826014929053286400 

noncomputable def Ns528p230 := BSN.cos_dyadic_bound_f 49484589 67108864 3 2 33554432 9000000 Ns528p225 Ns528p226 Ns528p227 Ns528p228 Ns528p229 Ns528p227 24838135 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 49484589) qz383 0 2 Ns528p225 Ns528p226 Ns528p227 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 49484589) (BSN.cosOddQ 67108864) 0 2 Ns528p228 Ns528p229 Ns528p227 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz387 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns528p231 := @Ns528p214 1266554432 301989888000000 24838135 33554432 19789913 4718592000000 (@Ns528p215 137 33554432 Bool.false 24838135 33554432 1 9000000 (@Ns528p219 Ns528p220 49484589 67108864 137 33554432 (@Ns528p221 4503599627370496 2922158655 4503599627370496 Ns528p216 Ns528p217 Ns528p218 Ns528p220 RS529to540.d55 (@Ns528p222 0 1 8456486708264944 528530419266559 4503599627370496 2922158655 4503599627370496 (@Ns528p223 16579610094943906824192 247055442555903 4503599627370496 2922158655 4503599627370496 (@Ns528p224 304912959 4503599627370496 (Ns528p207 rfl rfl) (Ns528p207 rfl rfl) rfl) (Ns528p207 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 49484589 67108864) (BSN.cos_neg_of_bound 49484589 67108864 Bool.false 24838135 33554432 1 9000000 (Ns528p230 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns528p232 := @Ns528p192 23724285296945796342049 Ns528p86 (Ns528p193 qz33 (@Enclosure.Real.IsNear.of_eq qz7 (@Inv.inv Real Real.instInv qz24) Bool.false 19325811 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz21 (BSN.t_div_two_pi_nonneg qz4 913584 1000 qz9)) Ns528p197) rfl) (@Ns528p198 1125899906842624 1221101140816027 158329674399744000000 (BSN.correction_mk qz8 (BSN.cos_two_pi_p_ne_zero_mk qz4 913584 1000 12 qz9 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 913584 1000 12 qz9 rfl rfl rfl))) (@Ns528p199 16777216 24838135 33554432 19789913 4718592000000 892545539909205 1125899906842624 1221101140816027 158329674399744000000 (@Ns528p200 16777216 (Ns528p213 rfl rfl rfl rfl rfl) rfl) (Ns528p231 rfl) rfl)) 

noncomputable abbrev qz34 := qz361

noncomputable def Ns528p233 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 259305943499235714045743 75557863725914323419136 Ns528p85 Ns528p86 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz7) (Zeta.RiemannSiegel.correction qz8))) Bool.true 259305943499235714045743 75557863725914323419136 Ns528p85 Ns528p86 (BSN.hardyZApproximantRS₀_eq qz4 12 (@BSN.floor_sqrt_eq_dec qz4 913584 1000 12 qz9 rfl rfl rfl)) (@Ns528p88 259305943499235714045743 75557863725914323419136 Ns528p85 Ns528p86 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12)) Bool.true 859958423 268435456 17509 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (Ns528p191 (Ns528p190 rfl rfl rfl rfl) rfl rfl)) (Ns528p232 rfl) rfl rfl)) 

theorem RS529to540.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 259305943499235714045743 75557863725914323419136 Ns528p85 Ns528p86 := Ns528p233 

theorem RS529to540.d58 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS529to540.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS529to540.d3 a b h)) 

noncomputable def Ns528p234 := nat_lit 664082786653543858176000000 

noncomputable def Ns528p235 := nat_lit 3126342068100742554265883508736 

noncomputable abbrev qz722 := (Enclosure.sfrac Bool.false 915477 1000)

noncomputable abbrev qz595 := qz722

noncomputable abbrev qz388 := qz595

noncomputable abbrev qz35 := qz388

noncomputable abbrev qz723 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 915477 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz596 := qz723

noncomputable abbrev qz389 := qz596

noncomputable abbrev qz36 := (@HPow.hPow Real Real Real qz356 qz389 qz358)

noncomputable abbrev qz724 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 915477 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz597 := qz724

noncomputable abbrev qz390 := qz597

noncomputable abbrev qz37 := qz390

noncomputable def Ns528p236 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz36) (Zeta.RiemannSiegel.correction qz37)) 691664049 134217728 280723 268435456 1042701708546023021881 4722366482869645213696 1533072341600255877799 Ns528p234 Ns528p235 

noncomputable def Ns528p237 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos BSN.quadSignPos 11 12 915477 1000 288 536870912 268435456 9007199254740992 Bool.false 978245571516 4469 1334074092 61 154981288 8 

noncomputable def Ns528p238 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 915477 1000 181 237 536870912 268435456 9007199254740992 Bool.false 978245571516 4469 

noncomputable def Ns528p239 := Ns528p238 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.false 1525726430 226025 Bool.true 818827277 Bool.true 437479610 28296951008113761 1 Bool.false 536312549 Bool.true Bool.false 390646565 Bool.true Bool.false 1238345137 

noncomputable def Ns528p240 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 915477 1000 51 120 536870912 268435456 9007199254740992 Bool.false 978245571516 4469 

noncomputable def Ns528p241 := Ns528p240 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.false 1224561276 184577 Bool.true 776273170 Bool.true 477069697 28296951008113761 1 Bool.false 532690437 Bool.false Bool.false 338491923 Bool.false Bool.false 1525726430 

noncomputable def Ns528p242 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 915477 1000 115 25 536870912 268435456 9007199254740992 Bool.false 978245571516 4469 

noncomputable def Ns528p243 := Ns528p242 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.false 1223476261 137138 Bool.false 627183254 Bool.false 761551975 28296951008113761 1 Bool.false 493950557 Bool.false Bool.false 530656887 Bool.true Bool.false 1224561276 

noncomputable def Ns528p244 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 915477 1000 352 222 536870912 268435456 9007199254740992 Bool.false 978245571516 4469 

noncomputable def Ns528p245 := Ns528p244 744261104 60 268435448 8 864060384 60 240095976 8 Bool.false 1196069516 80855 Bool.false 44819309 Bool.false 2265202 28296951008113761 1 Bool.false 535001184 Bool.false Bool.false 536866133 Bool.true Bool.false 1223476261 

noncomputable def Ns528p246 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 915477 1000 756 519 536870912 268435456 9007199254740992 Bool.false 978245571516 4469 

noncomputable def Ns528p247 := Ns528p246 372130544 60 379625064 8 589812976 60 309962568 8 Bool.false 536870800 4540 Bool.false 22585947 Bool.false 604947146 28296951008113761 1 Bool.false 536395891 Bool.false Bool.false 484817546 Bool.false Bool.false 1196069516 

noncomputable def Ns528p248 := nat_lit 3864673356357664991111402490841409137368182375940286361599 

noncomputable def Ns528p249 := nat_lit 2120971226267773780382882765903092098042257174901555200 

noncomputable def Ns528p250 := nat_lit 308658864680845459864084387755360000 

noncomputable def Ns528p251 := nat_lit 1695420784778353253536482094177258240320 

noncomputable abbrev qz598 := (@Eq.refl Real qz722)

noncomputable abbrev qz391 := qz598

noncomputable abbrev qz38 := qz391

noncomputable def Ns528p252 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 915477 1000 3352393550116 16000000 1830954 4000 2000 Ns528p250 Ns528p251 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p253 := nat_lit 11130259266310075174400839173623258315620365242708024721405120 

noncomputable abbrev qz599 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1830954))))

noncomputable abbrev qz392 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 915477 4000) (Real.log (Enclosure.sfrac Bool.false 3352393550116 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz599))

noncomputable abbrev qz600 := (Enclosure.sfrac Bool.false 915477 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz392 qz600) (@HMul.hMul Real Real Real qz355 qz600 (Real.log Real.pi)))

noncomputable def Ns528p254 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns528p250 Ns528p251) 6564895557668842242391 3602879701896396800 1227150601203679051 147456000000000000000000 Ns528p250 Ns528p251 0 1 Ns528p253 

noncomputable def Ns528p255 := nat_lit 2202813415769012455410363269120000 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz361 qz392 qz600)

noncomputable def Ns528p256 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz600 (Real.log Real.pi)) 42263787326856006993587 18014398509481984000 115434765072481 36000000000000000000 35164168247997 67108864000 2746431 536870912000 Ns528p255 6564895557668842242391 3602879701896396800 

noncomputable def Ns528p257 := nat_lit 84527574653712013987174000 

noncomputable abbrev qz41 := qz392

noncomputable def Ns528p258 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz600 50509671078988526126771 18014398509481984000 115434765072481 36000000000000000000 915477 2000 0 1 Ns528p257 42263787326856006993587 18014398509481984000 115434765072481 36000000000000000000 

noncomputable def Ns528p259 := nat_lit 113737667924969522448943281645140574208 

noncomputable def Ns528p260 := nat_lit 118499841323999454092591104 

noncomputable def Ns528p261 := nat_lit 92702466597785905487688124566529590245820855526325975396617301429735392197331886918532818108202330324528026322579456826844352336392011997983663873262679490560 

noncomputable def Ns528p262 := nat_lit 1693725692854510685703661151435165761228255949921726475289088410456341490600588002571148902003361557711455048345711136201467562011783813997212270234678853632 

noncomputable def Ns528p263 := nat_lit 159056774787267079881848856655044200393283116189510865791552699547413732945821300430889836363695307909349079381456425917986735531999749852783307653120 

noncomputable def Ns528p264 := BSN.log_dyadic_bound 1255241550116 5449545550116 7 6 Ns528p261 268435456 72000000 Ns528p262 Ns528p263 125921555 6704787100232 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1255241550116) (BSN.artanhQ 5449545550116) 0 6 Ns528p262 Ns528p261 Ns528p263 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz393 := (Real.log (Enclosure.sfrac Bool.false 3352393550116 16000000))

noncomputable def Ns528p265 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 915477 4000) qz393 915477 4000 0 1 55180788656696423 4503599627370496 125000153 9000000000000000 50516742857066471238771 18014398509481984000 38144921689327 12000000000000000000 (Enclosure.Real.IsNear.const Bool.false 915477 4000) (BSN.isNear_log_sfrac 3352393550116 16000000 55180788656696423 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3352393550116) qz364)) Bool.false Ns528p260 Ns528p113 1000001224000000 72000000000000000000000 55180788656696423 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3352393550116 16000000 17 6704787100232 4194304000000 125921555 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p264 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p266 := BSN.arctan_dyadic_bound_f 1000 1830954 1 0 33554432 9000000 0 1 1 0 1 1 18326 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1830954) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1830954) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz394 := (@Nat.cast Real Real.instNatCast 1830954)

noncomputable def Ns528p267 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz394)) 884279719003555 562949953421312 1 2000000000000000 18326 33554432 1 9000000 29661187079437495042048 883972259743139 562949953421312 2000000009 18000000000000000 qz15 (Ns528p266 rfl) rfl rfl 

noncomputable abbrev qz395 := (@HMul.hMul Real Real Real qz577 qz582 qz599)

noncomputable abbrev qz42 := qz395

noncomputable abbrev qz396 := qz599

noncomputable abbrev qz43 := qz396

noncomputable def Ns528p268 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 915477 4000) qz393) qz42 50516742857066471238771 18014398509481984000 38144921689327 12000000000000000000 883972259743139 2251799813685248 2000000009 72000000000000000 Ns528p259 50509671078988526126771 18014398509481984000 115434765072481 36000000000000000000 (Ns528p265 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz43 1 4 0 1 883972259743139 562949953421312 2000000009 18000000000000000 883972259743139 2251799813685248 2000000009 72000000000000000 qz372 Ns528p267 rfl) 

noncomputable def Ns528p269 := @Ns528p254 Ns528p248 Ns528p249 1227150601203679051 147456000000000000000000 (@Ns528p256 1227150601203679051 147456000000000000000000 (Ns528p258 (Ns528p268 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 915477 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz600 (Real.log Real.pi) 915477 2000 0 1 38410761 33554432 3 268435456 35164168247997 67108864000 2746431 536870912000 (Enclosure.Real.IsNear.const Bool.false 915477 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p250 Ns528p251) 

noncomputable def Ns528p270 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns528p248 Ns528p249 1227150601203679051 147456000000000000000000 122280696439 67108864 35 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz373 qz39 (Enclosure.sfrac Bool.true Ns528p250 Ns528p251)) Bool.false Ns528p248 Ns528p249 1227150601203679051 147456000000000000000000 Ns528p252 (Ns528p269 rfl rfl)) 

noncomputable def Ns528p271 := BSN.cos_dyadic_bound_f 86511143 137438953472 1 0 67108864 18017579 0 1 1 0 1 1 67108850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 86511143) qz588 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 86511143) qz589 0 0 rfl) rfl rfl 

noncomputable def Ns528p272 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 122280696439) qz19) Bool.false 122280696439 67108864 35 4194304 Bool.false 67108850 67108864 1 9000000 (Ns528p270 rfl) (Enclosure.sfrac_false_div 122280696439 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 122280696439) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6087680514061246660608) qz374) 226375608064910080 72057594037927936 Bool.false 67108850 67108864 290 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q0 122280696439 67108864 226375608064910080 72057594037927936 290 6087680514061246660608 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108850 67108864 6087680514061246660608 Ns528p113 86511143 137438953472 18017579 18000000 (Ns528p271 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p273 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns528p248 Ns528p249 1227150601203679051 147456000000000000000000 978245571516 536870912 4469 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz373 qz39 (Enclosure.sfrac Bool.true Ns528p250 Ns528p251)) Bool.false Ns528p248 Ns528p249 1227150601203679051 147456000000000000000000 Ns528p252 (Ns528p269 rfl rfl)) 

noncomputable def Ns528p274 := Ns528p247 80855 BSN.abs_quadSignPos (BSN.cos_quad_nat0 756 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536395891 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 519 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 484817546 536870912) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 33554425 33554432 4987411 589824000000 536870800 536870912 4540 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 33554425 33554432 4987411 589824000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 67108850 67108864 319194304 37748736000000 33554425 33554432 4987411 589824000000 (Ns528p272 rfl rfl) rfl)) rfl) (Ns528p273 rfl) RS529to540.d7 

noncomputable def Ns528p275 := nat_lit 260227517550016885810048202481 

noncomputable def Ns528p276 := BSN.cos_dyadic_bound_f 22585947 536870912 2 1 536870912 268435456 Ns528p275 Ns528p141 Ns528p275 Ns528p275 Ns528p142 Ns528p275 536395891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22585947) qz20 0 1 Ns528p275 Ns528p141 Ns528p275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22585947) qz377 0 1 Ns528p275 Ns528p142 Ns528p275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p277 := nat_lit 33663748463836373222913678392019682873960422609235518631988675608053080320 

noncomputable def Ns528p278 := nat_lit 17936572501934704837715427213514172549015155090370840416682851924500736 

noncomputable def Ns528p279 := nat_lit 88137920097425464156941427954086813152436034677851472199295711498927923456 

noncomputable def Ns528p280 := BSN.sin_dyadic_bound_f 604947146 536870912 3 2 536870912 268435456 Ns528p277 Ns528p180 Ns528p278 Ns528p279 Ns528p183 Ns528p278 484817546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 604947146) qz375 0 2 Ns528p277 Ns528p180 Ns528p278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 604947146) qz376 0 2 Ns528p279 Ns528p183 Ns528p278 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p281 := nat_lit 4035158757905160315803955225361 

noncomputable def Ns528p282 := BSN.cos_dyadic_bound_f 44819309 536870912 2 1 536870912 268435456 Ns528p281 Ns528p141 Ns528p281 Ns528p281 Ns528p142 Ns528p281 535001184 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 44819309) qz20 0 1 Ns528p281 Ns528p141 Ns528p281 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 44819309) qz377 0 1 Ns528p281 Ns528p142 Ns528p281 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p283 := BSN.cos_dyadic_bound_f 2265202 536870912 1 0 536870912 268435456 0 1 1 0 1 1 536866133 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2265202) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 2265202) qz377 0 0 rfl) rfl rfl 

noncomputable def Ns528p284 := Ns528p245 137138 BSN.abs_quadSignPos (BSN.cos_quad_nat0 352 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535001184 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 222 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536866133 536870912) qz38 rfl rfl (Ns528p274 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p276 rfl rfl) (Ns528p280 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p273 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p282 rfl rfl) (Ns528p283 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p285 := nat_lit 55450225039211847972304750046185077230957313131919545532235779115159571866735197784008303181862963188208942780416 

noncomputable def Ns528p286 := nat_lit 3704532833391422168407083947325479222839426654701092355177229861158776377997547327194126912800280251273216 

noncomputable def Ns528p287 := nat_lit 277145613733855501773500631169365707433302093206756100885109576877918078842931214414970880783390613394106227429376 

noncomputable def Ns528p288 := BSN.sin_dyadic_bound_f 627183254 536870912 4 3 536870912 268435456 Ns528p285 Ns528p135 Ns528p286 Ns528p287 Ns528p138 Ns528p286 493950557 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 627183254) qz375 0 3 Ns528p285 Ns528p135 Ns528p286 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 627183254) qz376 0 3 Ns528p287 Ns528p138 Ns528p286 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p289 := nat_lit 120625039720203383349149422143489946999224101269552507232487458080819822352918078597398676674770106797533775390625 

noncomputable def Ns528p290 := nat_lit 38053498033631482684381302901002027482761432586598539890870350439498029226717990422401275694370269775390625 

noncomputable def Ns528p291 := nat_lit 602626530041742225451526009055264973948638710057584333206813251604371018666986105833627820708293356506589775390625 

noncomputable def Ns528p292 := BSN.sin_dyadic_bound_f 761551975 536870912 4 3 536870912 268435456 Ns528p289 Ns528p135 Ns528p290 Ns528p291 Ns528p138 Ns528p290 530656887 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 761551975) qz375 0 3 Ns528p289 Ns528p135 Ns528p290 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 761551975) qz376 0 3 Ns528p291 Ns528p138 Ns528p290 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p293 := Ns528p243 184577 BSN.abs_quadSignPos (BSN.cos_quad_nat3 115 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 493950557 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530656887 536870912) qz38 rfl rfl (Ns528p284 rfl rfl) (Ns528p273 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p288 rfl rfl) (Ns528p292 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p294 := nat_lit 130239829010561266359960302982335102437952485534323076502458839005390952200852060038523562046721604292226214400000 

noncomputable def Ns528p295 := nat_lit 47882290045437888726789024297869676466363026235817688567134399068323213352266919006809311260561000000000000 

noncomputable def Ns528p296 := nat_lit 650617922099535427832963797336126316001975609895853768342863593603730840208507639552710067154269178466027072000000 

noncomputable def Ns528p297 := BSN.sin_dyadic_bound_f 776273170 536870912 4 3 536870912 268435456 Ns528p294 Ns528p135 Ns528p295 Ns528p296 Ns528p138 Ns528p295 532690437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 776273170) qz375 0 3 Ns528p294 Ns528p135 Ns528p295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 776273170) qz376 0 3 Ns528p296 Ns528p138 Ns528p295 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p298 := nat_lit 7232313763040759978556168255983093664059658969918257600715142281819786241 

noncomputable def Ns528p299 := nat_lit 2683209925675356328512465380281736040412179407614559109305285337615361 

noncomputable def Ns528p300 := nat_lit 21691574869270929223011479837188717520098152550939543683926816274784128001 

noncomputable def Ns528p301 := BSN.cos_dyadic_bound_f 477069697 536870912 3 2 536870912 268435456 Ns528p298 Ns528p165 Ns528p299 Ns528p300 Ns528p168 Ns528p299 338491923 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 477069697) qz20 0 2 Ns528p298 Ns528p165 Ns528p299 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 477069697) qz377 0 2 Ns528p300 Ns528p168 Ns528p299 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p302 := Ns528p241 226025 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 532690437 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 338491923 536870912) qz38 rfl rfl (Ns528p293 rfl) (Ns528p273 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p297 rfl rfl) (Ns528p301 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p303 := nat_lit 161288702508751875161028843662297418880288856495404827459338414119722712911176186990315689889722929120048075583921 

noncomputable def Ns528p304 := nat_lit 90846378406590207479507207353211992473839280055308629573365570797562656364320515554064666288821999470195121 

noncomputable def Ns528p305 := nat_lit 805552674786126326893832355137154276227079638298567437764953135433985114228564201002830776846241629246094919938481 

noncomputable def Ns528p306 := BSN.sin_dyadic_bound_f 818827277 536870912 4 3 536870912 268435456 Ns528p303 Ns528p135 Ns528p304 Ns528p305 Ns528p138 Ns528p304 536312549 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 818827277) qz375 0 3 Ns528p303 Ns528p135 Ns528p304 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 818827277) qz376 0 3 Ns528p305 Ns528p138 Ns528p304 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p307 := nat_lit 9203560389803181317163675035688030626899355731030765538406306122350240000 

noncomputable def Ns528p308 := nat_lit 1341721967148558834425723284124781387893676013387401369812448100000000 

noncomputable def Ns528p309 := nat_lit 24102390613918662925887221541484830567251246677249377760274914928279200000 

noncomputable def Ns528p310 := BSN.sin_dyadic_bound_f 437479610 536870912 3 2 536870912 268435456 Ns528p307 Ns528p180 Ns528p308 Ns528p309 Ns528p183 Ns528p308 390646565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 437479610) qz375 0 2 Ns528p307 Ns528p180 Ns528p308 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 437479610) qz376 0 2 Ns528p309 Ns528p183 Ns528p308 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz601 := (BSN.cos_quad_nat1 181 rfl)

noncomputable def Ns528p311 := Ns528p239 263302 BSN.abs_quadSignNeg qz601 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536312549 536870912) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 390646565 536870912) qz38 rfl rfl (Ns528p302 rfl) (Ns528p273 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p306 rfl rfl) (Ns528p310 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p312 := nat_lit 197278809510316287238559893351586213200445648534402813733425666032992256 

noncomputable def Ns528p313 := nat_lit 1997903570218288746075295102167956051393743789503948342764230475776 

noncomputable def Ns528p314 := nat_lit 591832432723808425138187529464554303689234158115629433303591469638025216 

noncomputable def Ns528p315 := BSN.cos_dyadic_bound_f 193897324 536870912 3 2 536870912 268435456 Ns528p312 Ns528p165 Ns528p313 Ns528p314 Ns528p168 Ns528p313 502235695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 193897324) qz20 0 2 Ns528p312 Ns528p165 Ns528p313 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 193897324) qz377 0 2 Ns528p314 Ns528p168 Ns528p313 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p316 := Ns528p237 Bool.false 1238345137 263302 Bool.true 193897324 28296951008113761 1 Bool.false 502235695 Bool.false Bool.false 1383328098 280723 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 502235695 536870912) qz38 rfl (Ns528p311 rfl) (Ns528p273 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p315 rfl rfl) rfl 

noncomputable def Ns528p317 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) 1383328098 536870912 280723 536870912 1383328098 536870912 280723 536870912 1485337235136970752 691664049 134217728 280723 268435456 (Ns528p316 rfl rfl rfl rfl) 

noncomputable def Ns528p318 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz36) (Zeta.RiemannSiegel.correction qz37) 19315813 67108864 1 67108864 53981766573637 70368744177664 78975763365491 9895604649984000000 1042701708546023021881 4722366482869645213696 

noncomputable def Ns528p319 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz36 1 1 0 1 19315813 67108864 1 67108864 19315813 67108864 1 67108864 

noncomputable abbrev qz44 := qz389

noncomputable def Ns528p320 := @Enclosure.Real.IsNear.sqrt_image qz44 9777941602239 67108864000 915477 67108864000 405026694 405026733 33554432 (@Enclosure.Real.IsNear.of_eq qz44 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 9777941602239 67108864000 915477 67108864000 (BSN.t_div_two_pi_mk qz35 915477 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 915477 1000 0 1 10680707 67108864 1 67108864 9777941602239 67108864000 915477 67108864000 (Enclosure.Real.IsNear.const Bool.false 915477 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz725 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 915477 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz602 := qz725

noncomputable abbrev qz397 := qz602

noncomputable abbrev qz45 := qz397

noncomputable def Ns528p321 := @Enclosure.Real.IsNear.sqrt_image qz45 810053427 67108864 39 67108864 116578045 116578051 33554432 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 810053427 67108864 39 67108864 810053427 67108864 39 67108864 (Ns528p320 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p322 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz45) 455383 131072 3 33554432 9657906 9657907 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz45) Bool.false 233156096 67108864 6 67108864 455383 131072 3 33554432 (Ns528p321 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p323 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz45)) Bool.false 19315813 67108864 1 67108864 19315813 67108864 1 67108864 (Ns528p322 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz390))

noncomputable abbrev qz603 := (@HMul.hMul Real Real Real qz713 qz724 qz724)

noncomputable abbrev qz398 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz603 qz597) qz594)

noncomputable abbrev qz47 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz398))

noncomputable def Ns528p324 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz46) qz47) Bool.false 53981766573637 

noncomputable def Ns528p325 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz46) qz47 9291289 8388608 39 

noncomputable def Ns528p326 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz46) Bool.false 74330312 67108864 312 67108864 9291289 8388608 39 

noncomputable def Ns528p327 := @Enclosure.Real.IsNear.recentre' qz46 Bool.false 30294502 33554432 1140554432 301989888000000 15147251 16777216 17821163 4718592000000 

noncomputable abbrev qz48 := (@HMul.hMul Real Real Real qz355 qz352 qz390)

noncomputable def Ns528p328 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 29826651) qz19) Bool.false 29826651 67108864 123 33554432 Bool.false 30294502 33554432 1 

noncomputable def Ns528p329 := nat_lit 1052456940993494699065954641 

noncomputable def Ns528p330 := nat_lit 288230376151711744000000000000000 

noncomputable def Ns528p331 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 4747059 67108864 39 67108864 4197727998613296794745 9444732965739290427392 Ns528p329 

noncomputable def Ns528p332 := @Enclosure.Real.IsNear.subLit_ff_p qz45 qz1 810053427 67108864 39 67108864 12 1 0 1 4747059 4747059 67108864 39 

noncomputable def Ns528p333 := @Ns528p332 67108864 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 810053427 67108864 39 67108864 810053427 67108864 39 67108864 (Ns528p320 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p334 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 4197727998613296794745 9444732965739290427392 Ns528p329 Ns528p330 29826651 67108864 123 33554432 (@Ns528p331 Ns528p330 RS529to540.d55 (Ns528p333 rfl rfl) rfl) 

noncomputable def Ns528p335 := nat_lit 26968506011696257182801690901681529867404408403472437310896058081 

noncomputable def Ns528p336 := nat_lit 626377199423728630025103243002072976525566985483816641343201 

noncomputable def Ns528p337 := nat_lit 80904265280689924091145022498558585456260174076446344299405487841 

noncomputable def Ns528p338 := BSN.cos_dyadic_bound_f 29826651 67108864 3 2 33554432 9000000 Ns528p335 Ns528p226 Ns528p336 Ns528p337 Ns528p229 Ns528p336 30294502 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 29826651) qz383 0 2 Ns528p335 Ns528p226 Ns528p336 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 29826651) (BSN.cosOddQ 67108864) 0 2 Ns528p337 Ns528p229 Ns528p336 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p339 := @Enclosure.Real.IsNear.inv_image qz46 15147251 16777216 17821163 4718592000000 37165000 37165312 33554432 (Ns528p327 (@Ns528p328 9000000 (Ns528p334 rfl) (Enclosure.sfrac_false_div 29826651 67108864) (Ns528p338 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p340 := @Enclosure.Real.IsNear.recentre' qz47 Bool.false 23239732 33554432 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz355 qz352 qz398)

noncomputable def Ns528p341 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 54070401)) qz19) Bool.true 54070401 67108864 

noncomputable def Ns528p342 := nat_lit 510680508204793760648883096805 

noncomputable def Ns528p343 := nat_lit 16124276230871514783941661451302073 

noncomputable def Ns528p344 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns528p342 Ns528p217 Ns528p343 

noncomputable def Ns528p345 := nat_lit 3868562622766813359059763200000000000000 

noncomputable abbrev qz50 := qz398

noncomputable def Ns528p346 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 577510144392151 

noncomputable abbrev qz399 := (@HSub.hSub Real Real Real qz581 qz603 qz597)

noncomputable abbrev qz51 := qz399

noncomputable def Ns528p347 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 296035167681495 4503599627370496 2987517819 4503599627370496 1 16 

noncomputable abbrev qz400 := qz603

noncomputable abbrev qz52 := qz400

noncomputable def Ns528p348 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 22534569149481 4503599627370496 370272123 4503599627370496 4747059 67108864 39 67108864 

noncomputable def Ns528p349 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 4747059 67108864 39 67108864 4747059 67108864 39 67108864 22534569149481 4503599627370496 

noncomputable def Ns528p350 := nat_lit 291323903460525256338423653860203979474070440339893541540531758081 

noncomputable def Ns528p351 := nat_lit 73059504664604960690433064556657237517395816219721345989043201 

noncomputable def Ns528p352 := nat_lit 873825591372246559093890095451498623947176529387241181929617187841 

noncomputable def Ns528p353 := BSN.cos_dyadic_bound_f 54070401 67108864 3 2 33554432 9000000 Ns528p350 Ns528p226 Ns528p351 Ns528p352 Ns528p229 Ns528p351 23239732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 54070401) qz383 0 2 Ns528p350 Ns528p226 Ns528p351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 54070401) (BSN.cosOddQ 67108864) 0 2 Ns528p352 Ns528p229 Ns528p351 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p354 := @Ns528p340 2596108864 603979776000000 5809933 8388608 40564201 9437184000000 (@Ns528p341 281 67108864 Bool.false 23239732 33554432 1 9000000 (@Ns528p344 Ns528p345 54070401 67108864 281 67108864 (@Ns528p346 4503599627370496 2987517819 4503599627370496 Ns528p342 Ns528p217 Ns528p343 Ns528p345 RS529to540.d55 (@Ns528p347 0 1 9240162310274416 577510144392151 4503599627370496 2987517819 4503599627370496 (@Ns528p348 19866583807154643271680 296035167681495 4503599627370496 2987517819 4503599627370496 (@Ns528p349 370272123 4503599627370496 (Ns528p333 rfl rfl) (Ns528p333 rfl rfl) rfl) (Ns528p333 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 54070401 67108864) (BSN.cos_neg_of_bound 54070401 67108864 Bool.false 23239732 33554432 1 9000000 (Ns528p353 rfl rfl)) rfl rfl) 

noncomputable def Ns528p355 := @Ns528p318 1533072341600255877799 Ns528p234 (Ns528p319 qz33 (@Enclosure.Real.IsNear.of_eq qz36 (@Inv.inv Real Real.instInv (Real.sqrt qz45)) Bool.false 19315813 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz44 (BSN.t_div_two_pi_nonneg qz35 915477 1000 qz38)) Ns528p323) rfl) (@Ns528p324 70368744177664 78975763365491 9895604649984000000 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 915477 1000 12 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 915477 1000 12 qz38 rfl rfl rfl))) (@Ns528p325 8388608 5809933 8388608 40564201 9437184000000 53981766573637 70368744177664 78975763365491 9895604649984000000 (@Ns528p326 8388608 (Ns528p339 rfl rfl rfl rfl rfl) rfl) (Ns528p354 rfl) rfl)) 

noncomputable def Ns528p356 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 23293063551938105778887 4722366482869645213696 696014028380964863877799 Ns528p234 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz36) (Zeta.RiemannSiegel.correction qz37))) Bool.false 23293063551938105778887 4722366482869645213696 696014028380964863877799 Ns528p234 (BSN.hardyZApproximantRS₀_eq qz35 12 (@BSN.floor_sqrt_eq_dec qz35 915477 1000 12 qz38 rfl rfl rfl)) (@Ns528p236 23293063551938105778887 4722366482869645213696 696014028380964863877799 Ns528p234 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12)) Bool.false 691664049 134217728 280723 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (Ns528p317 (Ns528p316 rfl rfl rfl rfl) rfl rfl)) (Ns528p355 rfl) rfl rfl)) 

theorem RS529to540.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 23293063551938105778887 4722366482869645213696 696014028380964863877799 Ns528p234 := Ns528p356 

noncomputable abbrev qz604 := (@HMul.hMul Real Real Real qz713 (Real.sqrt qz721) qz715)

noncomputable abbrev qz401 := qz604

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz401)

noncomputable abbrev qz402 := (@HMul.hMul Real Real Real qz577 (@HMul.hMul Real Real Real qz577 qz604 qz604) qz604)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz355 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz402))

noncomputable abbrev qz403 := (@HMul.hMul Real Real Real qz577 qz592 qz592)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz355 qz403 qz380))

noncomputable abbrev qz605 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns528p357 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz373 (@HAdd.hAdd Real Real Real qz373 qz605 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns528p358 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz373 qz605 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 26582601 2147483648 

noncomputable def Ns528p359 := @Enclosure.Real.IsNear.addLit_ff qz605 qz54 3322825 268435456 25 268435456 

noncomputable def Ns528p360 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 132913 67108864 1 67108864 3322825 

noncomputable def Ns528p361 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 132913 67108864 1 67108864 132913 67108864 1 67108864 

noncomputable def Ns528p362 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz21 116517737 33554432 3 33554432 609857688993 4194304000 57099 4194304000 71059237813514168841 140737488355328000 8482619503239 

noncomputable def Ns528p363 := @Enclosure.Real.IsNear.sqrt_image qz21 609857688993 4194304000 57099 4194304000 404607725 404607764 33554432 qz22 

noncomputable def Ns528p364 := @Enclosure.Real.IsNear.sqrt_image qz23 809215489 67108864 39 67108864 116517734 116517740 33554432 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 809215489 67108864 39 67108864 809215489 67108864 39 67108864 (Ns528p363 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz404 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 233035474 67108864 6 67108864 116517737 33554432 3 33554432 (Ns528p364 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns528p365 := @Ns528p362 140737488355328000 qz404 

noncomputable def Ns528p366 := Ns528p365 qz22 

noncomputable abbrev qz56 := qz401

noncomputable def Ns528p367 := @Enclosure.Real.IsNear.inv_image qz56 71059237813514168841 140737488355328000 8482619503239 140737488355328000 66456 66457 33554432 (Ns528p366 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz402)

noncomputable def Ns528p368 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns528p369 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 67108864 1 67108864 

noncomputable def Ns528p370 := nat_lit 358807601103898422744560134427091750334914299265376518447321 

noncomputable def Ns528p371 := nat_lit 2787593149816327892691964784081045188247552000000000 

noncomputable def Ns528p372 := nat_lit 128496820906739432695387384686713542497229698144464679 

noncomputable abbrev qz58 := qz402

noncomputable def Ns528p373 := @Enclosure.Real.IsNear.inv_image qz58 Ns528p370 Ns528p371 Ns528p372 Ns528p371 0 1 

noncomputable def Ns528p374 := nat_lit 5049415278637561914866571539063055283281 

noncomputable def Ns528p375 := nat_lit 19807040628566084398385987584000000 

noncomputable def Ns528p376 := nat_lit 1205537025079260683560521916243119 

noncomputable abbrev qz405 := (@HMul.hMul Real Real Real qz577 qz604 qz604)

noncomputable abbrev qz59 := qz405

noncomputable def Ns528p377 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns528p374 Ns528p375 Ns528p376 Ns528p375 71059237813514168841 140737488355328000 8482619503239 

noncomputable def Ns528p378 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 71059237813514168841 140737488355328000 8482619503239 140737488355328000 71059237813514168841 140737488355328000 8482619503239 140737488355328000 Ns528p374 

noncomputable def Ns528p379 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 1602705 67108864 1 

noncomputable def Ns528p380 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 1602705 67108864 1 67108864 1602705 67108864 

noncomputable def Ns528p381 := nat_lit 1581889427953438646434553 

noncomputable abbrev qz60 := qz403

noncomputable def Ns528p382 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz24 13576383035601169 1125899906842624 699106431 1125899906842624 116517737 33554432 3 33554432 Ns528p381 

noncomputable def Ns528p383 := @Enclosure.Real.IsNear.mulLit_ff qz24 qz24 116517737 33554432 3 33554432 116517737 33554432 3 33554432 13576383035601169 1125899906842624 699106431 

noncomputable def Ns528p384 := @Ns528p383 1125899906842624 qz404 

noncomputable def Ns528p385 := Ns528p384 qz404 

noncomputable def Ns528p386 := @Ns528p382 37778931862957161709568 122187450466389447 37778931862957161709568 (Ns528p385 rfl) qz404 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz355 qz403 qz380)

noncomputable def Ns528p387 := @Enclosure.Real.IsNear.inv_image qz61 Ns528p381 37778931862957161709568 122187450466389447 37778931862957161709568 801352 801353 33554432 (Ns528p386 rfl) 

noncomputable def Ns528p388 := @Ns528p358 201 2147483648 4167033 134217728 13 671088640 12516491538726912 93255129 2147483648 1213 10737418240 (@Ns528p359 1 2147483648 1 2147483648 7135712621101056 26582601 2147483648 201 2147483648 (@Ns528p360 268435456 25 268435456 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns528p361 (Ns528p367 rfl rfl rfl rfl) rfl) rfl) (@Ns528p368 67108864 1 67108864 1 2147483648 1 2147483648 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns528p369 1 67108864 1 67108864 (@Ns528p373 33554432 (@Ns528p377 140737488355328000 Ns528p370 Ns528p371 Ns528p372 Ns528p371 (@Ns528p378 Ns528p375 Ns528p376 Ns528p375 (Ns528p366 rfl) (Ns528p366 rfl) rfl) (Ns528p366 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns528p379 67108864 4167033 134217728 13 671088640 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns528p380 1 67108864 (Ns528p387 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS529to540.d60 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 := @Ns528p357 93255129 2147483648 1213 10737418240 (BSN.hardyZErrorBoundRS₀_mk qz4 913584 1000 qz9 rfl rfl) (Ns528p388 rfl rfl) 

noncomputable def Ns528p389 := nat_lit 708354972430446782054400000 

noncomputable def Ns528p390 := nat_lit 381120275630153192839760052224 

noncomputable abbrev qz726 := (Enclosure.sfrac Bool.false 916738 1000)

noncomputable abbrev qz606 := qz726

noncomputable abbrev qz406 := qz606

noncomputable abbrev qz62 := qz406

noncomputable abbrev qz727 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 916738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz607 := qz727

noncomputable abbrev qz407 := qz607

noncomputable abbrev qz63 := (@HPow.hPow Real Real Real qz356 qz407 qz358)

noncomputable abbrev qz728 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 916738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz608 := qz728

noncomputable abbrev qz408 := qz608

noncomputable abbrev qz64 := qz408

noncomputable def Ns528p391 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz63) (Zeta.RiemannSiegel.correction qz64)) 73458691 33554432 140551 134217728 1019877653606984967209 4722366482869645213696 1685499759498743878757 Ns528p389 Ns528p390 

noncomputable def Ns528p392 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos BSN.quadSignPos 11 12 916738 1000 288 536870912 268435456 9007199254740992 Bool.false 979932051025 4475 1334074092 61 154981288 8 

noncomputable def Ns528p393 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 916738 1000 181 237 536870912 268435456 9007199254740992 Bool.false 979932051025 4475 

noncomputable def Ns528p394 := Ns528p393 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.true 466127868 226329 Bool.true 691184564 Bool.true 374361339 28296951008113761 1 Bool.false 515460570 Bool.true Bool.false 344752759 Bool.true Bool.true 733077683 

noncomputable def Ns528p395 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 916738 1000 51 120 536870912 268435456 9007199254740992 Bool.false 979932051025 4475 

noncomputable def Ns528p396 := Ns528p395 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.true 773399618 184824 Bool.true 497563564 Bool.true 278098508 28296951008113761 1 Bool.false 429332114 Bool.false Bool.false 466439772 Bool.false Bool.true 466127868 

noncomputable def Ns528p397 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 916738 1000 116 26 536870912 268435456 9007199254740992 Bool.false 979932051025 4475 

noncomputable def Ns528p398 := Ns528p397 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.true 793335349 137320 Bool.false 257337111 Bool.false 287346723 28296951008113761 1 Bool.false 476368333 Bool.false Bool.false 461791610 Bool.true Bool.true 773399618 

noncomputable def Ns528p399 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 3 4 5 916738 1000 352 222 536870912 268435456 9007199254740992 Bool.false 979932051025 4475 

noncomputable def Ns528p400 := Ns528p399 744261104 60 268435448 8 864060384 60 240095976 8 Bool.true 713100186 80960 Bool.false 792785566 Bool.false 599164567 28296951008113761 1 Bool.false 50454723 Bool.false Bool.false 235821367 Bool.true Bool.true 793335349 

noncomputable def Ns528p401 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 916738 1000 757 520 536870912 268435456 9007199254740992 Bool.false 979932051025 4475 

noncomputable def Ns528p402 := Ns528p401 372130544 60 379625064 8 589812976 60 309962568 8 Bool.true 536870872 4540 Bool.false 396493984 Bool.false 704357635 28296951008113761 1 Bool.false 361421421 Bool.true Bool.false 137410908 Bool.false Bool.true 713100186 

noncomputable def Ns528p403 := nat_lit 274460708425556173557049298262376984734242255568714567751 

noncomputable def Ns528p404 := nat_lit 150367538939429866914894686471531839691483967494553600 

noncomputable def Ns528p405 := nat_lit 310790498937128033956934315760640000 

noncomputable def Ns528p406 := nat_lit 1709480999800574260403831050001961553920 

noncomputable abbrev qz609 := (@Eq.refl Real qz726)

noncomputable abbrev qz409 := qz609

noncomputable abbrev qz65 := qz409

noncomputable def Ns528p407 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 916738 1000 3361635242576 16000000 1833476 4000 2000 Ns528p405 Ns528p406 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p408 := nat_lit 5620955308555390434448369628413480647357281394047274347540480 

noncomputable abbrev qz610 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1833476))))

noncomputable abbrev qz410 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 916738 4000) (Real.log (Enclosure.sfrac Bool.false 3361635242576 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz610))

noncomputable abbrev qz611 := (Enclosure.sfrac Bool.false 916738 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz410 qz611) (@HMul.hMul Real Real Real qz355 qz611 (Real.log Real.pi)))

noncomputable def Ns528p409 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns528p405 Ns528p406) 3288106664585048689819 1801439850948198400 204805877662725749 24576000000000000000000 Ns528p405 Ns528p406 0 1 Ns528p408 

noncomputable def Ns528p410 := nat_lit 551652757427829122396103639040000 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz361 qz410 qz611)

noncomputable def Ns528p411 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz611 (Real.log Real.pi)) 21166689057977148980999 9007199254740992000 19265398377569 6000000000000000000 17606302108809 33554432000 1375107 268435456000 Ns528p410 3288106664585048689819 1801439850948198400 

noncomputable def Ns528p412 := nat_lit 42333378115954297961998000 

noncomputable abbrev qz68 := qz410

noncomputable def Ns528p413 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz611 25295309973173522743047 9007199254740992000 19265398377569 6000000000000000000 916738 2000 0 1 Ns528p412 21166689057977148980999 9007199254740992000 19265398377569 6000000000000000000 

noncomputable def Ns528p414 := nat_lit 56959974284702734097841691762838470656 

noncomputable def Ns528p415 := nat_lit 118526466244708498275303424 

noncomputable def Ns528p416 := nat_lit 94606692794930091308905571949375837474193842458696797984247823102074291297243744337170508272937147801516571248084953244643199555669639574125634648557758709760 

noncomputable def Ns528p417 := nat_lit 1748789639956696848382797112184365252834368590552257804017291335952530095411472605576231156035321209201354820435785862017231178939723790317394335934942543872 

noncomputable def Ns528p418 := nat_lit 173692646736633644919046271857016590214495891906027418697870385224005621442678821882288380394495826428825493280617061122322940090341622628585329131520 

noncomputable def Ns528p419 := BSN.log_dyadic_bound 1264483242576 5458787242576 7 6 Ns528p416 268435456 72000000 Ns528p417 Ns528p418 126660545 6723270485152 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1264483242576) (BSN.artanhQ 5458787242576) 0 6 Ns528p417 Ns528p416 Ns528p418 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz411 := (Real.log (Enclosure.sfrac Bool.false 3361635242576 16000000))

noncomputable def Ns528p420 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 916738 4000) qz411 916738 4000 0 1 55193186851548263 4503599627370496 125000153 9000000000000000 25298845863957325763047 9007199254740992000 57296195130457 18000000000000000000 (Enclosure.Real.IsNear.const Bool.false 916738 4000) (BSN.isNear_log_sfrac 3361635242576 16000000 55193186851548263 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3361635242576) qz364)) Bool.false Ns528p415 Ns528p113 1000001224000000 72000000000000000000000 55193186851548263 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3361635242576 16000000 17 6723270485152 4194304000000 126660545 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p419 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p421 := BSN.arctan_dyadic_bound_f 1000 1833476 1 0 33554432 9000000 0 1 1 0 1 1 18300 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1833476) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1833476) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz412 := (@Nat.cast Real Real.instNatCast 1833476)

noncomputable def Ns528p422 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz412)) 884279719003555 562949953421312 1 2000000000000000 18300 33554432 1 9000000 29661201716136283996160 883972695950755 562949953421312 2000000009 18000000000000000 qz15 (Ns528p421 rfl) rfl rfl 

noncomputable abbrev qz413 := (@HMul.hMul Real Real Real qz577 qz582 qz610)

noncomputable abbrev qz69 := qz413

noncomputable abbrev qz414 := qz610

noncomputable abbrev qz70 := qz414

noncomputable def Ns528p423 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 916738 4000) qz411) qz69 25298845863957325763047 9007199254740992000 57296195130457 18000000000000000000 883972695950755 2251799813685248 2000000009 72000000000000000 Ns528p414 25295309973173522743047 9007199254740992000 19265398377569 6000000000000000000 (Ns528p420 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz70 1 4 0 1 883972695950755 562949953421312 2000000009 18000000000000000 883972695950755 2251799813685248 2000000009 72000000000000000 qz372 Ns528p422 rfl) 

noncomputable def Ns528p424 := @Ns528p409 Ns528p403 Ns528p404 204805877662725749 24576000000000000000000 (@Ns528p411 204805877662725749 24576000000000000000000 (Ns528p413 (Ns528p423 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 916738 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz611 (Real.log Real.pi) 916738 2000 0 1 38410761 33554432 3 268435456 17606302108809 33554432000 1375107 268435456000 (Enclosure.Real.IsNear.const Bool.false 916738 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p405 Ns528p406) 

noncomputable def Ns528p425 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns528p403 Ns528p404 204805877662725749 24576000000000000000000 61245753189 33554432 35 4194304 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz373 qz66 (Enclosure.sfrac Bool.true Ns528p405 Ns528p406)) Bool.false Ns528p403 Ns528p404 204805877662725749 24576000000000000000000 Ns528p407 (Ns528p424 rfl rfl)) 

noncomputable def Ns528p426 := nat_lit 4835703278458516698824704 

noncomputable def Ns528p427 := BSN.cos_dyadic_bound_f 48059670 137438953472 1 0 67108864 18017579 0 1 1 0 1 1 67108859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 48059670) qz588 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 48059670) qz589 0 0 rfl) rfl rfl 

noncomputable abbrev qz415 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable def Ns528p428 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 61245753189) qz415) Bool.false 61245753189 33554432 35 4194304 Bool.true 67108859 67108864 1 9000000 (Ns528p425 rfl) (Enclosure.sfrac_false_div 61245753189 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 61245753189) qz415) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1690949334028766937088) (@Nat.cast Real Real.instNatCast Ns528p426)) 226375608064910080 72057594037927936 Bool.false 67108859 67108864 290 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q2 61245753189 33554432 226375608064910080 72057594037927936 290 1690949334028766937088 Ns528p426 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108859 67108864 1690949334028766937088 Ns528p426 48059670 137438953472 18017579 18000000 (Ns528p427 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p429 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns528p403 Ns528p404 204805877662725749 24576000000000000000000 979932051025 536870912 4475 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz373 qz66 (Enclosure.sfrac Bool.true Ns528p405 Ns528p406)) Bool.false Ns528p403 Ns528p404 204805877662725749 24576000000000000000000 Ns528p407 (Ns528p424 rfl rfl)) 

noncomputable def Ns528p430 := Ns528p402 80960 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 757 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 361421421 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 520 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 137410908 536870912) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 67108859 67108864 4987411 589824000000 536870872 536870912 4540 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 67108859 67108864 4987411 589824000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 67108859 67108864 319194304 37748736000000 67108859 67108864 4987411 589824000000 (Ns528p428 rfl rfl) rfl)) rfl) (Ns528p429 rfl) RS529to540.d7 

noncomputable def Ns528p431 := nat_lit 6209411106507854828773675038950201933772990995147592147067821430826598400 

noncomputable def Ns528p432 := nat_lit 610791264613268088499807081136403961105003166426706179373968492855296 

noncomputable def Ns528p433 := nat_lit 16261754474044531641311577795309641362992234982164717146601498274605039616 

noncomputable def Ns528p434 := BSN.sin_dyadic_bound_f 396493984 536870912 3 2 536870912 268435456 Ns528p431 Ns528p180 Ns528p432 Ns528p433 Ns528p183 Ns528p432 361421421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 396493984) qz375 0 2 Ns528p431 Ns528p180 Ns528p432 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 396493984) qz376 0 2 Ns528p433 Ns528p183 Ns528p432 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p435 := nat_lit 33964328478527104000365645955603996035332629339595217872668301208079820384260876987337465284850034498842870640625 

noncomputable def Ns528p436 := nat_lit 14911410248032347739945792080359770663796812386568392261387732405687266259303494567265628250252226806640625 

noncomputable def Ns528p437 := nat_lit 205808359203760776241033464398839989370926381347819641461483003460424527649038723473804302003205893964778128240625 

noncomputable def Ns528p438 := BSN.cos_dyadic_bound_f 704357635 536870912 4 3 536870912 268435456 Ns528p435 Ns528p145 Ns528p436 Ns528p437 Ns528p148 Ns528p436 137410908 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 704357635) qz20 0 3 Ns528p435 Ns528p145 Ns528p436 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 704357635) qz377 0 3 Ns528p437 Ns528p148 Ns528p436 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p439 := nat_lit 54567693502878430797069489139176749574965088371749431150053507439388337734579133063939471840375342904119128231936 

noncomputable def Ns528p440 := nat_lit 61640877677157425396847992283108377877960608753796465218887439506164889867604636779248941091805875736416256 

noncomputable def Ns528p441 := nat_lit 330420820241679203655792308847642689749831449870099993578308430202329416250285063080487215600769966341202766991360 

noncomputable def Ns528p442 := BSN.cos_dyadic_bound_f 792785566 536870912 4 3 536870912 268435456 Ns528p439 Ns528p145 Ns528p440 Ns528p441 Ns528p148 Ns528p440 50454723 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 792785566) qz20 0 3 Ns528p439 Ns528p145 Ns528p440 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 792785566) qz377 0 3 Ns528p441 Ns528p148 Ns528p440 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p443 := nat_lit 17769291272208150882295038457361692858848582787347710936785599798014034281407415069536238772904086099437957823841 

noncomputable def Ns528p444 := nat_lit 2140688466278451565357558510716351706666820375071658279549507515968574470708102319915644865566545131486561 

noncomputable def Ns528p445 := nat_lit 107734054638472988725563571840742671450894871867679902331793150492746011007161103149928652614291321689722576059745 

noncomputable def Ns528p446 := BSN.cos_dyadic_bound_f 599164567 536870912 4 3 536870912 268435456 Ns528p443 Ns528p145 Ns528p444 Ns528p445 Ns528p148 Ns528p444 235821367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 599164567) qz20 0 3 Ns528p443 Ns528p145 Ns528p444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 599164567) qz377 0 3 Ns528p445 Ns528p148 Ns528p444 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p447 := Ns528p400 137320 BSN.abs_quadSignPos (BSN.cos_quad_nat0 352 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 50454723 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 222 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 235821367 536870912) qz65 rfl rfl (Ns528p430 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p434 rfl rfl) (Ns528p438 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p429 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p442 rfl rfl) (Ns528p446 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p448 := nat_lit 612085524334547103866837920780635815817096620824101263100570251590391361 

noncomputable def Ns528p449 := nat_lit 19231774951533958972458079868316191145687170352867922196319017391681 

noncomputable def Ns528p450 := nat_lit 1836218109453738243682568846182170815068998488131598053457318116736390721 

noncomputable def Ns528p451 := BSN.cos_dyadic_bound_f 257337111 536870912 3 2 536870912 268435456 Ns528p448 Ns528p165 Ns528p449 Ns528p450 Ns528p168 Ns528p449 476368333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 257337111) qz20 0 2 Ns528p448 Ns528p165 Ns528p449 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 257337111) qz377 0 2 Ns528p450 Ns528p168 Ns528p449 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p452 := nat_lit 951557390703500935119457186350524286257464017650642978169992898557056161 

noncomputable def Ns528p453 := nat_lit 46478273717734712026598741155354800361274652781374631805067940664481 

noncomputable def Ns528p454 := nat_lit 2854579215563067335934318361569262149171669503646366185246368559789839521 

noncomputable def Ns528p455 := BSN.cos_dyadic_bound_f 287346723 536870912 3 2 536870912 268435456 Ns528p452 Ns528p165 Ns528p453 Ns528p454 Ns528p168 Ns528p453 461791610 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 287346723) qz20 0 2 Ns528p452 Ns528p165 Ns528p453 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 287346723) qz377 0 2 Ns528p454 Ns528p168 Ns528p453 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p456 := Ns528p398 184824 BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 476368333 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 461791610 536870912) qz65 rfl rfl (Ns528p447 rfl rfl) (Ns528p429 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p451 rfl rfl) (Ns528p455 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p457 := nat_lit 15401446259150808452360262435350453853437654907778852379214703103777505280 

noncomputable def Ns528p458 := nat_lit 3756544689350173014868114632573915392934892345023190871644325145542656 

noncomputable def Ns528p459 := nat_lit 40331039130183645666538519906988926134081487313719337731770131602514968576 

noncomputable def Ns528p460 := BSN.sin_dyadic_bound_f 497563564 536870912 3 2 536870912 268435456 Ns528p457 Ns528p180 Ns528p458 Ns528p459 Ns528p183 Ns528p458 429332114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 497563564) qz375 0 2 Ns528p457 Ns528p180 Ns528p458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 497563564) qz376 0 2 Ns528p459 Ns528p183 Ns528p458 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p461 := nat_lit 834837647760350571884895723320913034325294892324621112779973814397239296 

noncomputable def Ns528p462 := nat_lit 35775793164006098296405508601172770586235575532909186670304092553216 

noncomputable def Ns528p463 := nat_lit 2504441391694723703458094358945536757434712205822797519966580835006611456 

noncomputable def Ns528p464 := BSN.cos_dyadic_bound_f 278098508 536870912 3 2 536870912 268435456 Ns528p461 Ns528p165 Ns528p462 Ns528p463 Ns528p168 Ns528p462 466439772 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 278098508) qz20 0 2 Ns528p461 Ns528p165 Ns528p462 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 278098508) qz377 0 2 Ns528p463 Ns528p168 Ns528p462 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p465 := Ns528p396 226329 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 429332114 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 466439772 536870912) qz65 rfl rfl (Ns528p456 rfl) (Ns528p429 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p460 rfl rfl) (Ns528p464 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p466 := nat_lit 81814186838621125959043169133563149896317561165171029515681653567461753522678609524025898933313142898388417642496 

noncomputable def Ns528p467 := nat_lit 11888535732852247094076147306171283001984814252080287799361780624814130848317498803814719095008097988509696 

noncomputable def Ns528p468 := nat_lit 408841358858329133660707760520625035303120770110183821979681647919169201396813767537741482758122973810975945261056 

noncomputable def Ns528p469 := BSN.sin_dyadic_bound_f 691184564 536870912 4 3 536870912 268435456 Ns528p466 Ns528p135 Ns528p467 Ns528p468 Ns528p138 Ns528p467 515460570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 691184564) qz375 0 3 Ns528p466 Ns528p135 Ns528p467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 691184564) qz376 0 3 Ns528p468 Ns528p138 Ns528p467 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p470 := nat_lit 4934682374254651187477929817299973567874972719042661552156435283994062305 

noncomputable def Ns528p471 := nat_lit 385769542317409689486535532532514516004561353353999096720623508762081 

noncomputable def Ns528p472 := nat_lit 12923543543788905875325885606828211463789492593396778542824544734303596001 

noncomputable def Ns528p473 := BSN.sin_dyadic_bound_f 374361339 536870912 3 2 536870912 268435456 Ns528p470 Ns528p180 Ns528p471 Ns528p472 Ns528p183 Ns528p471 344752759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 374361339) qz375 0 2 Ns528p470 Ns528p180 Ns528p471 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 374361339) qz376 0 2 Ns528p472 Ns528p183 Ns528p471 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p474 := Ns528p394 263657 BSN.abs_quadSignNeg qz601 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 515460570 536870912) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 344752759 536870912) qz65 rfl rfl (Ns528p465 rfl) (Ns528p429 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p469 rfl rfl) (Ns528p473 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p475 := nat_lit 180687041291065510980943510513175478449088451639766414530310397028190625 

noncomputable def Ns528p476 := nat_lit 1675978328996522356295423623309416089843055813979664001044375390625 

noncomputable def Ns528p477 := nat_lit 542057771916538539898117940692279816515085668807671284262929102333790625 

noncomputable def Ns528p478 := BSN.cos_dyadic_bound_f 189685245 536870912 3 2 536870912 268435456 Ns528p475 Ns528p165 Ns528p476 Ns528p477 Ns528p168 Ns528p476 503708608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 189685245) qz20 0 2 Ns528p475 Ns528p165 Ns528p476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 189685245) qz377 0 2 Ns528p477 Ns528p168 Ns528p476 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p479 := Ns528p392 Bool.true 733077683 263657 Bool.true 189685245 28296951008113761 1 Bool.false 503708608 Bool.false Bool.true 587669528 281102 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 503708608 536870912) qz65 rfl (Ns528p474 rfl) (Ns528p429 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p478 rfl rfl) rfl 

noncomputable def Ns528p480 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) 587669528 536870912 281102 536870912 587669528 536870912 281102 536870912 631005350903939072 73458691 33554432 140551 134217728 (Ns528p479 rfl rfl rfl rfl) 

noncomputable def Ns528p481 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz63) (Zeta.RiemannSiegel.correction qz64) 1206823 4194304 1 33554432 845092986798383 1125899906842624 2594084985521813 316659348799488000000 1019877653606984967209 4722366482869645213696 

noncomputable def Ns528p482 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz63 1 1 0 1 1206823 4194304 1 33554432 1206823 4194304 1 33554432 

noncomputable abbrev qz71 := qz407

noncomputable def Ns528p483 := @Enclosure.Real.IsNear.sqrt_image qz71 4895704986883 33554432000 458369 33554432000 405305544 405305583 33554432 (@Enclosure.Real.IsNear.of_eq qz71 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 4895704986883 33554432000 458369 33554432000 (BSN.t_div_two_pi_mk qz62 916738 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 916738 1000 0 1 10680707 67108864 1 67108864 4895704986883 33554432000 458369 33554432000 (Enclosure.Real.IsNear.const Bool.false 916738 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz729 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 916738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz612 := qz729

noncomputable abbrev qz416 := qz612

noncomputable abbrev qz72 := qz416

noncomputable def Ns528p484 := @Enclosure.Real.IsNear.sqrt_image qz72 810611127 67108864 39 67108864 116618168 116618175 33554432 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 810611127 67108864 39 67108864 810611127 67108864 39 67108864 (Ns528p483 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p485 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz72) 233236343 67108864 7 67108864 9654583 9654585 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz72) Bool.false 233236343 67108864 7 67108864 233236343 67108864 7 67108864 (Ns528p484 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p486 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz72)) Bool.false 19309168 67108864 2 67108864 1206823 4194304 1 33554432 (Ns528p485 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz408))

noncomputable abbrev qz613 := (@HMul.hMul Real Real Real qz713 qz728 qz728)

noncomputable abbrev qz417 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz613 qz608) qz594)

noncomputable abbrev qz74 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz417))

noncomputable def Ns528p487 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz73) qz74) Bool.false 845092986798383 

noncomputable def Ns528p488 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz73) qz74 76331597 67108864 329 

noncomputable def Ns528p489 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz73) Bool.false 76331597 67108864 329 67108864 76331597 67108864 329 

noncomputable def Ns528p490 := @Enclosure.Real.IsNear.recentre' qz73 Bool.false 29500232 33554432 1140554432 301989888000000 3687529 4194304 17821163 4718592000000 

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz355 qz352 qz408)

noncomputable def Ns528p491 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 33330783) qz19) Bool.false 33330783 67108864 123 33554432 Bool.false 29500232 33554432 1 

noncomputable def Ns528p492 := nat_lit 1052456940998285305587913041 

noncomputable def Ns528p493 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 5304759 67108864 39 67108864 4690890797901579418245 9444732965739290427392 Ns528p492 

noncomputable def Ns528p494 := @Enclosure.Real.IsNear.subLit_ff_p qz72 qz1 810611127 67108864 39 67108864 12 1 0 1 5304759 5304759 67108864 39 

noncomputable def Ns528p495 := @Ns528p494 67108864 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 810611127 67108864 39 67108864 810611127 67108864 39 67108864 (Ns528p483 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p496 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 4690890797901579418245 9444732965739290427392 Ns528p492 Ns528p330 33330783 67108864 123 33554432 (@Ns528p493 Ns528p330 RS529to540.d55 (Ns528p495 rfl rfl) rfl) 

noncomputable def Ns528p497 := nat_lit 42055870369385168826261088852551769844043662229163585249246526721 

noncomputable def Ns528p498 := nat_lit 1523225245969767301417213606966653656905669029456767668010241 

noncomputable def Ns528p499 := nat_lit 126164564657663566944180432130441376224817175349431842212403559681 

noncomputable def Ns528p500 := BSN.cos_dyadic_bound_f 33330783 67108864 3 2 33554432 9000000 Ns528p497 Ns528p226 Ns528p498 Ns528p499 Ns528p229 Ns528p498 29500232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 33330783) qz383 0 2 Ns528p497 Ns528p226 Ns528p498 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 33330783) (BSN.cosOddQ 67108864) 0 2 Ns528p499 Ns528p229 Ns528p498 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p501 := @Enclosure.Real.IsNear.inv_image qz73 3687529 4194304 17821163 4718592000000 38165634 38165963 33554432 (Ns528p490 (@Ns528p491 9000000 (Ns528p496 rfl) (Enclosure.sfrac_false_div 33330783 67108864) (Ns528p500 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p502 := @Enclosure.Real.IsNear.recentre' qz74 Bool.false 22142678 33554432 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz355 qz352 qz417)

noncomputable def Ns528p503 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7131209)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true 7131209 8388608 

noncomputable def Ns528p504 := nat_lit 538818920729274069558923277805 

noncomputable def Ns528p505 := nat_lit 16359058325313914636025342172255393 

noncomputable def Ns528p506 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns528p504 Ns528p217 Ns528p505 

noncomputable abbrev qz77 := qz417

noncomputable def Ns528p507 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 609330858946351 

noncomputable abbrev qz418 := (@HSub.hSub Real Real Real qz581 qz613 qz608)

noncomputable abbrev qz78 := qz418

noncomputable def Ns528p508 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 327855882235695 4503599627370496 3031018419 4503599627370496 1 16 

noncomputable abbrev qz419 := qz613

noncomputable abbrev qz79 := qz419

noncomputable def Ns528p509 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 28140468048081 4503599627370496 413772723 4503599627370496 5304759 67108864 39 67108864 

noncomputable def Ns528p510 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 5304759 67108864 39 67108864 5304759 67108864 39 67108864 28140468048081 4503599627370496 

noncomputable def Ns528p511 := nat_lit 21520706860391033041100239624090333483787402497435036027201 

noncomputable def Ns528p512 := nat_lit 988643523323402220304136834155207460536120982503085435781120 

noncomputable def Ns528p513 := nat_lit 6688139435590420148477162384829010948624612206420429121 

noncomputable def Ns528p514 := nat_lit 64548744302301918283003764547501342429464958267892267223361 

noncomputable def Ns528p515 := nat_lit 44488958549553099913686157536984335724125444212638844610150400 

noncomputable def Ns528p516 := BSN.cos_dyadic_bound_f 7131209 8388608 3 2 33554432 9000000 Ns528p511 Ns528p512 Ns528p513 Ns528p514 Ns528p515 Ns528p513 22142678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 7131209) (BSN.cosEvenQ 8388608) 0 2 Ns528p511 Ns528p512 Ns528p513 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 7131209) (BSN.cosOddQ 8388608) 0 2 Ns528p514 Ns528p515 Ns528p513 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p517 := @Ns528p502 2632108864 603979776000000 11071339 16777216 41126701 9437184000000 (@Ns528p503 285 67108864 Bool.false 22142678 33554432 1 9000000 (@Ns528p506 Ns528p345 7131209 8388608 285 67108864 (@Ns528p507 4503599627370496 3031018419 4503599627370496 Ns528p504 Ns528p217 Ns528p505 Ns528p345 RS529to540.d55 (@Ns528p508 0 1 9749293743141616 609330858946351 4503599627370496 3031018419 4503599627370496 (@Ns528p509 22002035812555271700480 327855882235695 4503599627370496 3031018419 4503599627370496 (@Ns528p510 413772723 4503599627370496 (Ns528p495 rfl rfl) (Ns528p495 rfl rfl) rfl) (Ns528p495 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 7131209 8388608) (BSN.cos_neg_of_bound 7131209 8388608 Bool.false 22142678 33554432 1 9000000 (Ns528p516 rfl rfl)) rfl rfl) 

noncomputable def Ns528p518 := @Ns528p481 1685499759498743878757 Ns528p389 (Ns528p482 qz33 (@Enclosure.Real.IsNear.of_eq qz63 (@Inv.inv Real Real.instInv (Real.sqrt qz72)) Bool.false 1206823 4194304 1 33554432 (BSN.rpow_neg_quarter_mk qz71 (BSN.t_div_two_pi_nonneg qz62 916738 1000 qz65)) Ns528p486) rfl) (@Ns528p487 1125899906842624 2594084985521813 316659348799488000000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 916738 1000 12 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 916738 1000 12 qz65 rfl rfl rfl))) (@Ns528p488 67108864 11071339 16777216 41126701 9437184000000 845092986798383 1125899906842624 2594084985521813 316659348799488000000 (@Ns528p489 67108864 (Ns528p501 rfl rfl rfl rfl rfl) rfl) (Ns528p517 rfl) rfl)) 

noncomputable def Ns528p519 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 11358269322817122722857 4722366482869645213696 743465301978112708678757 Ns528p389 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz63) (Zeta.RiemannSiegel.correction qz64))) Bool.true 11358269322817122722857 4722366482869645213696 743465301978112708678757 Ns528p389 (BSN.hardyZApproximantRS₀_eq qz62 12 (@BSN.floor_sqrt_eq_dec qz62 916738 1000 12 qz65 rfl rfl rfl)) (@Ns528p391 11358269322817122722857 4722366482869645213696 743465301978112708678757 Ns528p389 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12)) Bool.true 73458691 33554432 140551 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (Ns528p480 (Ns528p479 rfl rfl rfl rfl) rfl rfl)) (Ns528p518 rfl) rfl rfl)) 

theorem RS529to540.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 11358269322817122722857 4722366482869645213696 743465301978112708678757 Ns528p389 := Ns528p519 

noncomputable def Ns528p520 := nat_lit 590295810358705651712000000 

noncomputable def Ns528p521 := nat_lit 2772278010729631362213159632896 

noncomputable abbrev qz730 := (Enclosure.sfrac Bool.false 917999 1000)

noncomputable abbrev qz614 := qz730

noncomputable abbrev qz420 := qz614

noncomputable abbrev qz80 := qz420

noncomputable abbrev qz731 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 917999 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz615 := qz731

noncomputable abbrev qz421 := qz615

noncomputable abbrev qz81 := (@HPow.hPow Real Real Real qz356 qz421 qz358)

noncomputable abbrev qz732 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 917999 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz616 := qz732

noncomputable abbrev qz422 := qz616

noncomputable abbrev qz82 := qz422

noncomputable def Ns528p522 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz81) (Zeta.RiemannSiegel.correction qz82)) 50868195 67108864 140745 134217728 15962334499710872691341 75557863725914323419136 1438913055444664346971 Ns528p520 Ns528p521 

noncomputable def Ns528p523 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos BSN.quadSignPos 11 12 917999 1000 288 536870912 268435456 9007199254740992 Bool.false 981618996061 4481 1334074092 61 154981288 8 

noncomputable def Ns528p524 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 917999 1000 181 237 536870912 268435456 9007199254740992 Bool.false 981618996061 4481 

noncomputable def Ns528p525 := Ns528p524 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.false 293324692 226641 Bool.true 563076323 Bool.true 310777540 28296951008113761 1 Bool.false 465376451 Bool.true Bool.false 293709696 Bool.true Bool.false 57602928 

noncomputable def Ns528p526 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 917999 1000 51 120 536870912 268435456 9007199254740992 Bool.false 981618996061 4481 

noncomputable def Ns528p527 := Ns528p526 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.false 41185057 185079 Bool.true 218388432 Bool.true 78661793 28296951008113761 1 Bool.false 212415272 Bool.false Bool.false 531118490 Bool.false Bool.false 293324692 

noncomputable def Ns528p528 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 917999 1000 116 26 536870912 268435456 9007199254740992 Bool.false 981618996061 4481 

noncomputable def Ns528p529 := Ns528p528 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.false 64817947 137510 Bool.false 731271352 Bool.false 656921855 28296951008113761 1 Bool.false 111231939 Bool.false Bool.false 182670970 Bool.true Bool.false 41185057 

noncomputable def Ns528p530 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 917999 1000 353 223 536870912 268435456 9007199254740992 Bool.false 981618996061 4481 

noncomputable def Ns528p531 := Ns528p530 744261104 60 268435448 8 864060384 60 240095976 8 Bool.false 176656341 81073 Bool.false 697902494 Bool.false 353214602 28296951008113761 1 Bool.false 517298418 Bool.true Bool.false 328278938 Bool.false Bool.false 64817947 

noncomputable def Ns528p532 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 917999 1000 758 521 536870912 268435456 9007199254740992 Bool.false 981618996061 4481 

noncomputable def Ns528p533 := Ns528p532 372130544 60 379625064 8 589812976 60 309962568 8 Bool.false 536870672 4548 Bool.false 770867547 Bool.false 804233652 28296951008113761 1 Bool.false 72227634 Bool.true Bool.false 535449093 Bool.true Bool.false 176656341 

noncomputable def Ns528p534 := nat_lit 177414450477578481634242795829488333804127637809355696525249 

noncomputable def Ns528p535 := nat_lit 97032207212809272226323306801571669115227681226489856000 

noncomputable def Ns528p536 := nat_lit 312933894013776633155742699199520000 

noncomputable def Ns528p537 := nat_lit 1723638249245760651474826850943096962880 

noncomputable abbrev qz617 := (@Eq.refl Real qz730)

noncomputable abbrev qz423 := qz617

noncomputable abbrev qz83 := qz423

noncomputable def Ns528p538 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 917999 1000 3370889656004 16000000 1835998 4000 2000 Ns528p536 Ns528p537 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p539 := nat_lit 56772624152825114122957694665436266817320844098993822888079680 

noncomputable abbrev qz618 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1835998))))

noncomputable abbrev qz424 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 917999 4000) (Real.log (Enclosure.sfrac Bool.false 3370889656004 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz618))

noncomputable abbrev qz619 := (Enclosure.sfrac Bool.false 917999 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz424 qz619) (@HMul.hMul Real Real Real qz355 qz619 (Real.log Real.pi)))

noncomputable def Ns528p540 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns528p536 Ns528p537) 32937671123847405696361 18014398509481984000 1230519930749029937 147456000000000000000000 Ns528p536 Ns528p537 0 1 Ns528p539 

noncomputable def Ns528p541 := nat_lit 442081938385400541125983128780800 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz361 qz424 qz619)

noncomputable def Ns528p542 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz619 (Real.log Real.pi)) 8480596905108646408469 3602879701896396800 115750015458347 36000000000000000000 35261040187239 67108864000 2753997 536870912000 Ns528p541 32937671123847405696361 18014398509481984000 

noncomputable def Ns528p543 := nat_lit 84805969051086464084690000 

noncomputable abbrev qz86 := qz424

noncomputable def Ns528p544 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz619 50671584434196207957353 18014398509481984000 115750015458347 36000000000000000000 917999 2000 0 1 Ns528p543 8480596905108646408469 3602879701896396800 115750015458347 36000000000000000000 

noncomputable def Ns528p545 := nat_lit 114102264388059333774040680485349228544 

noncomputable def Ns528p546 := nat_lit 118553054560159771190624256 

noncomputable def Ns528p547 := nat_lit 96549408792809658590442462723196794592783164616381623450499776665605278726053027731103963269668895859446379653092525953490361834273631412930650647342255964160 

noncomputable def Ns528p548 := nat_lit 1805479991681339871794892591604650974191929125857491893916170694489914611852072955363116403805663962157186543392169688349365305657299025642522863155179159552 

noncomputable def Ns528p549 := nat_lit 189576435091710412640954345660416652420709972696145423798420214404552449289740779646055209490322659837655699039165928373469230841507285940752948920320 

noncomputable def Ns528p550 := BSN.log_dyadic_bound 1273737656004 5468041656004 7 6 Ns528p547 268435456 72000000 Ns528p548 Ns528p549 127398519 6741779312008 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1273737656004) (BSN.artanhQ 5468041656004) 0 6 Ns528p548 Ns528p547 Ns528p549 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz425 := (Real.log (Enclosure.sfrac Bool.false 3370889656004 16000000))

noncomputable def Ns528p551 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 917999 4000) qz425 917999 4000 0 1 55205568000748647 4503599627370496 125000153 9000000000000000 50678656219119257197353 18014398509481984000 114750015453847 36000000000000000000 (Enclosure.Real.IsNear.const Bool.false 917999 4000) (BSN.isNear_log_sfrac 3370889656004 16000000 55205568000748647 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3370889656004) qz364)) Bool.false Ns528p546 Ns528p113 1000001224000000 72000000000000000000000 55205568000748647 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3370889656004 16000000 17 6741779312008 4194304000000 127398519 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p550 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p552 := BSN.arctan_dyadic_bound_f 1000 1835998 1 0 33554432 9000000 0 1 1 0 1 1 18275 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1835998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1835998) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz426 := (@Nat.cast Real Real.instNatCast 1835998)

noncomputable def Ns528p553 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 qz426)) 884279719003555 562949953421312 1 2000000000000000 18275 33554432 1 9000000 29661215789885119528960 883973115381155 562949953421312 2000000009 18000000000000000 qz15 (Ns528p552 rfl) rfl rfl 

noncomputable abbrev qz427 := (@HMul.hMul Real Real Real qz577 qz582 qz618)

noncomputable abbrev qz87 := qz427

noncomputable abbrev qz428 := qz618

noncomputable abbrev qz88 := qz428

noncomputable def Ns528p554 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 917999 4000) qz425) qz87 50678656219119257197353 18014398509481984000 114750015453847 36000000000000000000 883973115381155 2251799813685248 2000000009 72000000000000000 Ns528p545 50671584434196207957353 18014398509481984000 115750015458347 36000000000000000000 (Ns528p551 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz88 1 4 0 1 883973115381155 562949953421312 2000000009 18000000000000000 883973115381155 2251799813685248 2000000009 72000000000000000 qz372 Ns528p553 rfl) 

noncomputable def Ns528p555 := @Ns528p540 Ns528p534 Ns528p535 1230519930749029937 147456000000000000000000 (@Ns528p542 1230519930749029937 147456000000000000000000 (Ns528p544 (Ns528p554 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 917999 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz619 (Real.log Real.pi) 917999 2000 0 1 38410761 33554432 3 268435456 35261040187239 67108864000 2753997 536870912000 (Enclosure.Real.IsNear.const Bool.false 917999 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p536 Ns528p537) 

noncomputable def Ns528p556 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns528p534 Ns528p535 1230519930749029937 147456000000000000000000 122702374507 67108864 561 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz373 qz84 (Enclosure.sfrac Bool.true Ns528p536 Ns528p537)) Bool.false Ns528p534 Ns528p535 1230519930749029937 147456000000000000000000 Ns528p538 (Ns528p555 rfl rfl)) 

noncomputable def Ns528p557 := BSN.cos_dyadic_bound_f 128781317 137438953472 1 0 67108864 18017579 0 1 1 0 1 1 67108834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 128781317) qz588 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 128781317) qz589 0 0 rfl) rfl rfl 

noncomputable def Ns528p558 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 122702374507) qz19) Bool.false 122702374507 67108864 561 67108864 Bool.false 67108834 67108864 1 9000000 (Ns528p556 rfl) (Enclosure.sfrac_false_div 122702374507 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 122702374507) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9062179616187874279424) qz374) 226375608064910080 72057594037927936 Bool.false 67108834 67108864 291 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q0 122702374507 67108864 226375608064910080 72057594037927936 291 9062179616187874279424 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108834 67108864 9062179616187874279424 Ns528p113 128781317 137438953472 18017579 18000000 (Ns528p557 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p559 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns528p534 Ns528p535 1230519930749029937 147456000000000000000000 981618996061 536870912 4481 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz373 qz84 (Enclosure.sfrac Bool.true Ns528p536 Ns528p537)) Bool.false Ns528p534 Ns528p535 1230519930749029937 147456000000000000000000 Ns528p538 (Ns528p555 rfl rfl)) 

noncomputable def Ns528p560 := Ns528p533 81073 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 758 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 72227634 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 521 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535449093 536870912) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 33554417 33554432 79939201 9437184000000 536870672 536870912 4548 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 33554417 33554432 79939201 9437184000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 67108834 67108864 5116108864 603979776000000 33554417 33554432 79939201 9437184000000 (Ns528p558 rfl rfl) rfl)) rfl) (Ns528p559 rfl) RS529to540.d7 

noncomputable def Ns528p561 := nat_lit 48764251315131418299280357095696015989125892917475659573885425074182512750811038589643771037025403634606095111121 

noncomputable def Ns528p562 := nat_lit 44030858232233081055739200450954452370425317052906756343027006868434151652368844519737653957441923655308241 

noncomputable def Ns528p563 := nat_lit 295338505926818557070557515337265519960188913570122880257335749894110519171894577972109264222409890566512035402705 

noncomputable def Ns528p564 := BSN.cos_dyadic_bound_f 770867547 536870912 4 3 536870912 268435456 Ns528p561 Ns528p145 Ns528p562 Ns528p563 Ns528p148 Ns528p562 72227634 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 770867547) qz20 0 3 Ns528p561 Ns528p145 Ns528p562 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 770867547) qz377 0 3 Ns528p563 Ns528p148 Ns528p562 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p565 := nat_lit 150075510865177677004052514312291910633507606516964692153861002612389238122270411293375715233079505691022035255296 

noncomputable def Ns528p566 := nat_lit 73212780153886970233324804524813407087177354783258737472639181295418022291296748014192942825003992530026496 

noncomputable def Ns528p567 := nat_lit 749606107777712046965152513559317230783450229158635146752828686987885564931820177623407687697450668310642982649856 

noncomputable def Ns528p568 := BSN.sin_dyadic_bound_f 804233652 536870912 4 3 536870912 268435456 Ns528p565 Ns528p135 Ns528p566 Ns528p567 Ns528p138 Ns528p566 535449093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 804233652) qz375 0 3 Ns528p565 Ns528p135 Ns528p566 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 804233652) qz376 0 3 Ns528p567 Ns528p138 Ns528p566 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p569 := nat_lit 85044660517336917561716898851347477425085397312087595916614417217317796409585422327299635939807686911293124775936 

noncomputable def Ns528p570 := nat_lit 13351713468782310086254062565939917632771994997649930011027560431267829834577924786798663629841223276302336 

noncomputable def Ns528p571 := nat_lit 424975255270446833191611537303201300045746322225481207730817947945064479693510185615468564636080174182080295735296 

noncomputable def Ns528p572 := BSN.sin_dyadic_bound_f 697902494 536870912 4 3 536870912 268435456 Ns528p569 Ns528p135 Ns528p570 Ns528p571 Ns528p138 Ns528p570 517298418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 697902494) qz375 0 3 Ns528p569 Ns528p135 Ns528p570 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 697902494) qz376 0 3 Ns528p571 Ns528p138 Ns528p570 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p573 := nat_lit 3910594520049776038401607455289477972115469677207674064048845263356289280 

noncomputable def Ns528p574 := nat_lit 242275329643316214767929651674548691954473595791871479751919866470656 

noncomputable def Ns528p575 := nat_lit 10241641011501419493370776211084016848134494292579292852017853533768376576 

noncomputable def Ns528p576 := BSN.sin_dyadic_bound_f 353214602 536870912 3 2 536870912 268435456 Ns528p573 Ns528p180 Ns528p574 Ns528p575 Ns528p183 Ns528p574 328278938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 353214602) qz375 0 2 Ns528p573 Ns528p180 Ns528p574 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 353214602) qz376 0 2 Ns528p575 Ns528p183 Ns528p574 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p577 := Ns528p531 137510 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 353 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 517298418 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 223 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 328278938 536870912) qz83 rfl rfl (Ns528p560 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p564 rfl rfl) (Ns528p568 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p559 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p572 rfl rfl) (Ns528p576 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p578 := nat_lit 39471909733177290810959219678599150542825570949284413852355092197237245466924343822272677989289873310621867442176 

noncomputable def Ns528p579 := nat_lit 23385287853601792309746366976703302965573691914170913579759038432375608225270733105702722185846690672541696 

noncomputable def Ns528p580 := nat_lit 239136375653318686298322979782505587708135457061038371892989022013482281082947822800273908454200551481694790615040 

noncomputable def Ns528p581 := BSN.cos_dyadic_bound_f 731271352 536870912 4 3 536870912 268435456 Ns528p578 Ns528p145 Ns528p579 Ns528p580 Ns528p148 Ns528p579 111231939 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 731271352) qz20 0 3 Ns528p578 Ns528p145 Ns528p579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 731271352) qz377 0 3 Ns528p580 Ns528p148 Ns528p579 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p582 := nat_lit 25687318907101948287582263967963549418761968449570404200531130899874350655278795107695785144636181894262036890625 

noncomputable def Ns528p583 := nat_lit 6458988729928424811513535972215176216349477003391414665115144005618985030407546418500736470512168212890625 

noncomputable def Ns528p584 := nat_lit 155697927717937061755927737803643189294334770079356776929323295848761622773344878617513690155130240969967278490625 

noncomputable def Ns528p585 := BSN.cos_dyadic_bound_f 656921855 536870912 4 3 536870912 268435456 Ns528p582 Ns528p145 Ns528p583 Ns528p584 Ns528p148 Ns528p583 182670970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 656921855) qz20 0 3 Ns528p582 Ns528p145 Ns528p583 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 656921855) qz377 0 3 Ns528p584 Ns528p148 Ns528p583 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p586 := Ns528p529 185079 BSN.abs_quadSignPos (BSN.cos_quad_nat0 116 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111231939 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 26 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 182670970 536870912) qz83 rfl rfl (Ns528p577 rfl rfl) (Ns528p559 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p581 rfl rfl) (Ns528p585 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p587 := nat_lit 2274670632033380580903315534053376 

noncomputable def Ns528p588 := BSN.sin_dyadic_bound_f 218388432 536870912 2 1 536870912 268435456 Ns528p587 Ns528p160 Ns528p587 Ns528p587 Ns528p161 Ns528p587 212415272 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 218388432) qz375 0 1 Ns528p587 Ns528p160 Ns528p587 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 218388432) qz376 0 1 Ns528p587 Ns528p161 Ns528p587 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p589 := nat_lit 38287355046508219121441876572801 

noncomputable def Ns528p590 := BSN.cos_dyadic_bound_f 78661793 536870912 2 1 536870912 268435456 Ns528p589 Ns528p141 Ns528p589 Ns528p589 Ns528p142 Ns528p589 531118490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 78661793) qz20 0 1 Ns528p589 Ns528p141 Ns528p589 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 78661793) qz377 0 1 Ns528p589 Ns528p142 Ns528p589 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p591 := Ns528p527 226641 BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 212415272 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 531118490 536870912) qz83 rfl rfl (Ns528p586 rfl) (Ns528p559 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p588 rfl rfl) (Ns528p590 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p592 := nat_lit 25264115008693914403826090848337546510114907647549673146145603460114118305 

noncomputable def Ns528p593 := nat_lit 10105042102897788212446959592370731373762239232261818276638777335314081 

noncomputable def Ns528p594 := nat_lit 66151559716507941305295800001544021580457714499111196248409641517946468001 

noncomputable def Ns528p595 := BSN.sin_dyadic_bound_f 563076323 536870912 3 2 536870912 268435456 Ns528p592 Ns528p180 Ns528p593 Ns528p594 Ns528p183 Ns528p593 465376451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 563076323) qz375 0 2 Ns528p592 Ns528p180 Ns528p593 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 563076323) qz376 0 2 Ns528p594 Ns528p183 Ns528p593 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p596 := nat_lit 2343559088716889401931193603216685676243740474192315808082329883811840000 

noncomputable def Ns528p597 := nat_lit 87015575571397450749971159369942721904737668846691205091353600000000 

noncomputable def Ns528p598 := nat_lit 6137751969040928075851911864642815911469569761896980092550239885107200000 

noncomputable def Ns528p599 := BSN.sin_dyadic_bound_f 310777540 536870912 3 2 536870912 268435456 Ns528p596 Ns528p180 Ns528p597 Ns528p598 Ns528p183 Ns528p597 293709696 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 310777540) qz375 0 2 Ns528p596 Ns528p180 Ns528p597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 310777540) qz376 0 2 Ns528p598 Ns528p183 Ns528p597 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p600 := Ns528p525 264021 BSN.abs_quadSignNeg qz601 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 465376451 536870912) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 293709696 536870912) qz83 rfl rfl (Ns528p591 rfl) (Ns528p559 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p595 rfl rfl) (Ns528p599 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p601 := nat_lit 163512541051067905873147952927631403207506091972843717613838005030903361 

noncomputable def Ns528p602 := nat_lit 1372515592577222089731275092031955293622891890795078274932469423681 

noncomputable def Ns528p603 := nat_lit 490534878122018563175264396232710145711931030134749562684964150153862721 

noncomputable def Ns528p604 := BSN.cos_dyadic_bound_f 185007639 536870912 3 2 536870912 268435456 Ns528p601 Ns528p165 Ns528p602 Ns528p603 Ns528p168 Ns528p602 505307973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 185007639) qz20 0 2 Ns528p601 Ns528p165 Ns528p602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 185007639) qz377 0 2 Ns528p603 Ns528p168 Ns528p602 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p605 := Ns528p523 Bool.false 57602928 264021 Bool.true 185007639 28296951008113761 1 Bool.false 505307973 Bool.false Bool.false 203472780 281490 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 505307973 536870912) qz83 rfl (Ns528p600 rfl) (Ns528p559 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p604 rfl rfl) rfl 

noncomputable def Ns528p606 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) 203472780 536870912 281490 536870912 203472780 536870912 281490 536870912 218477233931550720 50868195 67108864 140745 134217728 (Ns528p605 rfl rfl rfl rfl) 

noncomputable def Ns528p607 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz81) (Zeta.RiemannSiegel.correction qz82) 19302533 67108864 1 67108864 826955431171177 1125899906842624 2671581295025359 316659348799488000000 15962334499710872691341 75557863725914323419136 

noncomputable def Ns528p608 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz81 1 1 0 1 19302533 67108864 1 67108864 19302533 67108864 1 67108864 

noncomputable abbrev qz89 := qz421

noncomputable def Ns528p609 := @Enclosure.Real.IsNear.sqrt_image qz89 9804878345293 67108864000 917999 67108864000 405584203 405584242 33554432 (@Enclosure.Real.IsNear.of_eq qz89 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 9804878345293 67108864000 917999 67108864000 (BSN.t_div_two_pi_mk qz80 917999 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 917999 1000 0 1 10680707 67108864 1 67108864 9804878345293 67108864000 917999 67108864000 (Enclosure.Real.IsNear.const Bool.false 917999 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz733 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 917999 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz620 := qz733

noncomputable abbrev qz429 := qz620

noncomputable abbrev qz90 := qz429

noncomputable def Ns528p610 := @Enclosure.Real.IsNear.sqrt_image qz90 811168445 67108864 39 67108864 116658251 116658257 33554432 (@Enclosure.Real.IsNear.recentre' qz90 Bool.false 811168445 67108864 39 67108864 811168445 67108864 39 67108864 (Ns528p609 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p611 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz90) 58329127 16777216 3 33554432 9651266 9651267 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz90) Bool.false 233316508 67108864 6 67108864 58329127 16777216 3 33554432 (Ns528p610 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p612 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz90)) Bool.false 19302533 67108864 1 67108864 19302533 67108864 1 67108864 (Ns528p611 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz422))

noncomputable abbrev qz621 := (@HMul.hMul Real Real Real qz713 qz732 qz732)

noncomputable abbrev qz430 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz621 qz616) qz594)

noncomputable abbrev qz92 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz430))

noncomputable def Ns528p613 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz91) qz92) Bool.false 826955431171177 

noncomputable def Ns528p614 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz91) qz92 78662269 67108864 349 

noncomputable def Ns528p615 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz91) Bool.false 78662269 67108864 349 67108864 78662269 67108864 349 

noncomputable def Ns528p616 := @Enclosure.Real.IsNear.recentre' qz91 Bool.false 28626174 33554432 1140554432 301989888000000 14313087 16777216 17821163 4718592000000 

noncomputable abbrev qz93 := (@HMul.hMul Real Real Real qz355 qz352 qz422)

noncomputable abbrev qz622 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns528p617 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9208129) qz622) Bool.false 9208129 16777216 123 33554432 Bool.false 28626174 33554432 1 

noncomputable def Ns528p618 := nat_lit 1052456941003072630754857297 

noncomputable def Ns528p619 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 5862077 67108864 39 67108864 5183715802337202683735 9444732965739290427392 Ns528p618 

noncomputable def Ns528p620 := @Enclosure.Real.IsNear.subLit_ff_p qz90 qz1 811168445 67108864 39 67108864 12 1 0 1 5862077 5862077 67108864 39 

noncomputable def Ns528p621 := @Ns528p620 67108864 (@Enclosure.Real.IsNear.recentre' qz90 Bool.false 811168445 67108864 39 67108864 811168445 67108864 39 67108864 (Ns528p609 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p622 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 5183715802337202683735 9444732965739290427392 Ns528p618 Ns528p330 9208129 16777216 123 33554432 (@Ns528p619 Ns528p330 RS529to540.d55 (Ns528p621 rfl rfl) rfl) 

noncomputable def Ns528p623 := nat_lit 956969070980584770265307792140656593048027518029148915223041 

noncomputable def Ns528p624 := nat_lit 253092741970790968397859029543733109897246971520789871559966720 

noncomputable def Ns528p625 := nat_lit 51685790013439799223556823189584107186203965497340316161 

noncomputable def Ns528p626 := nat_lit 2870803841361727431197476262775590610929710146156452065036801 

noncomputable def Ns528p627 := nat_lit 11389173388685593577903656329467989945376113718435544220198502400 

noncomputable def Ns528p628 := BSN.cos_dyadic_bound_f 9208129 16777216 3 2 33554432 9000000 Ns528p623 Ns528p624 Ns528p625 Ns528p626 Ns528p627 Ns528p625 28626174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 9208129) (BSN.cosEvenQ 16777216) 0 2 Ns528p623 Ns528p624 Ns528p625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 9208129) (BSN.cosOddQ 16777216) 0 2 Ns528p626 Ns528p627 Ns528p625 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p629 := @Enclosure.Real.IsNear.inv_image qz91 14313087 16777216 17821163 4718592000000 39330960 39331309 33554432 (Ns528p616 (@Ns528p617 9000000 (Ns528p622 rfl) (Enclosure.sfrac_false_div 9208129 16777216) (Ns528p628 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p630 := @Enclosure.Real.IsNear.recentre' qz92 Bool.false 21025466 33554432 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz355 qz352 qz430)

noncomputable def Ns528p631 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 3748045)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true 3748045 4194304 

noncomputable def Ns528p632 := nat_lit 566388550926511830474416291525 

noncomputable def Ns528p633 := nat_lit 82968398021673159386009752056207601 

noncomputable def Ns528p634 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns528p632 Ns528p217 Ns528p633 

noncomputable abbrev qz95 := qz430

noncomputable def Ns528p635 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 640508358107255 

noncomputable abbrev qz431 := (@HSub.hSub Real Real Real qz581 qz621 qz616)

noncomputable abbrev qz96 := qz431

noncomputable def Ns528p636 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 359033381396599 4503599627370496 3074489223 4503599627370496 1 16 

noncomputable abbrev qz432 := qz621

noncomputable abbrev qz97 := qz432

noncomputable def Ns528p637 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 34363946753929 4503599627370496 457243527 4503599627370496 5862077 67108864 39 67108864 

noncomputable def Ns528p638 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 5862077 67108864 39 67108864 5862077 67108864 39 67108864 34363946753929 4503599627370496 

noncomputable def Ns528p639 := nat_lit 102643840192445671865215509781099674323036553415142190625 

noncomputable def Ns528p640 := nat_lit 3861888762982039923063034508418779142719222587902677483520 

noncomputable def Ns528p641 := nat_lit 38943804107221470710054070749682469673824697625390625 

noncomputable def Ns528p642 := nat_lit 307853632969122572654226421201799658029762010850175790625 

noncomputable def Ns528p643 := nat_lit 173784994334191796537836552878845061422365016455620486758400 

noncomputable def Ns528p644 := BSN.cos_dyadic_bound_f 3748045 4194304 3 2 33554432 9000000 Ns528p639 Ns528p640 Ns528p641 Ns528p642 Ns528p643 Ns528p641 21025466 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3748045) (BSN.cosEvenQ 4194304) 0 2 Ns528p639 Ns528p640 Ns528p641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3748045) (BSN.cosOddQ 4194304) 0 2 Ns528p642 Ns528p643 Ns528p641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p645 := @Ns528p630 2668108864 603979776000000 10512733 16777216 41689201 9437184000000 (@Ns528p631 289 67108864 Bool.false 21025466 33554432 1 9000000 (@Ns528p634 Ns528p220 3748045 4194304 289 67108864 (@Ns528p635 4503599627370496 3074489223 4503599627370496 Ns528p632 Ns528p217 Ns528p633 Ns528p220 RS529to540.d55 (@Ns528p636 0 1 10248133729716080 640508358107255 4503599627370496 3074489223 4503599627370496 (@Ns528p637 24094322363604492353536 359033381396599 4503599627370496 3074489223 4503599627370496 (@Ns528p638 457243527 4503599627370496 (Ns528p621 rfl rfl) (Ns528p621 rfl rfl) rfl) (Ns528p621 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 3748045 4194304) (BSN.cos_neg_of_bound 3748045 4194304 Bool.false 21025466 33554432 1 9000000 (Ns528p644 rfl rfl)) rfl rfl) 

noncomputable def Ns528p646 := @Ns528p607 1438913055444664346971 Ns528p520 (Ns528p608 qz33 (@Enclosure.Real.IsNear.of_eq qz81 (@Inv.inv Real Real.instInv (Real.sqrt qz90)) Bool.false 19302533 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz89 (BSN.t_div_two_pi_nonneg qz80 917999 1000 qz83)) Ns528p612) rfl) (@Ns528p613 1125899906842624 2671581295025359 316659348799488000000 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 917999 1000 12 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 917999 1000 12 qz83 rfl rfl rfl))) (@Ns528p614 67108864 10512733 16777216 41689201 9437184000000 826955431171177 1125899906842624 2671581295025359 316659348799488000000 (@Ns528p615 67108864 (Ns528p629 rfl rfl rfl rfl rfl) rfl) (Ns528p645 rfl) rfl)) 

noncomputable def Ns528p647 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 41310161512041559252339 75557863725914323419136 620441969260777144346971 Ns528p520 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz81) (Zeta.RiemannSiegel.correction qz82))) Bool.false 41310161512041559252339 75557863725914323419136 620441969260777144346971 Ns528p520 (BSN.hardyZApproximantRS₀_eq qz80 12 (@BSN.floor_sqrt_eq_dec qz80 917999 1000 12 qz83 rfl rfl rfl)) (@Ns528p522 41310161512041559252339 75557863725914323419136 620441969260777144346971 Ns528p520 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12)) Bool.false 50868195 67108864 140745 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (Ns528p606 (Ns528p605 rfl rfl rfl rfl) rfl rfl)) (Ns528p646 rfl) rfl rfl)) 

theorem RS529to540.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 41310161512041559252339 75557863725914323419136 620441969260777144346971 Ns528p520 := Ns528p647 

noncomputable def Ns528p648 := nat_lit 885443715538058477568000000 

noncomputable def Ns528p649 := nat_lit 768712570112106068839766163456 

noncomputable abbrev qz734 := (Enclosure.sfrac Bool.false 919259 1000)

noncomputable abbrev qz623 := qz734

noncomputable abbrev qz433 := qz623

noncomputable abbrev qz98 := qz433

noncomputable abbrev qz735 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 919259 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz624 := qz735

noncomputable abbrev qz434 := qz624

noncomputable abbrev qz99 := (@HPow.hPow Real Real Real qz356 qz434 qz358)

noncomputable abbrev qz736 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 919259 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz625 := qz736

noncomputable abbrev qz435 := qz625

noncomputable abbrev qz100 := qz435

noncomputable def Ns528p650 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz99) (Zeta.RiemannSiegel.correction qz100)) 25910073 268435456 140935 134217728 1952047830463553052015 9444732965739290427392 2232669879276005621539 Ns528p648 Ns528p649 

noncomputable def Ns528p651 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos BSN.quadSignPos 11 12 919259 1000 288 536870912 268435456 9007199254740992 Bool.false 983305067752 4487 1334074092 61 154981288 8 

noncomputable def Ns528p652 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 919259 1000 181 237 536870912 268435456 9007199254740992 Bool.false 983305067752 4487 

noncomputable def Ns528p653 := Ns528p652 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.false 22447871 226946 Bool.true 434605237 Bool.true 246779726 28296951008113761 1 Bool.false 388669261 Bool.true Bool.false 238180721 Bool.true Bool.true 172274333 

noncomputable def Ns528p654 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 919259 1000 50 119 536870912 268435456 9007199254740992 Bool.false 983305067752 4487 

noncomputable def Ns528p655 := Ns528p654 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.true 130446255 185327 Bool.true 782285109 Bool.true 722233653 28296951008113761 1 Bool.false 60898390 Bool.true Bool.false 523274886 Bool.false Bool.false 22447871 

noncomputable def Ns528p656 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 919259 1000 117 27 536870912 268435456 9007199254740992 Bool.false 983305067752 4487 

noncomputable def Ns528p657 := Ns528p656 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.true 61575368 137693 Bool.false 361979335 Bool.false 183353488 28296951008113761 1 Bool.false 335170152 Bool.true Bool.false 179809898 Bool.false Bool.true 130446255 

noncomputable def Ns528p658 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 919259 1000 354 224 536870912 268435456 9007199254740992 Bool.false 983305067752 4487 

noncomputable def Ns528p659 := Ns528p658 744261104 60 268435448 8 864060384 60 240095976 8 Bool.true 180661655 81178 Bool.false 602890337 Bool.false 107255353 28296951008113761 1 Bool.false 232468618 Bool.true Bool.false 526192832 Bool.false Bool.true 61575368 

noncomputable def Ns528p660 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 919259 1000 760 523 536870912 268435456 9007199254740992 Bool.false 983305067752 4487 

noncomputable def Ns528p661 := Ns528p660 372130544 60 379625064 8 589812976 60 309962568 8 Bool.true 536870904 4548 Bool.false 301425040 Bool.false 60511280 28296951008113761 1 Bool.false 454453240 Bool.false Bool.false 60383241 Bool.false Bool.true 180661655 

noncomputable def Ns528p662 := nat_lit 179187787474774387491296677601298985972488439041382992726941 

noncomputable def Ns528p663 := nat_lit 97834043610434152410978966750281130820568989613162496000 

noncomputable def Ns528p664 := nat_lit 315087384694583849738584822543520000 

noncomputable def Ns528p665 := nat_lit 1737881724935770798107962895611697910080 

noncomputable abbrev qz626 := (@Eq.refl Real qz734)

noncomputable abbrev qz436 := qz626

noncomputable abbrev qz101 := qz436

noncomputable def Ns528p666 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 919259 1000 3380149436324 16000000 1838518 4000 2000 Ns528p664 Ns528p665 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p667 := nat_lit 57340091991927803997214936832415675511196300493242557672621120 

noncomputable abbrev qz627 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1838518))))

noncomputable abbrev qz437 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 919259 4000) (Real.log (Enclosure.sfrac Bool.false 3380149436324 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz627))

noncomputable abbrev qz628 := (Enclosure.sfrac Bool.false 919259 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz437 qz628) (@HMul.hMul Real Real Real qz355 qz628 (Real.log Real.pi)))

noncomputable def Ns528p668 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns528p664 Ns528p665) 32994246297259792695389 18014398509481984000 1232203259546469317 147456000000000000000000 Ns528p664 Ns528p665 0 1 Ns528p667 

noncomputable def Ns528p669 := nat_lit 2214206387545311000663053828096000 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz361 qz437 qz628)

noncomputable def Ns528p670 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz628 (Real.log Real.pi)) 42472551319737489981533 18014398509481984000 115907515651127 36000000000000000000 35309437746099 67108864000 2757777 536870912000 Ns528p669 32994246297259792695389 18014398509481984000 

noncomputable def Ns528p671 := nat_lit 84945102639474979963066000 

noncomputable abbrev qz104 := qz437

noncomputable def Ns528p672 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz628 50752500299451439546461 18014398509481984000 115907515651127 36000000000000000000 919259 2000 0 1 Ns528p671 42472551319737489981533 18014398509481984000 115907515651127 36000000000000000000 

noncomputable def Ns528p673 := nat_lit 114284470718365244898500184658126307328 

noncomputable def Ns528p674 := nat_lit 118579585337622204820488192 

noncomputable def Ns528p675 := nat_lit 98529789543404052398381119679132064029656007416684348838485631796466691829113355090055780107783234243940612674978315053241848150478078394715254938717137141760 

noncomputable def Ns528p676 := nat_lit 1863794083447842560408186952330276008712656930312275456909325149191549983049144829964487454453774967097713349023990786793926669240189278317320663038030774272 

noncomputable def Ns528p677 := nat_lit 206792106179055068192749585974737952843516124884363242463282974786567008945763231458173493041903786146334160824867540995486052297419111376944124395520 

noncomputable def Ns528p678 := BSN.log_dyadic_bound 1282997436324 5477301436324 7 6 Ns528p675 268435456 72000000 Ns528p676 Ns528p677 128134896 6760298872648 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1282997436324) (BSN.artanhQ 5477301436324) 0 6 Ns528p676 Ns528p675 Ns528p677 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz438 := (Real.log (Enclosure.sfrac Bool.false 3380149436324 16000000))

noncomputable def Ns528p679 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 919259 4000) qz438 919259 4000 0 1 55217922356735079 4503599627370496 125000153 9000000000000000 50759572087729931986461 18014398509481984000 114907515646627 36000000000000000000 (Enclosure.Real.IsNear.const Bool.false 919259 4000) (BSN.isNear_log_sfrac 3380149436324 16000000 55217922356735079 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3380149436324) qz364)) Bool.false Ns528p674 Ns528p113 1000001224000000 72000000000000000000000 55217922356735079 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3380149436324 16000000 17 6760298872648 4194304000000 128134896 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p678 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p680 := BSN.arctan_dyadic_bound_f 1000 1838518 1 0 33554432 9000000 0 1 1 0 1 1 18250 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1838518) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1838518) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns528p681 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1838518))) 884279719003555 562949953421312 1 2000000000000000 18250 33554432 1 9000000 29661229863633955061760 883973534811555 562949953421312 2000000009 18000000000000000 qz15 (Ns528p680 rfl) rfl rfl 

noncomputable abbrev qz439 := (@HMul.hMul Real Real Real qz577 qz582 qz627)

noncomputable abbrev qz105 := qz439

noncomputable abbrev qz440 := qz627

noncomputable abbrev qz106 := qz440

noncomputable def Ns528p682 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 919259 4000) qz438) qz105 50759572087729931986461 18014398509481984000 114907515646627 36000000000000000000 883973534811555 2251799813685248 2000000009 72000000000000000 Ns528p673 50752500299451439546461 18014398509481984000 115907515651127 36000000000000000000 (Ns528p679 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz106 1 4 0 1 883973534811555 562949953421312 2000000009 18000000000000000 883973534811555 2251799813685248 2000000009 72000000000000000 qz372 Ns528p681 rfl) 

noncomputable def Ns528p683 := @Ns528p668 Ns528p662 Ns528p663 1232203259546469317 147456000000000000000000 (@Ns528p670 1232203259546469317 147456000000000000000000 (Ns528p672 (Ns528p682 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 919259 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz628 (Real.log Real.pi) 919259 2000 0 1 38410761 33554432 3 268435456 35309437746099 67108864000 2757777 536870912000 (Enclosure.Real.IsNear.const Bool.false 919259 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p664 Ns528p665) 

noncomputable def Ns528p684 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns528p662 Ns528p663 1232203259546469317 147456000000000000000000 122913133469 67108864 561 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz373 qz102 (Enclosure.sfrac Bool.true Ns528p664 Ns528p665)) Bool.false Ns528p662 Ns528p663 1232203259546469317 147456000000000000000000 Ns528p666 (Ns528p683 rfl rfl)) 

noncomputable def Ns528p685 := nat_lit 15190819732372994987655168 

noncomputable def Ns528p686 := nat_lit 14376625878238462702213509961830015208758192389394848294898176594379759710906325830341626356421564933145816346715182365651856688093723847405041 

noncomputable def Ns528p687 := nat_lit 282877490902138091004622673603363019119652456796264491099280832830873987773707601701812303598028785564314492868916806270538811366318583631052800 

noncomputable def Ns528p688 := nat_lit 10242758047937488249532341598511536585709871158630452187972315391890102606225234726669860591514260906004016691171919938498842633399021041 

noncomputable def Ns528p689 := nat_lit 71793828981830529491493546163447582900817257620233153333720413109541136107827600833169418824390240656658292794579683254322708509458477690236401 

noncomputable def Ns528p690 := nat_lit 9900712181574833185161793576117705669187835987869257188474829149080589572079766059563430625931007494751007250412088219468858397821150427086848000 

noncomputable def Ns528p691 := BSN.sin_dyadic_bound_f 215874532221 137438953472 4 3 67108864 18017579 Ns528p686 Ns528p687 Ns528p688 Ns528p689 Ns528p690 Ns528p688 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215874532221) (BSN.sinEvenQ 137438953472) 0 3 Ns528p686 Ns528p687 Ns528p688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215874532221) (BSN.sinOddQ 137438953472) 0 3 Ns528p689 Ns528p690 Ns528p688 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p692 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 122913133469) qz19) Bool.false 122913133469 67108864 561 67108864 Bool.true 67108863 67108864 1 9000000 (Ns528p684 rfl) (Enclosure.sfrac_false_div 122913133469 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 122913133469) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns528p685) qz374) 226375608064910080 72057594037927936 Bool.false 67108863 67108864 291 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q1 122913133469 67108864 226375608064910080 72057594037927936 291 Ns528p685 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108863 67108864 Ns528p685 Ns528p113 215874532221 137438953472 18017579 18000000 (Ns528p691 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p693 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns528p662 Ns528p663 1232203259546469317 147456000000000000000000 983305067752 536870912 4487 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz373 qz102 (Enclosure.sfrac Bool.true Ns528p664 Ns528p665)) Bool.false Ns528p662 Ns528p663 1232203259546469317 147456000000000000000000 Ns528p666 (Ns528p683 rfl rfl)) 

noncomputable def Ns528p694 := Ns528p661 81178 BSN.abs_quadSignPos (BSN.cos_quad_nat0 760 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 454453240 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 523 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 60383241 536870912) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 67108863 67108864 79939201 9437184000000 536870904 536870912 4548 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 67108863 67108864 79939201 9437184000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 67108863 67108864 5116108864 603979776000000 67108863 67108864 79939201 9437184000000 (Ns528p692 rfl rfl) rfl)) rfl) (Ns528p693 rfl) RS529to540.d7 

noncomputable def Ns528p695 := nat_lit 1152210354667601232059884443296672388191683578667712221903762279628800000 

noncomputable def Ns528p696 := nat_lit 68145097575435678953961238820407642201965582904323403782553600000000 

noncomputable def Ns528p697 := nat_lit 3456494773807652824821745407412376349290646804837328018903721731686400000 

noncomputable def Ns528p698 := BSN.cos_dyadic_bound_f 301425040 536870912 3 2 536870912 268435456 Ns528p695 Ns528p165 Ns528p696 Ns528p697 Ns528p168 Ns528p696 454453240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 301425040) qz20 0 2 Ns528p695 Ns528p165 Ns528p696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 301425040) qz377 0 2 Ns528p697 Ns528p168 Ns528p696 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p699 := nat_lit 13407424461233468084394434560000 

noncomputable def Ns528p700 := BSN.sin_dyadic_bound_f 60511280 536870912 2 1 536870912 268435456 Ns528p699 Ns528p160 Ns528p699 Ns528p699 Ns528p161 Ns528p699 60383241 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 60511280) qz375 0 1 Ns528p699 Ns528p160 Ns528p699 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 60511280) qz376 0 1 Ns528p699 Ns528p161 Ns528p699 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p701 := nat_lit 18215830261114393741140388813782497338407243048976685821351154080725554783485960976508622293426093140838960581761 

noncomputable def Ns528p702 := nat_lit 2306003051646160687434597568257672259056749921872337700403325168506781882061784838489781530551325879422081 

noncomputable def Ns528p703 := nat_lit 110439686066569308904556127816598415606072788625712427713112044061493033619672001839523408926788300690044288224385 

noncomputable def Ns528p704 := BSN.cos_dyadic_bound_f 602890337 536870912 4 3 536870912 268435456 Ns528p701 Ns528p145 Ns528p702 Ns528p703 Ns528p148 Ns528p702 232468618 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 602890337) qz20 0 3 Ns528p701 Ns528p145 Ns528p702 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 602890337) qz377 0 3 Ns528p703 Ns528p148 Ns528p702 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p705 := nat_lit 132335360954200452438789749942881 

noncomputable def Ns528p706 := BSN.cos_dyadic_bound_f 107255353 536870912 2 1 536870912 268435456 Ns528p705 Ns528p141 Ns528p705 Ns528p705 Ns528p142 Ns528p705 526192832 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 107255353) qz20 0 1 Ns528p705 Ns528p141 Ns528p705 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 107255353) qz377 0 1 Ns528p705 Ns528p142 Ns528p705 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p707 := Ns528p659 137693 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 354 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 232468618 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 224 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 526192832 536870912) qz101 rfl rfl (Ns528p694 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p698 rfl rfl) (Ns528p700 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p693 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p704 rfl rfl) (Ns528p706 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p708 := nat_lit 4313462967608529423432781274907976801183737977159270741907721822259730625 

noncomputable def Ns528p709 := nat_lit 294761136801934437316719031527294077563384427165980305201868687890625 

noncomputable def Ns528p710 := nat_lit 11296687682848469167520676270136514098403258746344583213073706508995090625 

noncomputable def Ns528p711 := BSN.sin_dyadic_bound_f 361979335 536870912 3 2 536870912 268435456 Ns528p708 Ns528p180 Ns528p709 Ns528p710 Ns528p183 Ns528p709 335170152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 361979335) qz375 0 2 Ns528p708 Ns528p180 Ns528p709 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 361979335) qz376 0 2 Ns528p710 Ns528p183 Ns528p709 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p712 := nat_lit 1130203647258472663241488544628736 

noncomputable def Ns528p713 := BSN.sin_dyadic_bound_f 183353488 536870912 2 1 536870912 268435456 Ns528p712 Ns528p160 Ns528p712 Ns528p712 Ns528p161 Ns528p712 179809898 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 183353488) qz375 0 1 Ns528p712 Ns528p160 Ns528p712 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 183353488) qz376 0 1 Ns528p712 Ns528p161 Ns528p712 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p714 := Ns528p657 185327 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 335170152 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 179809898 536870912) qz101 rfl rfl (Ns528p707 rfl rfl) (Ns528p693 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p711 rfl rfl) (Ns528p713 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p715 := nat_lit 51726036126604035994488797278153873145503263325055159434989253473128493438393337887121118678870602419890159810961 

noncomputable def Ns528p716 := nat_lit 52526777886764614736927279628386392960955797364346091259179868694573733124955465404901369557125788016507281 

noncomputable def Ns528p717 := nat_lit 313244498344337497918210507384958572654935526711008503278086360305612912878820916681304407261527163522790613776785 

noncomputable def Ns528p718 := BSN.cos_dyadic_bound_f 782285109 536870912 4 3 536870912 268435456 Ns528p715 Ns528p145 Ns528p716 Ns528p717 Ns528p148 Ns528p716 60898390 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 782285109) qz20 0 3 Ns528p715 Ns528p145 Ns528p716 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 782285109) qz377 0 3 Ns528p717 Ns528p148 Ns528p716 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p719 := nat_lit 97552666901647135019275225503139107712125017169994779429040709591901578270614779141254585134798666444245664676241 

noncomputable def Ns528p720 := nat_lit 20143394112458301300826722128762215715953734957996346153011162889248000533153993634436899900818780475505041 

noncomputable def Ns528p721 := nat_lit 487437038294557451958821329464853211767567784616359785953949285808743938660246955519388492267339069642528317389201 

noncomputable def Ns528p722 := BSN.sin_dyadic_bound_f 722233653 536870912 4 3 536870912 268435456 Ns528p719 Ns528p135 Ns528p720 Ns528p721 Ns528p138 Ns528p720 523274886 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 722233653) qz375 0 3 Ns528p719 Ns528p135 Ns528p720 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 722233653) qz376 0 3 Ns528p721 Ns528p138 Ns528p720 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p723 := Ns528p655 226946 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 60898390 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 523274886 536870912) qz101 rfl rfl (Ns528p714 rfl) (Ns528p693 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p718 rfl rfl) (Ns528p722 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p724 := nat_lit 8964019129495340650021757006491660440821137406984913387424025972990339425 

noncomputable def Ns528p725 := nat_lit 1272798462929406842140259477434020881322973899897754305907024980666721 

noncomputable def Ns528p726 := nat_lit 23475132236881149329455422215943265120723694108170176793424789984053619041 

noncomputable def Ns528p727 := BSN.sin_dyadic_bound_f 434605237 536870912 3 2 536870912 268435456 Ns528p724 Ns528p180 Ns528p725 Ns528p726 Ns528p183 Ns528p725 388669261 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 434605237) qz375 0 2 Ns528p724 Ns528p180 Ns528p725 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 434605237) qz376 0 2 Ns528p726 Ns528p183 Ns528p725 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p728 := nat_lit 931763311818482931272516165025334937589868249332968018670040935034896640 

noncomputable def Ns528p729 := nat_lit 13755482273657037116904507177751905721610919373522419855560888402176 

noncomputable def Ns528p730 := nat_lit 2440310212553297946701257824911875142983248521050216250694150588414935296 

noncomputable def Ns528p731 := BSN.sin_dyadic_bound_f 246779726 536870912 3 2 536870912 268435456 Ns528p728 Ns528p180 Ns528p729 Ns528p730 Ns528p183 Ns528p729 238180721 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 246779726) qz375 0 2 Ns528p728 Ns528p180 Ns528p729 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 246779726) qz376 0 2 Ns528p730 Ns528p183 Ns528p729 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p732 := Ns528p653 264377 BSN.abs_quadSignNeg qz601 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 388669261 536870912) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 238180721 536870912) qz101 rfl rfl (Ns528p723 rfl) (Ns528p693 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p727 rfl rfl) (Ns528p731 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p733 := nat_lit 146089920403457678229806690954403619343620524059250181624263999295062016 

noncomputable def Ns528p734 := nat_lit 1095611124635700541571774472601428223231333908390846603601050075136 

noncomputable def Ns528p735 := nat_lit 438267569988123763288336929314265655174415109509933763179584795785035776 

noncomputable def Ns528p736 := BSN.cos_dyadic_bound_f 179869304 536870912 3 2 536870912 268435456 Ns528p733 Ns528p165 Ns528p734 Ns528p735 Ns528p168 Ns528p734 507020654 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 179869304) qz20 0 2 Ns528p733 Ns528p165 Ns528p734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 179869304) qz377 0 2 Ns528p735 Ns528p168 Ns528p734 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p737 := Ns528p651 Bool.true 172274333 264377 Bool.true 179869304 28296951008113761 1 Bool.false 507020654 Bool.false Bool.true 25910073 281870 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 507020654 536870912) qz101 rfl (Ns528p732 rfl) (Ns528p693 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p736 rfl rfl) rfl 

noncomputable def Ns528p738 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) 25910073 536870912 281870 536870912 25910073 536870912 281870 536870912 27820729042993152 25910073 268435456 140935 134217728 (Ns528p737 rfl rfl rfl rfl) 

noncomputable def Ns528p739 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz99) (Zeta.RiemannSiegel.correction qz100) 19295915 67108864 1 67108864 101163786763341 140737488355328 1382584236540173 158329674399744000000 1952047830463553052015 9444732965739290427392 

noncomputable def Ns528p740 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz99 1 1 0 1 19295915 67108864 1 67108864 19295915 67108864 1 67108864 

noncomputable abbrev qz107 := qz434

noncomputable def Ns528p741 := @Enclosure.Real.IsNear.sqrt_image qz107 9818336036113 67108864000 919259 67108864000 405862450 405862489 33554432 (@Enclosure.Real.IsNear.of_eq qz107 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 9818336036113 67108864000 919259 67108864000 (BSN.t_div_two_pi_mk qz98 919259 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 919259 1000 0 1 10680707 67108864 1 67108864 9818336036113 67108864000 919259 67108864000 (Enclosure.Real.IsNear.const Bool.false 919259 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz737 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 919259 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz629 := qz737

noncomputable abbrev qz441 := qz629

noncomputable abbrev qz108 := qz441

noncomputable def Ns528p742 := @Enclosure.Real.IsNear.sqrt_image qz108 811724939 67108864 39 67108864 116698260 116698267 33554432 (@Enclosure.Real.IsNear.recentre' qz108 Bool.false 811724939 67108864 39 67108864 811724939 67108864 39 67108864 (Ns528p741 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p743 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz108) 233396527 67108864 7 67108864 9647957 9647958 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz108) Bool.false 233396527 67108864 7 67108864 233396527 67108864 7 67108864 (Ns528p742 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p744 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz108)) Bool.false 19295915 67108864 1 67108864 19295915 67108864 1 67108864 (Ns528p743 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz435))

noncomputable abbrev qz630 := (@HMul.hMul Real Real Real qz713 qz736 qz736)

noncomputable abbrev qz442 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz630 qz625) qz594)

noncomputable abbrev qz110 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz442))

noncomputable def Ns528p745 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz109) qz110) Bool.false 101163786763341 

noncomputable def Ns528p746 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz109) qz110 40681959 33554432 187 

noncomputable def Ns528p747 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz109) Bool.false 81363918 67108864 374 67108864 40681959 33554432 187 

noncomputable def Ns528p748 := @Enclosure.Real.IsNear.recentre' qz109 Bool.false 27675656 33554432 1140554432 301989888000000 3459457 4194304 17821163 4718592000000 

noncomputable abbrev qz111 := (@HMul.hMul Real Real Real qz355 qz352 qz435)

noncomputable def Ns528p749 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 40329071) qz19) Bool.false 40329071 67108864 123 33554432 Bool.false 27675656 33554432 1 

noncomputable def Ns528p750 := nat_lit 210491388201570575563139549 

noncomputable def Ns528p751 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 6418571 67108864 39 67108864 5675812160284367019905 9444732965739290427392 Ns528p750 

noncomputable def Ns528p752 := @Enclosure.Real.IsNear.subLit_ff_p qz108 qz1 811724939 67108864 39 67108864 12 1 0 1 6418571 6418571 67108864 39 

noncomputable def Ns528p753 := @Ns528p752 67108864 (@Enclosure.Real.IsNear.recentre' qz108 Bool.false 811724939 67108864 39 67108864 811724939 67108864 39 67108864 (Ns528p741 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p754 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 5675812160284367019905 9444732965739290427392 Ns528p750 Ns528p204 40329071 67108864 123 33554432 (@Ns528p751 Ns528p204 RS529to540.d55 (Ns528p753 rfl rfl) rfl) 

noncomputable def Ns528p755 := nat_lit 90143707607057231239938350578337446934903897781929724523384103041 

noncomputable def Ns528p756 := nat_lit 6997545700340217190295462250180331802882790324388442444357761 

noncomputable def Ns528p757 := nat_lit 270417127729771013285434460810511980141105927765140396685263593601 

noncomputable def Ns528p758 := BSN.cos_dyadic_bound_f 40329071 67108864 3 2 33554432 9000000 Ns528p755 Ns528p226 Ns528p756 Ns528p757 Ns528p229 Ns528p756 27675656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 40329071) qz383 0 2 Ns528p755 Ns528p226 Ns528p756 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 40329071) (BSN.cosOddQ 67108864) 0 2 Ns528p757 Ns528p229 Ns528p756 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p759 := @Enclosure.Real.IsNear.inv_image qz109 3459457 4194304 17821163 4718592000000 40681772 40682146 33554432 (Ns528p748 (@Ns528p749 9000000 (Ns528p754 rfl) (Enclosure.sfrac_false_div 40329071 67108864) (Ns528p758 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p760 := @Enclosure.Real.IsNear.recentre' qz110 Bool.false 19893592 33554432 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz355 qz352 qz442)

noncomputable def Ns528p761 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15706355)) qz622) Bool.true 15706355 16777216 

noncomputable def Ns528p762 := nat_lit 593369316332852273285441664245 

noncomputable def Ns528p763 := nat_lit 84139769967732335252854123612180813 

noncomputable def Ns528p764 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns528p762 Ns528p217 Ns528p763 

noncomputable abbrev qz113 := qz442

noncomputable def Ns528p765 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 671019931341959 

noncomputable abbrev qz443 := (@HSub.hSub Real Real Real qz581 qz630 qz625)

noncomputable abbrev qz114 := qz443

noncomputable def Ns528p766 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 389544954631303 4503599627370496 3117895755 4503599627370496 1 16 

noncomputable abbrev qz444 := qz630

noncomputable abbrev qz115 := qz444

noncomputable def Ns528p767 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 41198053682041 4503599627370496 500650059 4503599627370496 6418571 67108864 39 67108864 

noncomputable def Ns528p768 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 6418571 67108864 39 67108864 6418571 67108864 39 67108864 41198053682041 4503599627370496 

noncomputable def Ns528p769 := nat_lit 8103805700217687770690690621269667722536852361140859022190625 

noncomputable def Ns528p770 := nat_lit 3703422615345980402821754291774549974780249634546625390625 

noncomputable def Ns528p771 := nat_lit 24304010255422371351266428355225454067660996584153483815790625 

noncomputable def Ns528p772 := BSN.cos_dyadic_bound_f 15706355 16777216 3 2 33554432 9000000 Ns528p769 Ns528p624 Ns528p770 Ns528p771 Ns528p627 Ns528p770 19893592 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 15706355) (BSN.cosEvenQ 16777216) 0 2 Ns528p769 Ns528p624 Ns528p770 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 15706355) (BSN.cosOddQ 16777216) 0 2 Ns528p771 Ns528p627 Ns528p770 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p773 := @Ns528p760 2704108864 603979776000000 2486699 4194304 42251701 9437184000000 (@Ns528p761 293 67108864 Bool.false 19893592 33554432 1 9000000 (@Ns528p764 Ns528p220 15706355 16777216 293 67108864 (@Ns528p765 4503599627370496 3117895755 4503599627370496 Ns528p762 Ns528p217 Ns528p763 Ns528p220 RS529to540.d55 (@Ns528p766 0 1 10736318901471344 671019931341959 4503599627370496 3117895755 4503599627370496 (@Ns528p767 26141919382238283169792 389544954631303 4503599627370496 3117895755 4503599627370496 (@Ns528p768 500650059 4503599627370496 (Ns528p753 rfl rfl) (Ns528p753 rfl rfl) rfl) (Ns528p753 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 15706355 16777216) (BSN.cos_neg_of_bound 15706355 16777216 Bool.false 19893592 33554432 1 9000000 (Ns528p772 rfl rfl)) rfl rfl) 

noncomputable def Ns528p774 := @Ns528p739 2232669879276005621539 Ns528p648 (Ns528p740 qz33 (@Enclosure.Real.IsNear.of_eq qz99 (@Inv.inv Real Real.instInv (Real.sqrt qz108)) Bool.false 19295915 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz107 (BSN.t_div_two_pi_nonneg qz98 919259 1000 qz101)) Ns528p744) rfl) (@Ns528p745 140737488355328 1382584236540173 158329674399744000000 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 919259 1000 12 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 919259 1000 12 qz101 rfl rfl rfl))) (@Ns528p746 33554432 2486699 4194304 42251701 9437184000000 101163786763341 140737488355328 1382584236540173 158329674399744000000 (@Ns528p747 33554432 (Ns528p759 rfl rfl rfl rfl rfl) rfl) (Ns528p773 rfl) rfl)) 

noncomputable def Ns528p775 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 2863677479744352656751 9444732965739290427392 931990697442939365621539 Ns528p648 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz99) (Zeta.RiemannSiegel.correction qz100))) Bool.true 2863677479744352656751 9444732965739290427392 931990697442939365621539 Ns528p648 (BSN.hardyZApproximantRS₀_eq qz98 12 (@BSN.floor_sqrt_eq_dec qz98 919259 1000 12 qz101 rfl rfl rfl)) (@Ns528p650 2863677479744352656751 9444732965739290427392 931990697442939365621539 Ns528p648 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12)) Bool.true 25910073 268435456 140935 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (Ns528p738 (Ns528p737 rfl rfl rfl rfl) rfl rfl)) (Ns528p774 rfl) rfl rfl)) 

theorem RS529to540.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 2863677479744352656751 9444732965739290427392 931990697442939365621539 Ns528p648 := Ns528p775 

noncomputable def Ns528p776 := nat_lit 1493425949052444288698281 

noncomputable def Ns528p777 := nat_lit 1416709944860893564108800000 

noncomputable def Ns528p778 := nat_lit 103986937844627294312813903740928 

noncomputable abbrev qz738 := (Enclosure.sfrac Bool.false 920519 1000)

noncomputable abbrev qz631 := qz738

noncomputable abbrev qz445 := qz631

noncomputable abbrev qz116 := qz445

noncomputable abbrev qz739 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 920519 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz632 := qz739

noncomputable abbrev qz446 := qz632

noncomputable abbrev qz117 := (@HPow.hPow Real Real Real qz356 qz446 qz358)

noncomputable abbrev qz740 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 920519 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz633 := qz740

noncomputable abbrev qz447 := qz633

noncomputable abbrev qz118 := qz447

noncomputable def Ns528p779 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz117) (Zeta.RiemannSiegel.correction qz118)) 742412899 268435456 282269 268435456 30559776192079090467225 151115727451828646838272 3707320281066317498281 Ns528p777 Ns528p778 

noncomputable def Ns528p780 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos BSN.quadSignPos 11 12 920519 1000 288 536870912 268435456 9007199254740992 Bool.false 984991602875 4494 1334074092 61 154981288 8 

noncomputable def Ns528p781 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 920519 1000 181 237 536870912 268435456 9007199254740992 Bool.false 984991602875 4494 

noncomputable def Ns528p782 := Ns528p781 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.false 740968659 227269 Bool.true 305670718 Bool.true 182318480 28296951008113761 1 Bool.false 289421643 Bool.true Bool.false 178834332 Bool.true Bool.false 595524917 

noncomputable def Ns528p783 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 920519 1000 50 119 536870912 268435456 9007199254740992 Bool.false 984991602875 4494 

noncomputable def Ns528p784 := Ns528p783 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.false 705704189 185593 Bool.true 502403498 Bool.true 522027224 28296951008113761 1 Bool.false 318458408 Bool.true Bool.false 443569576 Bool.false Bool.false 740968659 

noncomputable def Ns528p785 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 5 6 7 920519 1000 117 27 536870912 268435456 9007199254740992 Bool.false 984991602875 4494 

noncomputable def Ns528p786 := Ns528p785 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.false 750787479 137893 Bool.false 836465607 Bool.false 553563409 28296951008113761 1 Bool.false 536827222 Bool.true Bool.false 460560489 Bool.false Bool.false 705704189 

noncomputable def Ns528p787 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 920519 1000 355 224 536870912 268435456 9007199254740992 Bool.false 984991602875 4494 

noncomputable def Ns528p788 := Ns528p787 744261104 60 268435448 8 864060384 60 240095976 8 Bool.false 471787181 81300 Bool.false 508341612 Bool.false 705074392 28296951008113761 1 Bool.false 435716397 Bool.false Bool.false 136717903 Bool.false Bool.false 750787479 

noncomputable def Ns528p789 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 920519 1000 761 524 536870912 268435456 9007199254740992 Bool.false 984991602875 4494 

noncomputable def Ns528p790 := Ns528p789 372130544 60 379625064 8 589812976 60 309962568 8 Bool.false 536870888 4564 Bool.false 675760821 Bool.false 160567197 28296951008113761 1 Bool.false 510936169 Bool.true Bool.false 513038164 Bool.false Bool.false 471787181 

noncomputable def Ns528p791 := nat_lit 180976362757127417309716142933235143328730892283721296064409 

noncomputable def Ns528p792 := nat_lit 98641394139985153786592825466946784367155863288283136000 

noncomputable def Ns528p793 := nat_lit 317252714688340272770702277727520000 

noncomputable def Ns528p794 := nat_lit 1752223151285384151282770401304609897280 

noncomputable abbrev qz634 := (@Eq.refl Real qz738)

noncomputable abbrev qz448 := qz634

noncomputable abbrev qz119 := qz448

noncomputable def Ns528p795 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 920519 1000 3389421917444 16000000 1841038 4000 2000 Ns528p793 Ns528p794 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p796 := nat_lit 57912436082280773539109165738635245865193885530790814740610880 

noncomputable abbrev qz635 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1841038))))

noncomputable abbrev qz449 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 920519 4000) (Real.log (Enclosure.sfrac Bool.false 3389421917444 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz635))

noncomputable abbrev qz636 := (Enclosure.sfrac Bool.false 920519 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz449 qz636) (@HMul.hMul Real Real Real qz355 qz636 (Real.log Real.pi)))

noncomputable def Ns528p797 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns528p793 Ns528p794) 33050837020909455543121 18014398509481984000 1233886588343908697 147456000000000000000000 Ns528p793 Ns528p794 0 1 Ns528p796 

noncomputable def Ns528p798 := nat_lit 88720165068895112334294132981760 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz361 qz449 qz636)

noncomputable def Ns528p799 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz636 (Real.log Real.pi)) 1701685346566760950777 720575940379279360 116065015843907 36000000000000000000 35357835304959 67108864000 2761557 536870912000 Ns528p798 33050837020909455543121 18014398509481984000 

noncomputable def Ns528p800 := nat_lit 85084267328338047538850000 

noncomputable abbrev qz122 := qz449

noncomputable def Ns528p801 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz636 50833431714943946984273 18014398509481984000 116065015843907 36000000000000000000 920519 2000 0 1 Ns528p800 1701685346566760950777 720575940379279360 116065015843907 36000000000000000000 

noncomputable def Ns528p802 := nat_lit 114466712064692556540469765124028104704 

noncomputable def Ns528p803 := nat_lit 118606079762028446315708416 

noncomputable def Ns528p804 := nat_lit 100550135657596249044095571523618528764966827633126321934749187020362158359192929556910121132145586679120819220628578780347784379809361454341307192468423311360 

noncomputable def Ns528p805 := nat_lit 1923821530346799659022244291995838619514232639608537268307780522427370479388450920859248753554770012583818900213625099987935836509234772909499846979739451392 

noncomputable def Ns528p806 := nat_lit 225456784365328570945705640262232252657425541379924851833830076881217912829923220567932771970816389815868556762324981118376529604970499283910100254720 

noncomputable def Ns528p807 := BSN.log_dyadic_bound 1292269917444 5486573917444 7 6 Ns528p804 268435456 72000000 Ns528p805 Ns528p806 128870264 6778843834888 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1292269917444) (BSN.artanhQ 5486573917444) 0 6 Ns528p805 Ns528p804 Ns528p806 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz450 := (Real.log (Enclosure.sfrac Bool.false 3389421917444 16000000))

noncomputable def Ns528p808 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 920519 4000) qz450 920519 4000 0 1 55230259784510567 4503599627370496 125000153 9000000000000000 50840503506577882624273 18014398509481984000 115065015839407 36000000000000000000 (Enclosure.Real.IsNear.const Bool.false 920519 4000) (BSN.isNear_log_sfrac 3389421917444 16000000 55230259784510567 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3389421917444) qz364)) Bool.false Ns528p803 Ns528p113 1000001224000000 72000000000000000000000 55230259784510567 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3389421917444 16000000 17 6778843834888 4194304000000 128870264 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p807 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p809 := BSN.arctan_dyadic_bound_f 1000 1841038 1 0 33554432 9000000 0 1 1 0 1 1 18225 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1841038) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1841038) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns528p810 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1841038))) 884279719003555 562949953421312 1 2000000000000000 18225 33554432 1 9000000 29661243937382790594560 883973954241955 562949953421312 2000000009 18000000000000000 qz15 (Ns528p809 rfl) rfl rfl 

noncomputable abbrev qz451 := (@HMul.hMul Real Real Real qz577 qz582 qz635)

noncomputable abbrev qz123 := qz451

noncomputable abbrev qz452 := qz635

noncomputable abbrev qz124 := qz452

noncomputable def Ns528p811 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 920519 4000) qz450) qz123 50840503506577882624273 18014398509481984000 115065015839407 36000000000000000000 883973954241955 2251799813685248 2000000009 72000000000000000 Ns528p802 50833431714943946984273 18014398509481984000 116065015843907 36000000000000000000 (Ns528p808 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz124 1 4 0 1 883973954241955 562949953421312 2000000009 18000000000000000 883973954241955 2251799813685248 2000000009 72000000000000000 qz372 Ns528p810 rfl) 

noncomputable def Ns528p812 := @Ns528p797 Ns528p791 Ns528p792 1233886588343908697 147456000000000000000000 (@Ns528p799 1233886588343908697 147456000000000000000000 (Ns528p801 (Ns528p811 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 920519 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz636 (Real.log Real.pi) 920519 2000 0 1 38410761 33554432 3 268435456 35357835304959 67108864000 2761557 536870912000 (Enclosure.Real.IsNear.const Bool.false 920519 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p793 Ns528p794) 

noncomputable def Ns528p813 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns528p791 Ns528p792 1233886588343908697 147456000000000000000000 123123950359 67108864 563 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz373 qz120 (Enclosure.sfrac Bool.true Ns528p793 Ns528p794)) Bool.false Ns528p791 Ns528p792 1233886588343908697 147456000000000000000000 Ns528p795 (Ns528p812 rfl rfl)) 

noncomputable def Ns528p814 := nat_lit 15189115695199306549035008 

noncomputable def Ns528p815 := nat_lit 14370163186268158246301706837206342237625434904136195947801079566138915323732197653333993792533597383912583276255424836232503303251394629206016 

noncomputable def Ns528p816 := nat_lit 10228978718193994164020827413443407566032120387900358211789029865663331645193339039241187228620168011670516690321773160506543227866710016 

noncomputable def Ns528p817 := nat_lit 71761595647402887325668197787315671682293270996478882458012487888113438100321288091647172886020269631034410358270462504696987903223797043429376 

noncomputable def Ns528p818 := BSN.sin_dyadic_bound_f 215850316396 137438953472 4 3 67108864 18017579 Ns528p815 Ns528p687 Ns528p816 Ns528p817 Ns528p690 Ns528p816 67108861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215850316396) (BSN.sinEvenQ 137438953472) 0 3 Ns528p815 Ns528p687 Ns528p816 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215850316396) (BSN.sinOddQ 137438953472) 0 3 Ns528p817 Ns528p690 Ns528p816 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p819 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123123950359) qz19) Bool.false 123123950359 67108864 563 67108864 Bool.false 67108861 67108864 1 9000000 (Ns528p813 rfl) (Enclosure.sfrac_false_div 123123950359 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123123950359) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns528p814) qz374) 226375608064910080 72057594037927936 Bool.false 67108861 67108864 291 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q3 123123950359 67108864 226375608064910080 72057594037927936 291 Ns528p814 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108861 67108864 Ns528p814 Ns528p113 215850316396 137438953472 18017579 18000000 (Ns528p818 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p820 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns528p791 Ns528p792 1233886588343908697 147456000000000000000000 984991602875 536870912 4494 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz373 qz120 (Enclosure.sfrac Bool.true Ns528p793 Ns528p794)) Bool.false Ns528p791 Ns528p792 1233886588343908697 147456000000000000000000 Ns528p795 (Ns528p812 rfl rfl)) 

noncomputable def Ns528p821 := Ns528p790 81300 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 761 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 510936169 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 524 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 513038164 536870912) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 67108861 67108864 80220451 9437184000000 536870888 536870912 4564 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 67108861 67108864 80220451 9437184000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 67108861 67108864 5134108864 603979776000000 67108861 67108864 80220451 9437184000000 (Ns528p819 rfl rfl) rfl)) rfl) (Ns528p820 rfl) RS529to540.d7 

noncomputable def Ns528p822 := nat_lit 74746436775508208735745763480349651404064634550992941872412693603115216428090868362787879530616854611262629143441 

noncomputable def Ns528p823 := nat_lit 9068095928283877501100288802251017429953192670272339144777661779135058994992167930192880089754967978468241 

noncomputable def Ns528p824 := nat_lit 373540533673144875677855206979116121792169876829797617724361459110708116460788495396292305345114240228015882560401 

noncomputable def Ns528p825 := BSN.sin_dyadic_bound_f 675760821 536870912 4 3 536870912 268435456 Ns528p822 Ns528p135 Ns528p823 Ns528p824 Ns528p138 Ns528p823 510936169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 675760821) qz375 0 3 Ns528p822 Ns528p135 Ns528p823 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 675760821) qz376 0 3 Ns528p824 Ns528p138 Ns528p823 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p826 := nat_lit 92772263140071340960510704335669691177622251721921798795585613510126241 

noncomputable def Ns528p827 := nat_lit 441829396975581989255129450066993494078715609149424214726058355361 

noncomputable def Ns528p828 := nat_lit 278315905761420071717553602748108939545878597734547097538327388413668001 

noncomputable def Ns528p829 := BSN.cos_dyadic_bound_f 160567197 536870912 3 2 536870912 268435456 Ns528p826 Ns528p165 Ns528p827 Ns528p828 Ns528p168 Ns528p827 513038164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 160567197) qz20 0 2 Ns528p826 Ns528p165 Ns528p827 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 160567197) qz377 0 2 Ns528p828 Ns528p168 Ns528p827 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p830 := nat_lit 16780285776887862364205532780832265114570778630571729248841475059576012800 

noncomputable def Ns528p831 := nat_lit 4459080310073886113020586488875802822033444522287529681222374848004096 

noncomputable def Ns528p832 := nat_lit 43941148047537615138260076333578704952640175598461301556053312739611836416 

noncomputable def Ns528p833 := BSN.sin_dyadic_bound_f 508341612 536870912 3 2 536870912 268435456 Ns528p830 Ns528p180 Ns528p831 Ns528p832 Ns528p183 Ns528p831 435716397 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 508341612) qz375 0 2 Ns528p830 Ns528p180 Ns528p831 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 508341612) qz376 0 2 Ns528p832 Ns528p183 Ns528p831 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p834 := nat_lit 34103033428669398498978407288098724997513602947644085906695572321223340892196529305203420865117089943585518780416 

noncomputable def Ns528p835 := nat_lit 15094519711769850876469687332545005720560133052345240097533674436179095396399172595460474007135440533979136 

noncomputable def Ns528p836 := nat_lit 206647859293962478386380798515867382907032466744733653139324029167830966504958872509998818129696801430166852075520 

noncomputable def Ns528p837 := BSN.cos_dyadic_bound_f 705074392 536870912 4 3 536870912 268435456 Ns528p834 Ns528p145 Ns528p835 Ns528p836 Ns528p148 Ns528p835 136717903 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 705074392) qz20 0 3 Ns528p834 Ns528p145 Ns528p835 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 705074392) qz377 0 3 Ns528p836 Ns528p148 Ns528p835 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p838 := Ns528p788 137893 BSN.abs_quadSignPos (BSN.cos_quad_nat3 355 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 435716397 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 224 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 136717903 536870912) qz119 rfl rfl (Ns528p821 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p825 rfl rfl) (Ns528p829 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p820 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p833 rfl rfl) (Ns528p837 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p839 := nat_lit 175669420450099701340764529762530408854552639435047290866339427553493684138384829475945971635902549319297856615201 

noncomputable def Ns528p840 := nat_lit 117321353613959261351956515918107297427885576392987793798056790200561467619750768737348059157076906774016801 

noncomputable def Ns528p841 := nat_lit 877290623714837932410291147170651981720583567892818984906320571536526019558627979115355986275149852263891305411361 

noncomputable def Ns528p842 := BSN.sin_dyadic_bound_f 836465607 536870912 4 3 536870912 268435456 Ns528p839 Ns528p135 Ns528p840 Ns528p841 Ns528p138 Ns528p840 536827222 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 836465607) qz375 0 3 Ns528p839 Ns528p135 Ns528p840 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 836465607) qz376 0 3 Ns528p841 Ns528p138 Ns528p840 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p843 := nat_lit 23598971830798210180307149895948979235663069244749293729503469018403357825 

noncomputable def Ns528p844 := nat_lit 8817368701988807980761755046368194336599355195996817686532840079803521 

noncomputable def Ns528p845 := nat_lit 61792555245620663830740349743124635207334496684978441110540413307117683841 

noncomputable def Ns528p846 := BSN.sin_dyadic_bound_f 553563409 536870912 3 2 536870912 268435456 Ns528p843 Ns528p180 Ns528p844 Ns528p845 Ns528p183 Ns528p844 460560489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 553563409) qz375 0 2 Ns528p843 Ns528p180 Ns528p844 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 553563409) qz376 0 2 Ns528p845 Ns528p183 Ns528p844 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p847 := Ns528p786 185593 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536827222 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 27 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 460560489 536870912) qz119 rfl rfl (Ns528p838 rfl rfl) (Ns528p820 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p842 rfl rfl) (Ns528p846 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p848 := nat_lit 8779980449748341909569251617775527964552993651360039882951596665595016481073564141966345263440087764462751256576 

noncomputable def Ns528p849 := nat_lit 258601985112579917879504017316992991309553355028434117513960944673089801279064608965318893594292035588096 

noncomputable def Ns528p850 := nat_lit 53249011141396708969529327229321340290413844298311301854001402545460030339804938093980961221726294527905348259840 

noncomputable def Ns528p851 := BSN.cos_dyadic_bound_f 502403498 536870912 4 3 536870912 268435456 Ns528p848 Ns528p145 Ns528p849 Ns528p850 Ns528p148 Ns528p849 318458408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 502403498) qz20 0 3 Ns528p848 Ns528p145 Ns528p849 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 502403498) qz377 0 3 Ns528p850 Ns528p148 Ns528p849 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p852 := nat_lit 18662174823741863466343154741759769502276702588289252202208350326059171840 

noncomputable def Ns528p853 := nat_lit 5514996209292822404296062086875212017434243883724393546662708380696576 

noncomputable def Ns528p854 := nat_lit 48868195496889834985101306889801598353172660860183916273374892183252893696 

noncomputable def Ns528p855 := BSN.sin_dyadic_bound_f 522027224 536870912 3 2 536870912 268435456 Ns528p852 Ns528p180 Ns528p853 Ns528p854 Ns528p183 Ns528p853 443569576 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 522027224) qz375 0 2 Ns528p852 Ns528p180 Ns528p853 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 522027224) qz376 0 2 Ns528p854 Ns528p183 Ns528p853 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p856 := Ns528p784 227269 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 318458408 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 443569576 536870912) qz119 rfl rfl (Ns528p847 rfl) (Ns528p820 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p851 rfl rfl) (Ns528p855 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p857 := nat_lit 2193268108005077359147961265172785852360820571626892490057684553860317440 

noncomputable def Ns528p858 := nat_lit 76213287705435695516752246328653042373534252449428939030273896939776 

noncomputable def Ns528p859 := nat_lit 5744150223261774759023347619434668936971639584518847922345029578562928896 

noncomputable def Ns528p860 := BSN.sin_dyadic_bound_f 305670718 536870912 3 2 536870912 268435456 Ns528p857 Ns528p180 Ns528p858 Ns528p859 Ns528p183 Ns528p858 289421643 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 305670718) qz375 0 2 Ns528p857 Ns528p180 Ns528p858 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 305670718) qz376 0 2 Ns528p859 Ns528p183 Ns528p858 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p861 := nat_lit 1104899471380243786935759708160000 

noncomputable def Ns528p862 := BSN.sin_dyadic_bound_f 182318480 536870912 2 1 536870912 268435456 Ns528p861 Ns528p160 Ns528p861 Ns528p861 Ns528p161 Ns528p861 178834332 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 182318480) qz375 0 1 Ns528p861 Ns528p160 Ns528p861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 182318480) qz376 0 1 Ns528p861 Ns528p161 Ns528p861 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p863 := Ns528p782 264752 BSN.abs_quadSignNeg qz601 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 289421643 536870912) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 178834332 536870912) qz119 rfl rfl (Ns528p856 rfl) (Ns528p820 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p860 rfl rfl) (Ns528p862 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p864 := nat_lit 128723435241079557512389279621535164003041034445978740860153377720451201 

noncomputable def Ns528p865 := nat_lit 850612861950953941061333465609158576574757646685597800790855073921 

noncomputable def Ns528p866 := nat_lit 386168604497514770629285716197674273691969953822642851384858551451205761 

noncomputable def Ns528p867 := BSN.cos_dyadic_bound_f 174267537 536870912 3 2 536870912 268435456 Ns528p864 Ns528p165 Ns528p865 Ns528p866 Ns528p168 Ns528p865 508834882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 174267537) qz20 0 2 Ns528p864 Ns528p165 Ns528p865 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 174267537) qz377 0 2 Ns528p866 Ns528p168 Ns528p865 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p868 := Ns528p780 Bool.false 595524917 264752 Bool.true 174267537 28296951008113761 1 Bool.false 508834882 Bool.false Bool.false 742412899 282269 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 508834882 536870912) qz119 rfl (Ns528p863 rfl) (Ns528p820 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p867 rfl rfl) rfl 

noncomputable def Ns528p869 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) 742412899 536870912 282269 536870912 742412899 536870912 282269 536870912 797159780333387776 742412899 268435456 282269 268435456 (Ns528p868 rfl rfl rfl rfl) 

noncomputable def Ns528p870 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz117) (Zeta.RiemannSiegel.correction qz118) 19289309 67108864 1 67108864 1584285688620525 2251799813685248 2871383892997339 316659348799488000000 30559776192079090467225 151115727451828646838272 

noncomputable def Ns528p871 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz117 1 1 0 1 19289309 67108864 1 67108864 19289309 67108864 1 67108864 

noncomputable abbrev qz125 := qz446

noncomputable def Ns528p872 := @Enclosure.Real.IsNear.sqrt_image qz125 9831793726933 67108864000 920519 67108864000 406140507 406140546 33554432 (@Enclosure.Real.IsNear.of_eq qz125 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 9831793726933 67108864000 920519 67108864000 (BSN.t_div_two_pi_mk qz116 920519 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 920519 1000 0 1 10680707 67108864 1 67108864 9831793726933 67108864000 920519 67108864000 (Enclosure.Real.IsNear.const Bool.false 920519 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz741 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 920519 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz637 := qz741

noncomputable abbrev qz453 := qz637

noncomputable abbrev qz126 := qz453

noncomputable def Ns528p873 := @Enclosure.Real.IsNear.sqrt_image qz126 812281053 67108864 39 67108864 116738228 116738235 33554432 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 812281053 67108864 39 67108864 812281053 67108864 39 67108864 (Ns528p872 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p874 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz126) 233476463 67108864 7 67108864 9644654 9644655 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz126) Bool.false 233476463 67108864 7 67108864 233476463 67108864 7 67108864 (Ns528p873 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p875 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz126)) Bool.false 19289309 67108864 1 67108864 19289309 67108864 1 67108864 (Ns528p874 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz447))

noncomputable abbrev qz638 := (@HMul.hMul Real Real Real qz713 qz740 qz740)

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz638 qz633) qz594)

noncomputable abbrev qz128 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz454))

noncomputable def Ns528p876 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz127) qz128) Bool.false 1584285688620525 

noncomputable def Ns528p877 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz127) qz128 84492925 67108864 403 

noncomputable def Ns528p878 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz127) Bool.false 84492925 67108864 403 67108864 84492925 67108864 403 

noncomputable def Ns528p879 := @Enclosure.Real.IsNear.recentre' qz127 Bool.false 26650750 33554432 1140554432 301989888000000 13325375 16777216 17821163 4718592000000 

noncomputable abbrev qz129 := (@HMul.hMul Real Real Real qz355 qz352 qz447)

noncomputable def Ns528p880 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 21911619) qz415) Bool.false 21911619 33554432 123 33554432 Bool.false 26650750 33554432 1 

noncomputable def Ns528p881 := nat_lit 1052456941012629860701393233 

noncomputable def Ns528p882 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 6974685 67108864 39 67108864 6167572491938310005175 9444732965739290427392 Ns528p881 

noncomputable def Ns528p883 := @Enclosure.Real.IsNear.subLit_ff_p qz126 qz1 812281053 67108864 39 67108864 12 1 0 1 6974685 6974685 67108864 39 

noncomputable def Ns528p884 := @Ns528p883 67108864 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 812281053 67108864 39 67108864 812281053 67108864 39 67108864 (Ns528p872 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p885 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 6167572491938310005175 9444732965739290427392 Ns528p881 Ns528p330 21911619 33554432 123 33554432 (@Ns528p882 Ns528p330 RS529to540.d55 (Ns528p884 rfl rfl) rfl) 

noncomputable def Ns528p886 := nat_lit 490968608216642152251208427033720706477894381423261473342959521 

noncomputable def Ns528p887 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320 

noncomputable def Ns528p888 := nat_lit 53136842267221937521225475914172371508989564175382743822241 

noncomputable def Ns528p889 := nat_lit 1472799550965392012878582830149333774690665165141433654541234081 

noncomputable def Ns528p890 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400 

noncomputable def Ns528p891 := BSN.cos_dyadic_bound_f 21911619 33554432 3 2 33554432 9000000 Ns528p886 Ns528p887 Ns528p888 Ns528p889 Ns528p890 Ns528p888 26650750 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 21911619) (BSN.cosEvenQ 33554432) 0 2 Ns528p886 Ns528p887 Ns528p888 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 21911619) (BSN.cosOddQ 33554432) 0 2 Ns528p889 Ns528p890 Ns528p888 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p892 := @Enclosure.Real.IsNear.inv_image qz127 13325375 16777216 17821163 4718592000000 42246261 42246664 33554432 (Ns528p879 (@Ns528p880 9000000 (Ns528p885 rfl) (Enclosure.sfrac_false_div 21911619 33554432) (Ns528p891 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p893 := @Enclosure.Real.IsNear.recentre' qz128 Bool.false 18750513 33554432 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz355 qz352 qz454)

noncomputable def Ns528p894 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32811119)) qz415) Bool.true 32811119 33554432 

noncomputable def Ns528p895 := nat_lit 619784521537925466336554758405 

noncomputable def Ns528p896 := nat_lit 85310342046510893175916806376268081 

noncomputable def Ns528p897 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns528p895 Ns528p217 Ns528p896 

noncomputable abbrev qz131 := qz454

noncomputable def Ns528p898 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 700891932969271 

noncomputable abbrev qz455 := (@HSub.hSub Real Real Real qz581 qz638 qz633)

noncomputable abbrev qz132 := qz455

noncomputable def Ns528p899 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 419416956258615 4503599627370496 3161272647 4503599627370496 1 16 

noncomputable abbrev qz456 := qz638

noncomputable abbrev qz133 := qz456

noncomputable def Ns528p900 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 48646230849225 4503599627370496 544026951 4503599627370496 6974685 67108864 39 67108864 

noncomputable def Ns528p901 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 6974685 67108864 39 67108864 6974685 67108864 39 67108864 48646230849225 4503599627370496 

noncomputable def Ns528p902 := nat_lit 2469615281442273590151354025999989901680802249513210934152763521 

noncomputable def Ns528p903 := nat_lit 1343285527043136620575140290579688730624734333195217195866241 

noncomputable def Ns528p904 := nat_lit 7406159273272734497212911797418810327581157279873242368066558081 

noncomputable def Ns528p905 := BSN.cos_dyadic_bound_f 32811119 33554432 3 2 33554432 9000000 Ns528p902 Ns528p887 Ns528p903 Ns528p904 Ns528p890 Ns528p903 18750513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 32811119) (BSN.cosEvenQ 33554432) 0 2 Ns528p902 Ns528p887 Ns528p903 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 32811119) (BSN.cosOddQ 33554432) 0 2 Ns528p904 Ns528p890 Ns528p903 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p906 := @Ns528p893 2740108864 603979776000000 18750513 33554432 42814201 9437184000000 (@Ns528p894 297 67108864 Bool.false 18750513 33554432 1 9000000 (@Ns528p897 Ns528p220 32811119 33554432 297 67108864 (@Ns528p898 4503599627370496 3161272647 4503599627370496 Ns528p895 Ns528p217 Ns528p896 Ns528p220 RS529to540.d55 (@Ns528p899 0 1 11214270927508336 700891932969271 4503599627370496 3161272647 4503599627370496 (@Ns528p900 28146595476853342863360 419416956258615 4503599627370496 3161272647 4503599627370496 (@Ns528p901 544026951 4503599627370496 (Ns528p884 rfl rfl) (Ns528p884 rfl rfl) rfl) (Ns528p884 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 32811119 33554432) (BSN.cos_neg_of_bound 32811119 33554432 Bool.false 18750513 33554432 1 9000000 (Ns528p905 rfl rfl)) rfl rfl) 

noncomputable def Ns528p907 := @Ns528p870 3707320281066317498281 Ns528p777 (Ns528p871 qz33 (@Enclosure.Real.IsNear.of_eq qz117 (@Inv.inv Real Real.instInv (Real.sqrt qz126)) Bool.false 19289309 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz125 (BSN.t_div_two_pi_nonneg qz116 920519 1000 qz119)) Ns528p875) rfl) (@Ns528p876 2251799813685248 2871383892997339 316659348799488000000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 920519 1000 12 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 920519 1000 12 qz119 rfl rfl rfl))) (@Ns528p877 67108864 18750513 33554432 42814201 9437184000000 1584285688620525 2251799813685248 2871383892997339 316659348799488000000 (@Ns528p878 67108864 (Ns528p892 rfl rfl rfl rfl rfl) rfl) (Ns528p906 rfl) rfl)) 

noncomputable def Ns528p908 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 387381530719352119836263 151115727451828646838272 Ns528p776 Ns528p777 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz117) (Zeta.RiemannSiegel.correction qz118))) Bool.false 387381530719352119836263 151115727451828646838272 Ns528p776 Ns528p777 (BSN.hardyZApproximantRS₀_eq qz116 12 (@BSN.floor_sqrt_eq_dec qz116 920519 1000 12 qz119 rfl rfl rfl)) (@Ns528p779 387381530719352119836263 151115727451828646838272 Ns528p776 Ns528p777 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12)) Bool.false 742412899 268435456 282269 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (Ns528p869 (Ns528p868 rfl rfl rfl rfl) rfl rfl)) (Ns528p907 rfl) rfl rfl)) 

theorem RS529to540.d64 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 387381530719352119836263 151115727451828646838272 Ns528p776 Ns528p777 := Ns528p908 

noncomputable def Ns528p909 := nat_lit 118059162071741130342400000 

noncomputable def Ns528p910 := nat_lit 5069677018445212871387770781696 

noncomputable abbrev qz742 := (Enclosure.sfrac Bool.false 921779 1000)

noncomputable abbrev qz639 := qz742

noncomputable abbrev qz457 := qz639

noncomputable abbrev qz134 := qz457

noncomputable abbrev qz743 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 921779 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz640 := qz743

noncomputable abbrev qz458 := qz640

noncomputable abbrev qz135 := (@HPow.hPow Real Real Real qz356 qz458 qz358)

noncomputable abbrev qz744 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 921779 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz641 := qz744

noncomputable abbrev qz459 := qz641

noncomputable abbrev qz136 := qz459

noncomputable def Ns528p911 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz135) (Zeta.RiemannSiegel.correction qz136)) 241824923 134217728 35331 33554432 3738204941557957083213 18889465931478580854784 323288966159812189047 Ns528p909 Ns528p910 

noncomputable def Ns528p912 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos BSN.quadSignPos 11 12 921779 1000 288 536870912 268435456 9007199254740992 Bool.false 986678601368 4500 1334074092 61 154981288 8 

noncomputable def Ns528p913 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 921779 1000 181 237 536870912 268435456 9007199254740992 Bool.false 986678601368 4500 

noncomputable def Ns528p914 := Ns528p913 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.true 541226433 227573 Bool.true 176272830 Bool.true 117393865 28296951008113761 1 Bool.false 173122732 Bool.true Bool.false 116460595 Bool.true Bool.true 631086840 

noncomputable def Ns528p915 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 921779 1000 50 119 536870912 268435456 9007199254740992 Bool.false 986678601368 4500 

noncomputable def Ns528p916 := Ns528p915 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.true 468256257 185840 Bool.true 222058516 Bool.true 321357426 28296951008113761 1 Bool.false 491598397 Bool.true Bool.false 302508330 Bool.false Bool.true 541226433 

noncomputable def Ns528p917 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 921779 1000 118 28 536870912 268435456 9007199254740992 Bool.false 986678601368 4500 

noncomputable def Ns528p918 := Ns528p917 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.true 527862155 138075 Bool.false 468100391 Bool.false 80921844 28296951008113761 1 Bool.false 345406311 Bool.true Bool.false 530783828 Bool.false Bool.true 468256257 

noncomputable def Ns528p919 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 921779 1000 356 225 536870912 268435456 9007199254740992 Bool.false 986678601368 4500 

noncomputable def Ns528p920 := Ns528p919 744261104 60 268435448 8 864060384 60 240095976 8 Bool.true 538805603 81405 Bool.false 414256258 Bool.false 460041945 28296951008113761 1 Bool.false 384822241 Bool.false Bool.false 405774029 Bool.true Bool.true 527862155 

noncomputable def Ns528p921 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 921779 1000 763 525 536870912 268435456 9007199254740992 Bool.false 986678601368 4500 

noncomputable def Ns528p922 := Ns528p921 372130544 60 379625064 8 589812976 60 309962568 8 Bool.true 536870864 4564 Bool.false 207245115 Bool.false 261086484 28296951008113761 1 Bool.false 202136236 Bool.false Bool.false 250916383 Bool.true Bool.true 538805603 

noncomputable def Ns528p923 := nat_lit 182780286046170425135952942380028783952716507574356745511477 

noncomputable def Ns528p924 := nat_lit 99454289095845966095604892920478098111808565491531776000 

noncomputable def Ns528p925 := nat_lit 319429932745112187144779429551520000 

noncomputable def Ns528p926 := nat_lit 1766663066430957337893035460049839324480 

noncomputable abbrev qz642 := (@Eq.refl Real qz742)

noncomputable abbrev qz460 := qz642

noncomputable abbrev qz137 := qz460

noncomputable def Ns528p927 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 921779 1000 3398707099364 16000000 1843558 4000 2000 Ns528p925 Ns528p926 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p928 := nat_lit 58489691534774536043504941561609210864869282423794158563672640 

noncomputable abbrev qz643 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1843558))))

noncomputable abbrev qz461 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 921779 4000) (Real.log (Enclosure.sfrac Bool.false 3398707099364 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz643))

noncomputable abbrev qz644 := (Enclosure.sfrac Bool.false 921779 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz461 qz644) (@HMul.hMul Real Real Real qz355 qz644 (Real.log Real.pi)))

noncomputable def Ns528p929 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns528p925 Ns528p926) 33107443292667298420293 18014398509481984000 1235569917141348077 147456000000000000000000 Ns528p925 Ns528p926 0 1 Ns528p928 

noncomputable def Ns528p930 := nat_lit 2221802909315321926934857777152000 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz361 qz461 qz644)

noncomputable def Ns528p931 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz644 (Real.log Real.pi)) 42611731556708737586757 18014398509481984000 116222516036687 36000000000000000000 35406232863819 67108864000 2765337 536870912000 Ns528p930 33107443292667298420293 18014398509481984000 

noncomputable def Ns528p932 := nat_lit 3408938524536699006940560 

noncomputable abbrev qz140 := qz461

noncomputable def Ns528p933 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz644 2036575147141785378061 720575940379279360 116222516036687 36000000000000000000 921779 2000 0 1 Ns528p932 42611731556708737586757 18014398509481984000 116222516036687 36000000000000000000 

noncomputable def Ns528p934 := nat_lit 4585959536889878845232508249338544128 

noncomputable def Ns528p935 := nat_lit 118632537977493683752140800 

noncomputable def Ns528p936 := nat_lit 102611237457171163488247390298622151834365743753220391181138090457210777349853258287944842618248014510581864719116587951854167546938427456570905733524053032960 

noncomputable def Ns528p937 := nat_lit 1985608790426183372819620864727158427646240134447025011983724323854527402932615405560036862461561509556365492894320868213071934586918807357772969177264422912 

noncomputable def Ns528p938 := nat_lit 245683047233863057098492497450727591209202104867660609886387204606055959863560381260157789840897213305865758709514500877947109781584236524553025617920 

noncomputable def Ns528p939 := BSN.log_dyadic_bound 1301555099364 5495859099364 7 6 Ns528p936 268435456 72000000 Ns528p937 Ns528p938 129604627 6797414198728 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1301555099364) (BSN.artanhQ 5495859099364) 0 6 Ns528p937 Ns528p936 Ns528p938 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz462 := (Real.log (Enclosure.sfrac Bool.false 3398707099364 16000000))

noncomputable def Ns528p940 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 921779 4000) qz462 921779 4000 0 1 55242580351183975 4503599627370496 125000153 9000000000000000 2036858018941360531661 720575940379279360 115222516032187 36000000000000000000 (Enclosure.Real.IsNear.const Bool.false 921779 4000) (BSN.isNear_log_sfrac 3398707099364 16000000 55242580351183975 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3398707099364) qz364)) Bool.false Ns528p935 Ns528p113 1000001224000000 72000000000000000000000 55242580351183975 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3398707099364 16000000 17 6797414198728 4194304000000 129604627 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p939 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p941 := BSN.arctan_dyadic_bound_f 1000 1843558 1 0 33554432 9000000 0 1 1 0 1 1 18200 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1843558) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1843558) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns528p942 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1843558))) 884279719003555 562949953421312 1 2000000000000000 18200 33554432 1 9000000 29661258011131626127360 883974373672355 562949953421312 2000000009 18000000000000000 qz15 (Ns528p941 rfl) rfl rfl 

noncomputable abbrev qz463 := (@HMul.hMul Real Real Real qz577 qz582 qz643)

noncomputable abbrev qz141 := qz463

noncomputable abbrev qz464 := qz643

noncomputable abbrev qz142 := qz464

noncomputable def Ns528p943 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 921779 4000) qz462) qz141 2036858018941360531661 720575940379279360 115222516032187 36000000000000000000 883974373672355 2251799813685248 2000000009 72000000000000000 Ns528p934 2036575147141785378061 720575940379279360 116222516036687 36000000000000000000 (Ns528p940 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz142 1 4 0 1 883974373672355 562949953421312 2000000009 18000000000000000 883974373672355 2251799813685248 2000000009 72000000000000000 qz372 Ns528p942 rfl) 

noncomputable def Ns528p944 := @Ns528p929 Ns528p923 Ns528p924 1235569917141348077 147456000000000000000000 (@Ns528p931 1235569917141348077 147456000000000000000000 (Ns528p933 (Ns528p943 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 921779 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz644 (Real.log Real.pi) 921779 2000 0 1 38410761 33554432 3 268435456 35406232863819 67108864000 2765337 536870912000 (Enclosure.Real.IsNear.const Bool.false 921779 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p925 Ns528p926) 

noncomputable def Ns528p945 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns528p923 Ns528p924 1235569917141348077 147456000000000000000000 123334825171 67108864 563 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz373 qz138 (Enclosure.sfrac Bool.true Ns528p925 Ns528p926)) Bool.false Ns528p923 Ns528p924 1235569917141348077 147456000000000000000000 Ns528p927 (Ns528p944 rfl rfl)) 

noncomputable def Ns528p946 := BSN.cos_dyadic_bound_f 56121555 137438953472 1 0 67108864 18017579 0 1 1 0 1 1 67108858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 56121555) qz588 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 56121555) qz589 0 0 rfl) rfl rfl 

noncomputable def Ns528p947 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123334825171) qz19) Bool.false 123334825171 67108864 563 67108864 Bool.true 67108858 67108864 1 9000000 (Ns528p945 rfl) (Enclosure.sfrac_false_div 123334825171 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123334825171) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3949203403994103283712) qz374) 226375608064910080 72057594037927936 Bool.false 67108858 67108864 292 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q2 123334825171 67108864 226375608064910080 72057594037927936 292 3949203403994103283712 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108858 67108864 3949203403994103283712 Ns528p113 56121555 137438953472 18017579 18000000 (Ns528p946 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p948 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns528p923 Ns528p924 1235569917141348077 147456000000000000000000 986678601368 536870912 4500 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz373 qz138 (Enclosure.sfrac Bool.true Ns528p925 Ns528p926)) Bool.false Ns528p923 Ns528p924 1235569917141348077 147456000000000000000000 Ns528p927 (Ns528p944 rfl rfl)) 

noncomputable def Ns528p949 := Ns528p922 81405 BSN.abs_quadSignPos (BSN.cos_quad_nat3 763 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 202136236 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 525 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 250916383 536870912) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 33554429 33554432 80220451 9437184000000 536870864 536870912 4564 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 33554429 33554432 80220451 9437184000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 67108858 67108864 5134108864 603979776000000 33554429 33554432 80220451 9437184000000 (Ns528p947 rfl rfl) rfl)) rfl) (Ns528p948 rfl) RS529to540.d7 

noncomputable def Ns528p950 := nat_lit 1844748687977213029586758882400625 

noncomputable def Ns528p951 := BSN.sin_dyadic_bound_f 207245115 536870912 2 1 536870912 268435456 Ns528p950 Ns528p160 Ns528p950 Ns528p950 Ns528p161 Ns528p950 202136236 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 207245115) qz375 0 1 Ns528p950 Ns528p160 Ns528p950 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 207245115) qz376 0 1 Ns528p950 Ns528p161 Ns528p950 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p952 := nat_lit 1167365557009949432084837152238576723557038706576633333777094014731878400 

noncomputable def Ns528p953 := nat_lit 21591117346941992562159897735956884950476060829780050764498479415296 

noncomputable def Ns528p954 := nat_lit 3057351025597972511281853806504699869597562508364124801714960850569199616 

noncomputable def Ns528p955 := BSN.sin_dyadic_bound_f 261086484 536870912 3 2 536870912 268435456 Ns528p952 Ns528p180 Ns528p953 Ns528p954 Ns528p183 Ns528p953 250916383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 261086484) qz375 0 2 Ns528p952 Ns528p180 Ns528p953 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 261086484) qz376 0 2 Ns528p954 Ns528p183 Ns528p953 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p956 := nat_lit 4111087474699991952414303772005434341231677339702784716122855074161623296 

noncomputable def Ns528p957 := nat_lit 867266603100167467592344142535491238301959190915126455427049102377216 

noncomputable def Ns528p958 := nat_lit 12331527890893775522307726627731232041218428100726523895457711124280115456 

noncomputable def Ns528p959 := BSN.cos_dyadic_bound_f 414256258 536870912 3 2 536870912 268435456 Ns528p956 Ns528p165 Ns528p957 Ns528p958 Ns528p168 Ns528p957 384822241 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 414256258) qz20 0 2 Ns528p956 Ns528p165 Ns528p957 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 414256258) qz377 0 2 Ns528p958 Ns528p168 Ns528p957 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p960 := nat_lit 11254557679541278309932536638668158385847783343671052472171854562132530625 

noncomputable def Ns528p961 := nat_lit 2006224119738960714535567396287861652773290089452861898684745187890625 

noncomputable def Ns528p962 := nat_lit 29472974321652342018190252658822615425020656763755547079280796170519090625 

noncomputable def Ns528p963 := BSN.sin_dyadic_bound_f 460041945 536870912 3 2 536870912 268435456 Ns528p960 Ns528p180 Ns528p961 Ns528p962 Ns528p183 Ns528p961 405774029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 460041945) qz375 0 2 Ns528p960 Ns528p180 Ns528p961 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 460041945) qz376 0 2 Ns528p962 Ns528p183 Ns528p961 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p964 := Ns528p920 138075 BSN.abs_quadSignPos (BSN.cos_quad_nat0 356 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 384822241 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 225 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 405774029 536870912) qz137 rfl rfl (Ns528p949 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p951 rfl rfl) (Ns528p955 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p948 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p959 rfl rfl) (Ns528p963 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p965 := nat_lit 6703385088082818332381713755018672759118509296706789769975714212971083201 

noncomputable def Ns528p966 := nat_lit 2305218154265856367413411816827350286340180224331151837016150706025921 

noncomputable def Ns528p967 := nat_lit 20105544827939923284410314441422363576782847529671707006253110337501197761 

noncomputable def Ns528p968 := BSN.cos_dyadic_bound_f 468100391 536870912 3 2 536870912 268435456 Ns528p965 Ns528p165 Ns528p966 Ns528p967 Ns528p168 Ns528p966 345406311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 468100391) qz20 0 2 Ns528p965 Ns528p165 Ns528p966 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 468100391) qz377 0 2 Ns528p967 Ns528p168 Ns528p966 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p969 := nat_lit 42880820095887075665779634032896 

noncomputable def Ns528p970 := BSN.cos_dyadic_bound_f 80921844 536870912 2 1 536870912 268435456 Ns528p969 Ns528p141 Ns528p969 Ns528p969 Ns528p142 Ns528p969 530783828 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 80921844) qz20 0 1 Ns528p969 Ns528p141 Ns528p969 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 80921844) qz377 0 1 Ns528p969 Ns528p142 Ns528p969 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p971 := Ns528p918 185840 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 345406311 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 530783828 536870912) qz137 rfl rfl (Ns528p964 rfl rfl) (Ns528p948 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p968 rfl rfl) (Ns528p970 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p972 := nat_lit 339364239945446358150105592848419207707235016067133406309475751339032576 

noncomputable def Ns528p973 := nat_lit 5912068604804333573979218581758384479720768490876371304538712375296 

noncomputable def Ns528p974 := nat_lit 1018080895699129465783168820108094106352745606664418466185818176592347136 

noncomputable def Ns528p975 := BSN.cos_dyadic_bound_f 222058516 536870912 3 2 536870912 268435456 Ns528p972 Ns528p165 Ns528p973 Ns528p974 Ns528p168 Ns528p973 491598397 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 222058516) qz20 0 2 Ns528p972 Ns528p165 Ns528p973 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 222058516) qz377 0 2 Ns528p974 Ns528p168 Ns528p973 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p976 := nat_lit 2679372406136875470373951587755516765844645705544798641009406972402909440 

noncomputable def Ns528p977 := nat_lit 113738296950769683127610560350906099974960324489341058153987459563776 

noncomputable def Ns528p978 := nat_lit 7017219773115801176254333265119118634002684054949108936168578471834992896 

noncomputable def Ns528p979 := BSN.sin_dyadic_bound_f 321357426 536870912 3 2 536870912 268435456 Ns528p976 Ns528p180 Ns528p977 Ns528p978 Ns528p183 Ns528p977 302508330 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 321357426) qz375 0 2 Ns528p976 Ns528p180 Ns528p977 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 321357426) qz376 0 2 Ns528p978 Ns528p183 Ns528p977 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p980 := Ns528p916 227573 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 491598397 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 302508330 536870912) qz137 rfl rfl (Ns528p971 rfl) (Ns528p948 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p975 rfl rfl) (Ns528p979 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p981 := nat_lit 965476056903037403023052439210000 

noncomputable def Ns528p982 := BSN.sin_dyadic_bound_f 176272830 536870912 2 1 536870912 268435456 Ns528p981 Ns528p160 Ns528p981 Ns528p981 Ns528p161 Ns528p981 173122732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 176272830) qz375 0 1 Ns528p981 Ns528p160 Ns528p981 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 176272830) qz376 0 1 Ns528p981 Ns528p161 Ns528p981 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p983 := nat_lit 189924768253614337846963881150625 

noncomputable def Ns528p984 := BSN.sin_dyadic_bound_f 117393865 536870912 2 1 536870912 268435456 Ns528p983 Ns528p160 Ns528p983 Ns528p983 Ns528p161 Ns528p983 116460595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 117393865) qz375 0 1 Ns528p983 Ns528p160 Ns528p983 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 117393865) qz376 0 1 Ns528p983 Ns528p161 Ns528p983 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p985 := Ns528p914 265107 BSN.abs_quadSignNeg qz601 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 173122732 536870912) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 116460595 536870912) qz137 rfl rfl (Ns528p980 rfl) (Ns528p948 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p982 rfl rfl) (Ns528p984 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p986 := nat_lit 111717194888015685637183104813161156116446944242467966967349248000000000 

noncomputable def Ns528p987 := nat_lit 640704104185103726449009421268334628083062286581760000000000000000 

noncomputable def Ns528p988 := nat_lit 335150303255838686704096416420640931680084666602830737382047744000000000 

noncomputable def Ns528p989 := BSN.cos_dyadic_bound_f 168202400 536870912 3 2 536870912 268435456 Ns528p986 Ns528p165 Ns528p987 Ns528p988 Ns528p168 Ns528p987 510736715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 168202400) qz20 0 2 Ns528p986 Ns528p165 Ns528p987 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 168202400) qz377 0 2 Ns528p988 Ns528p168 Ns528p987 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p990 := Ns528p912 Bool.true 631086840 265107 Bool.true 168202400 28296951008113761 1 Bool.false 510736715 Bool.false Bool.true 483649846 282648 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 510736715 536870912) qz137 rfl (Ns528p985 rfl) (Ns528p948 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p989 rfl rfl) rfl 

noncomputable def Ns528p991 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) 483649846 536870912 282648 536870912 483649846 536870912 282648 536870912 519315067821359104 241824923 134217728 35331 33554432 (Ns528p990 rfl rfl rfl rfl) 

noncomputable def Ns528p992 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz135) (Zeta.RiemannSiegel.correction qz136) 9641357 33554432 1 33554432 387726016323009 562949953421312 66560266418443 7036874417766400000 3738204941557957083213 18889465931478580854784 

noncomputable def Ns528p993 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz135 1 1 0 1 9641357 33554432 1 33554432 9641357 33554432 1 33554432 

noncomputable abbrev qz143 := qz458

noncomputable def Ns528p994 := @Enclosure.Real.IsNear.sqrt_image qz143 9845251417753 67108864000 921779 67108864000 406418373 406418412 33554432 (@Enclosure.Real.IsNear.of_eq qz143 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 9845251417753 67108864000 921779 67108864000 (BSN.t_div_two_pi_mk qz134 921779 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 921779 1000 0 1 10680707 67108864 1 67108864 9845251417753 67108864000 921779 67108864000 (Enclosure.Real.IsNear.const Bool.false 921779 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz745 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 921779 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz645 := qz745

noncomputable abbrev qz465 := qz645

noncomputable abbrev qz144 := qz465

noncomputable def Ns528p995 := @Enclosure.Real.IsNear.sqrt_image qz144 812836785 67108864 39 67108864 116778155 116778162 33554432 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 812836785 67108864 39 67108864 812836785 67108864 39 67108864 (Ns528p994 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p996 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz144) 233556317 67108864 7 67108864 9641356 9641358 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz144) Bool.false 233556317 67108864 7 67108864 233556317 67108864 7 67108864 (Ns528p995 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p997 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz144)) Bool.false 19282714 67108864 2 67108864 9641357 33554432 1 33554432 (Ns528p996 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz459))

noncomputable abbrev qz646 := (@HMul.hMul Real Real Real qz713 qz744 qz744)

noncomputable abbrev qz466 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz646 qz641) qz594)

noncomputable abbrev qz146 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz466))

noncomputable def Ns528p998 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz145) qz146) Bool.false 387726016323009 

noncomputable def Ns528p999 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz145) qz146 22029483 16777216 219 

noncomputable def Ns528p1000 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz145) Bool.false 88117932 67108864 438 67108864 22029483 16777216 219 

noncomputable def Ns528p1001 := @Enclosure.Real.IsNear.recentre' qz145 Bool.false 25554388 33554432 1140554432 301989888000000 6388597 8388608 17821163 4718592000000 

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz355 qz352 qz459)

noncomputable def Ns528p1002 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 47315005) qz19) Bool.false 47315005 67108864 123 33554432 Bool.false 25554388 33554432 1 

noncomputable def Ns528p1003 := nat_lit 1052456941017403562232074577 

noncomputable def Ns528p1004 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 7530417 67108864 39 67108864 6658995028739593632435 9444732965739290427392 Ns528p1003 

noncomputable def Ns528p1005 := @Enclosure.Real.IsNear.subLit_ff_p qz144 qz1 812836785 67108864 39 67108864 12 1 0 1 7530417 7530417 67108864 39 

noncomputable def Ns528p1006 := @Ns528p1005 67108864 (@Enclosure.Real.IsNear.recentre' qz144 Bool.false 812836785 67108864 39 67108864 812836785 67108864 39 67108864 (Ns528p994 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p1007 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 6658995028739593632435 9444732965739290427392 Ns528p1003 Ns528p330 47315005 67108864 123 33554432 (@Ns528p1004 Ns528p330 RS529to540.d55 (Ns528p1006 rfl rfl) rfl) 

noncomputable def Ns528p1008 := nat_lit 170800156909407625505705026722767990705537082700597191073292190625 

noncomputable def Ns528p1009 := nat_lit 25118350864612649021550231580021266892113228432190509375390625 

noncomputable def Ns528p1010 := nat_lit 512350234026493651219071979705143929582827021644927192201125790625 

noncomputable def Ns528p1011 := BSN.cos_dyadic_bound_f 47315005 67108864 3 2 33554432 9000000 Ns528p1008 Ns528p226 Ns528p1009 Ns528p1010 Ns528p229 Ns528p1009 25554388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 47315005) qz383 0 2 Ns528p1008 Ns528p226 Ns528p1009 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 47315005) (BSN.cosOddQ 67108864) 0 2 Ns528p1010 Ns528p229 Ns528p1009 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1012 := @Enclosure.Real.IsNear.inv_image qz145 6388597 8388608 17821163 4718592000000 44058747 44059185 33554432 (Ns528p1001 (@Ns528p1002 9000000 (Ns528p1007 rfl) (Enclosure.sfrac_false_div 47315005 67108864) (Ns528p1011 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p1013 := @Enclosure.Real.IsNear.recentre' qz146 Bool.false 17600323 33554432 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz355 qz352 qz466)

noncomputable def Ns528p1014 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 68359285)) qz19) Bool.true 68359285 67108864 

noncomputable def Ns528p1015 := nat_lit 645635195705256431559436510525 

noncomputable def Ns528p1016 := nat_lit 86480110048181079341669376402654041 

noncomputable def Ns528p1017 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns528p1015 Ns528p217 Ns528p1016 

noncomputable abbrev qz149 := qz466

noncomputable def Ns528p1018 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 730125526833055 

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz581 qz646 qz641)

noncomputable abbrev qz150 := qz467

noncomputable def Ns528p1019 := @Enclosure.Real.IsNear.subLit_tf qz150 qz31 448650550122399 4503599627370496 3204619743 4503599627370496 1 16 

noncomputable abbrev qz468 := qz646

noncomputable abbrev qz151 := qz468

noncomputable def Ns528p1020 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz136 56707180193889 4503599627370496 587374047 4503599627370496 7530417 67108864 39 67108864 

noncomputable def Ns528p1021 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 7530417 67108864 39 67108864 7530417 67108864 39 67108864 56707180193889 4503599627370496 

noncomputable def Ns528p1022 := nat_lit 744555555948216388740402403764604482541159583720703714470147190625 

noncomputable def Ns528p1023 := nat_lit 476848139775781961589078576584836715114518105134563613750390625 

noncomputable def Ns528p1024 := nat_lit 2232712971565097602298029054140643774193249714951842016182940790625 

noncomputable def Ns528p1025 := BSN.cos_dyadic_bound_f 68359285 67108864 3 2 33554432 9000000 Ns528p1022 Ns528p226 Ns528p1023 Ns528p1024 Ns528p229 Ns528p1023 17600323 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 68359285) qz383 0 2 Ns528p1022 Ns528p226 Ns528p1023 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 68359285) (BSN.cosOddQ 67108864) 0 2 Ns528p1024 Ns528p229 Ns528p1023 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1026 := @Ns528p1013 2776108864 603979776000000 17600323 33554432 43376701 9437184000000 (@Ns528p1014 301 67108864 Bool.false 17600323 33554432 1 9000000 (@Ns528p1017 Ns528p220 68359285 67108864 301 67108864 (@Ns528p1018 4503599627370496 3204619743 4503599627370496 Ns528p1015 Ns528p217 Ns528p1016 Ns528p220 RS529to540.d55 (@Ns528p1019 0 1 11682008429328880 730125526833055 4503599627370496 3204619743 4503599627370496 (@Ns528p1020 30108428751689257844736 448650550122399 4503599627370496 3204619743 4503599627370496 (@Ns528p1021 587374047 4503599627370496 (Ns528p1006 rfl rfl) (Ns528p1006 rfl rfl) rfl) (Ns528p1006 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 68359285 67108864) (BSN.cos_neg_of_bound 68359285 67108864 Bool.false 17600323 33554432 1 9000000 (Ns528p1025 rfl rfl)) rfl rfl) 

noncomputable def Ns528p1027 := @Ns528p992 323288966159812189047 Ns528p909 (Ns528p993 qz33 (@Enclosure.Real.IsNear.of_eq qz135 (@Inv.inv Real Real.instInv (Real.sqrt qz144)) Bool.false 9641357 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz143 (BSN.t_div_two_pi_nonneg qz134 921779 1000 qz137)) Ns528p997) rfl) (@Ns528p998 562949953421312 66560266418443 7036874417766400000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 921779 1000 12 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 921779 1000 12 qz137 rfl rfl rfl))) (@Ns528p999 33554432 17600323 33554432 43376701 9437184000000 387726016323009 562949953421312 66560266418443 7036874417766400000 (@Ns528p1000 33554432 (Ns528p1012 rfl rfl rfl rfl rfl) rfl) (Ns528p1026 rfl) rfl)) 

noncomputable def Ns528p1028 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 37772037226298547322957 18889465931478580854784 124633193993212151389047 Ns528p909 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz135) (Zeta.RiemannSiegel.correction qz136))) Bool.true 37772037226298547322957 18889465931478580854784 124633193993212151389047 Ns528p909 (BSN.hardyZApproximantRS₀_eq qz134 12 (@BSN.floor_sqrt_eq_dec qz134 921779 1000 12 qz137 rfl rfl rfl)) (@Ns528p911 37772037226298547322957 18889465931478580854784 124633193993212151389047 Ns528p909 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12)) Bool.true 241824923 134217728 35331 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (Ns528p991 (Ns528p990 rfl rfl rfl rfl) rfl rfl)) (Ns528p1027 rfl) rfl rfl)) 

theorem RS529to540.d65 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 37772037226298547322957 18889465931478580854784 124633193993212151389047 Ns528p909 := Ns528p1028 

noncomputable def Ns528p1029 := nat_lit 4493419439924267262411377 

noncomputable def Ns528p1030 := nat_lit 4250129834582680692326400000 

noncomputable def Ns528p1031 := nat_lit 29170164812287670238348402753536 

noncomputable abbrev qz746 := (Enclosure.sfrac Bool.false 923038 1000)

noncomputable abbrev qz647 := qz746

noncomputable abbrev qz469 := qz647

noncomputable abbrev qz152 := qz469

noncomputable abbrev qz747 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 923038 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz648 := qz747

noncomputable abbrev qz470 := qz648

noncomputable abbrev qz153 := (@HPow.hPow Real Real Real qz356 qz470 qz358)

noncomputable abbrev qz748 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 923038 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz649 := qz748

noncomputable abbrev qz471 := qz649

noncomputable abbrev qz154 := qz471

noncomputable def Ns528p1032 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz153) (Zeta.RiemannSiegel.correction qz154)) 245027263 268435456 141517 134217728 29270754313051206772875 151115727451828646838272 12151333518552932811377 Ns528p1030 Ns528p1031 

noncomputable def Ns528p1033 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos BSN.quadSignPos 11 12 923038 1000 288 536870912 268435456 9007199254740992 Bool.false 988364722190 4506 1334074092 61 154981288 8 

noncomputable def Ns528p1034 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 923038 1000 181 237 536870912 268435456 9007199254740992 Bool.false 988364722190 4506 

noncomputable def Ns528p1035 := Ns528p1034 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.false 127384286 227884 Bool.true 46516421 Bool.true 52059560 28296951008113761 1 Bool.false 46458242 Bool.true Bool.false 51978013 Bool.true Bool.false 97020939 

noncomputable def Ns528p1036 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 923038 1000 49 119 536870912 268435456 9007199254740992 Bool.false 988364722190 4506 

noncomputable def Ns528p1037 := Ns528p1036 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.false 276277004 186094 Bool.true 784789671 Bool.true 120385672 28296951008113761 1 Bool.false 533684106 Bool.true Bool.false 119379339 Bool.false Bool.false 127384286 

noncomputable def Ns528p1038 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 923038 1000 119 28 536870912 268435456 9007199254740992 Bool.false 988364722190 4506 

noncomputable def Ns528p1039 := Ns528p1038 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.false 100542617 138264 Bool.false 99819449 Bool.false 451762167 28296951008113761 1 Bool.false 99245327 Bool.false Bool.false 357752272 Bool.false Bool.false 276277004 

noncomputable def Ns528p1040 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 923038 1000 357 226 536870912 268435456 9007199254740992 Bool.false 988364722190 4506 

noncomputable def Ns528p1041 := Ns528p1040 744261104 60 268435448 8 864060384 60 240095976 8 Bool.false 472351005 81517 Bool.false 320037493 Bool.false 214995887 28296951008113761 1 Bool.false 301416968 Bool.true Bool.false 494394413 Bool.true Bool.false 100542617 

noncomputable def Ns528p1042 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 923038 1000 764 526 536870912 268435456 9007199254740992 Bool.false 988364722190 4506 

noncomputable def Ns528p1043 := Ns528p1042 372130544 60 379625064 8 589812976 60 309962568 8 Bool.false 536870832 4572 Bool.false 581538726 Bool.false 361317912 28296951008113761 1 Bool.false 251525867 Bool.false Bool.false 419806631 Bool.true Bool.false 472351005 

noncomputable def Ns528p1044 := nat_lit 1442173572674655198675487708127673009657647570021041863149 

noncomputable def Ns528p1045 := nat_lit 783375836713295612614140699562597288330246716653568000 

noncomputable def Ns528p1046 := nat_lit 321617345577932722801478788080640000 

noncomputable def Ns528p1047 := nat_lit 1781190432469192302537841668623962705920 

noncomputable abbrev qz650 := (@Eq.refl Real qz746)

noncomputable abbrev qz472 := qz650

noncomputable abbrev qz155 := qz472

noncomputable def Ns528p1048 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 923038 1000 3407997597776 16000000 1846076 4000 2000 Ns528p1046 Ns528p1047 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p1049 := nat_lit 29535714768376938468873988262454743237788622234030937357291520 

noncomputable abbrev qz651 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1846076))))

noncomputable abbrev qz473 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 923038 4000) (Real.log (Enclosure.sfrac Bool.false 3407997597776 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz651))

noncomputable abbrev qz652 := (Enclosure.sfrac Bool.false 923038 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz473 qz652) (@HMul.hMul Real Real Real qz355 qz652 (Real.log Real.pi)))

noncomputable def Ns528p1050 := @Enclosure.Real.IsNear.addLit_ft_p qz156 (Enclosure.sfrac Bool.true Ns528p1046 Ns528p1047) 16582010057343662168681 9007199254740992000 206208651660591899 24576000000000000000000 Ns528p1046 Ns528p1047 0 1 Ns528p1049 

noncomputable def Ns528p1051 := nat_lit 111279985778490802573995828838400 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz361 qz473 qz652)

noncomputable def Ns528p1052 := @Enclosure.Real.IsNear.subLit_ff_p qz157 (@HMul.hMul Real Real Real qz5 qz652 (Real.log Real.pi)) 4268128968870049010197 1801439850948198400 19396648538219 6000000000000000000 17727296005959 33554432000 1384557 268435456000 Ns528p1051 16582010057343662168681 9007199254740992000 

noncomputable def Ns528p1053 := nat_lit 42681289688700490101970000 

noncomputable abbrev qz158 := qz473

noncomputable def Ns528p1054 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz652 25497638437199052937833 9007199254740992000 19396648538219 6000000000000000000 923038 2000 0 1 Ns528p1053 4268128968870049010197 1801439850948198400 19396648538219 6000000000000000000 

noncomputable def Ns528p1055 := nat_lit 57415577482298645393003226652773187584 

noncomputable def Ns528p1056 := nat_lit 118658939051286849111719936 

noncomputable def Ns528p1057 := nat_lit 104712215046722551441781763546041701779823254024881563344509059446367348275418335925111013267162029599283438726397589925881939172369350232063215359326169333760 

noncomputable def Ns528p1058 := nat_lit 2049152297164595999537388323511239781217437312651778198902303358263025242749581581407225450019315913490312237296163671061978962871934580564892604342491676672 

noncomputable def Ns528p1059 := nat_lit 267573421825556378590625619181151385774850469047265416024605901897786657444149724240287524854010197719277352782631304570332666781759760537270899179520 

noncomputable def Ns528p1060 := BSN.log_dyadic_bound 1310845597776 5505149597776 7 6 Ns528p1057 268435456 72000000 Ns528p1058 Ns528p1059 130337404 6815995195552 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1310845597776) (BSN.artanhQ 5505149597776) 0 6 Ns528p1058 Ns528p1057 Ns528p1059 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz474 := (Real.log (Enclosure.sfrac Bool.false 3407997597776 16000000))

noncomputable def Ns528p1061 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 923038 4000) qz474 923038 4000 0 1 55254874309192807 4503599627370496 125000153 9000000000000000 25501174336304355093833 9007199254740992000 57689945612407 18000000000000000000 (Enclosure.Real.IsNear.const Bool.false 923038 4000) (BSN.isNear_log_sfrac 3407997597776 16000000 55254874309192807 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3407997597776) qz364)) Bool.false Ns528p1056 Ns528p113 1000001224000000 72000000000000000000000 55254874309192807 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3407997597776 16000000 17 6815995195552 4194304000000 130337404 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p1060 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p1062 := BSN.arctan_dyadic_bound_f 1000 1846076 1 0 33554432 9000000 0 1 1 0 1 1 18176 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1846076) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1846076) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns528p1063 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1846076))) 884279719003555 562949953421312 1 2000000000000000 18176 33554432 1 9000000 29661271521930508238848 883974776325539 562949953421312 2000000009 18000000000000000 qz15 (Ns528p1062 rfl) rfl rfl 

noncomputable abbrev qz475 := (@HMul.hMul Real Real Real qz577 qz582 qz651)

noncomputable abbrev qz159 := qz475

noncomputable abbrev qz476 := qz651

noncomputable abbrev qz160 := qz476

noncomputable def Ns528p1064 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 923038 4000) qz474) qz159 25501174336304355093833 9007199254740992000 57689945612407 18000000000000000000 883974776325539 2251799813685248 2000000009 72000000000000000 Ns528p1055 25497638437199052937833 9007199254740992000 19396648538219 6000000000000000000 (Ns528p1061 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz160 1 4 0 1 883974776325539 562949953421312 2000000009 18000000000000000 883974776325539 2251799813685248 2000000009 72000000000000000 qz372 Ns528p1063 rfl) 

noncomputable def Ns528p1065 := @Ns528p1050 Ns528p1044 Ns528p1045 206208651660591899 24576000000000000000000 (@Ns528p1052 206208651660591899 24576000000000000000000 (Ns528p1054 (Ns528p1064 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 923038 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz652 (Real.log Real.pi) 923038 2000 0 1 38410761 33554432 3 268435456 17727296005959 33554432000 1384557 268435456000 (Enclosure.Real.IsNear.const Bool.false 923038 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p1046 Ns528p1047) 

noncomputable def Ns528p1066 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns528p1044 Ns528p1045 206208651660591899 24576000000000000000000 123545590273 67108864 141 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz373 qz156 (Enclosure.sfrac Bool.true Ns528p1046 Ns528p1047)) Bool.false Ns528p1044 Ns528p1045 206208651660591899 24576000000000000000000 Ns528p1048 (Ns528p1065 rfl rfl)) 

noncomputable def Ns528p1067 := nat_lit 15186591623415586971713536 

noncomputable def Ns528p1068 := nat_lit 14360594467845958170837938805583923178187223600528757784026008742980548013259578125071803648432196818878324645460295864032415295982404614500241 

noncomputable def Ns528p1069 := nat_lit 10208599579061576914068574941018464866043150310428761796002042421413280041641449986375331295508649525406894694836489141328982340254052241 

noncomputable def Ns528p1070 := nat_lit 71713870623889728775298383957753508965167785924750980797355868830416485952857168755960280067320533236655041204956153630871009800234907040755601 

noncomputable def Ns528p1071 := BSN.sin_dyadic_bound_f 215814447179 137438953472 4 3 67108864 18017579 Ns528p1068 Ns528p687 Ns528p1069 Ns528p1070 Ns528p690 Ns528p1069 67108854 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215814447179) (BSN.sinEvenQ 137438953472) 0 3 Ns528p1068 Ns528p687 Ns528p1069 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215814447179) (BSN.sinOddQ 137438953472) 0 3 Ns528p1070 Ns528p690 Ns528p1069 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1072 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123545590273) qz19) Bool.false 123545590273 67108864 141 16777216 Bool.false 67108854 67108864 1 9000000 (Ns528p1066 rfl) (Enclosure.sfrac_false_div 123545590273 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123545590273) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns528p1067) qz374) 226375608064910080 72057594037927936 Bool.false 67108854 67108864 292 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q3 123545590273 67108864 226375608064910080 72057594037927936 292 Ns528p1067 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108854 67108864 Ns528p1067 Ns528p113 215814447179 137438953472 18017579 18000000 (Ns528p1071 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p1073 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns528p1044 Ns528p1045 206208651660591899 24576000000000000000000 988364722190 536870912 4506 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz373 qz156 (Enclosure.sfrac Bool.true Ns528p1046 Ns528p1047)) Bool.false Ns528p1044 Ns528p1045 206208651660591899 24576000000000000000000 Ns528p1048 (Ns528p1065 rfl rfl)) 

noncomputable def Ns528p1074 := Ns528p1043 81517 BSN.abs_quadSignPos (BSN.cos_quad_nat0 764 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 251525867 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 526 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 419806631 536870912) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 33554427 33554432 20090269 2359296000000 536870832 536870912 4572 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 33554427 33554432 20090269 2359296000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 67108854 67108864 1285777216 150994944000000 33554427 33554432 20090269 2359296000000 (Ns528p1072 rfl rfl) rfl)) rfl) (Ns528p1073 rfl) RS529to540.d7 

noncomputable def Ns528p1075 := nat_lit 15767217554002037626258337705585573488178365486233346667861306898038876068454959717495355248631671522649626054656 

noncomputable def Ns528p1076 := nat_lit 1496041663178311667864527920193746154333193407317478558172031857405216534997178412164789776977162767896576 

noncomputable def Ns528p1077 := nat_lit 95602231944975363688602421326716371990610735405077425974386330191508546718988403055492218661946479475026319052800 

noncomputable def Ns528p1078 := BSN.cos_dyadic_bound_f 581538726 536870912 4 3 536870912 268435456 Ns528p1075 Ns528p145 Ns528p1076 Ns528p1077 Ns528p148 Ns528p1076 251525867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 581538726) qz20 0 3 Ns528p1075 Ns528p145 Ns528p1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 581538726) qz377 0 3 Ns528p1077 Ns528p148 Ns528p1076 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1079 := nat_lit 2379029223162093062825050906446990062942113232953756763465895174865944576 

noncomputable def Ns528p1080 := nat_lit 290479798590664041545264191722853577462628946528413528574597892407296 

noncomputable def Ns528p1081 := nat_lit 7136506709889097860392062190957524481671414440968213463340536328813019136 

noncomputable def Ns528p1082 := BSN.cos_dyadic_bound_f 361317912 536870912 3 2 536870912 268435456 Ns528p1079 Ns528p165 Ns528p1080 Ns528p1081 Ns528p168 Ns528p1080 419806631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 361317912) qz20 0 2 Ns528p1079 Ns528p165 Ns528p1080 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 361317912) qz377 0 2 Ns528p1081 Ns528p168 Ns528p1080 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1083 := nat_lit 2635620383988964090080320273357911758307977680509790740229381964709863265 

noncomputable def Ns528p1084 := nat_lit 110054265023957248025014223357821329923192099077186401264412237864801 

noncomputable def Ns528p1085 := nat_lit 6902637108303914781332607835766237180081970661746184113093953240140717921 

noncomputable def Ns528p1086 := BSN.sin_dyadic_bound_f 320037493 536870912 3 2 536870912 268435456 Ns528p1083 Ns528p180 Ns528p1084 Ns528p1085 Ns528p183 Ns528p1084 301416968 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 320037493) qz375 0 2 Ns528p1083 Ns528p180 Ns528p1084 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 320037493) qz376 0 2 Ns528p1085 Ns528p183 Ns528p1084 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1087 := nat_lit 298205764109924560048571098864128627419087401919671009142915950867881601 

noncomputable def Ns528p1088 := nat_lit 4565004536503878050283074649006051230606047570365293106734955208321 

noncomputable def Ns528p1089 := nat_lit 894608162320700672389612730443087870154800993663872296842534382693228161 

noncomputable def Ns528p1090 := BSN.cos_dyadic_bound_f 214995887 536870912 3 2 536870912 268435456 Ns528p1087 Ns528p165 Ns528p1088 Ns528p1089 Ns528p168 Ns528p1088 494394413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 214995887) qz20 0 2 Ns528p1087 Ns528p165 Ns528p1088 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 214995887) qz377 0 2 Ns528p1089 Ns528p168 Ns528p1088 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1091 := Ns528p1041 138264 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 357 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 301416968 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 226 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 494394413 536870912) qz155 rfl rfl (Ns528p1074 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p1078 rfl rfl) (Ns528p1082 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p1073 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p1086 rfl rfl) (Ns528p1090 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p1092 := nat_lit 99279749566590208138910762287201 

noncomputable def Ns528p1093 := BSN.sin_dyadic_bound_f 99819449 536870912 2 1 536870912 268435456 Ns528p1092 Ns528p160 Ns528p1092 Ns528p1092 Ns528p161 Ns528p1092 99245327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 99819449) qz375 0 1 Ns528p1092 Ns528p160 Ns528p1092 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 99819449) qz376 0 1 Ns528p1092 Ns528p161 Ns528p1092 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1094 := nat_lit 5815108202755127386369886431804145012419216151269271438545531700942477121 

noncomputable def Ns528p1095 := nat_lit 1734917643081657045469214331793347687472674804074714881348813278943041 

noncomputable def Ns528p1096 := nat_lit 17441854772979218845018720866748848341882703104199664885873897476269545281 

noncomputable def Ns528p1097 := BSN.cos_dyadic_bound_f 451762167 536870912 3 2 536870912 268435456 Ns528p1094 Ns528p165 Ns528p1095 Ns528p1096 Ns528p168 Ns528p1095 357752272 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 451762167) qz20 0 2 Ns528p1094 Ns528p165 Ns528p1095 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 451762167) qz377 0 2 Ns528p1096 Ns528p168 Ns528p1095 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1098 := Ns528p1039 186094 BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 99245327 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 357752272 536870912) qz155 rfl rfl (Ns528p1091 rfl rfl) (Ns528p1073 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p1093 rfl rfl) (Ns528p1097 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1099 := nat_lit 136058790065097558328180515257528538418388912170852108900670287859158913243962344928496397001462068358390143892641 

noncomputable def Ns528p1100 := nat_lit 54580730182182218243614537440624316850778688813020717452383472570777944929003440108623978554331965925473441 

noncomputable def Ns528p1101 := nat_lit 679659702831220020020730370864474567704358522837021336754629406132103527482224098420394343425852106559880837053601 

noncomputable def Ns528p1102 := BSN.sin_dyadic_bound_f 784789671 536870912 4 3 536870912 268435456 Ns528p1099 Ns528p135 Ns528p1100 Ns528p1101 Ns528p138 Ns528p1100 533684106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 784789671) qz375 0 3 Ns528p1099 Ns528p135 Ns528p1100 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 784789671) qz376 0 3 Ns528p1101 Ns528p138 Ns528p1100 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1103 := nat_lit 210038643807622177229304618029056 

noncomputable def Ns528p1104 := BSN.sin_dyadic_bound_f 120385672 536870912 2 1 536870912 268435456 Ns528p1103 Ns528p160 Ns528p1103 Ns528p1103 Ns528p161 Ns528p1103 119379339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 120385672) qz375 0 1 Ns528p1103 Ns528p160 Ns528p1103 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 120385672) qz376 0 1 Ns528p1103 Ns528p161 Ns528p1103 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1105 := Ns528p1037 227884 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533684106 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 119379339 536870912) qz155 rfl rfl (Ns528p1098 rfl) (Ns528p1073 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p1102 rfl rfl) (Ns528p1104 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1106 := nat_lit 4681932734766592118894917876081 

noncomputable def Ns528p1107 := BSN.sin_dyadic_bound_f 46516421 536870912 2 1 536870912 268435456 Ns528p1106 Ns528p160 Ns528p1106 Ns528p1106 Ns528p161 Ns528p1106 46458242 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 46516421) qz375 0 1 Ns528p1106 Ns528p160 Ns528p1106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 46516421) qz376 0 1 Ns528p1106 Ns528p161 Ns528p1106 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1108 := nat_lit 7345172046793165067081320960000 

noncomputable def Ns528p1109 := BSN.sin_dyadic_bound_f 52059560 536870912 2 1 536870912 268435456 Ns528p1108 Ns528p160 Ns528p1108 Ns528p1108 Ns528p161 Ns528p1108 51978013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 52059560) qz375 0 1 Ns528p1108 Ns528p160 Ns528p1108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 52059560) qz376 0 1 Ns528p1108 Ns528p161 Ns528p1108 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1110 := Ns528p1035 265469 BSN.abs_quadSignNeg qz601 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 46458242 536870912) BSN.abs_quadSignNeg qz590 (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51978013 536870912) qz155 rfl rfl (Ns528p1105 rfl) (Ns528p1073 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p1107 rfl rfl) (Ns528p1109 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1111 := nat_lit 95372978831639166022536538929244708168126344308636561011969011916800000 

noncomputable def Ns528p1112 := nat_lit 466948392468943381845407252175237157786236225805931048985600000000 

noncomputable def Ns528p1113 := nat_lit 286118002598132560180845925973229774030063460453458071173809064550400000 

noncomputable def Ns528p1114 := BSN.cos_dyadic_bound_f 161680860 536870912 3 2 536870912 268435456 Ns528p1111 Ns528p165 Ns528p1112 Ns528p1113 Ns528p168 Ns528p1112 512708930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 161680860) qz20 0 2 Ns528p1111 Ns528p165 Ns528p1112 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 161680860) qz377 0 2 Ns528p1113 Ns528p168 Ns528p1112 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1115 := Ns528p1033 Bool.false 97020939 265469 Bool.true 161680860 28296951008113761 1 Bool.false 512708930 Bool.false Bool.false 245027263 283034 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 512708930 536870912) qz155 rfl (Ns528p1110 rfl) (Ns528p1073 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p1114 rfl rfl) rfl 

noncomputable def Ns528p1116 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) 245027263 536870912 283034 536870912 245027263 536870912 283034 536870912 263096020303347712 245027263 268435456 141517 134217728 (Ns528p1115 rfl rfl rfl rfl) 

noncomputable def Ns528p1117 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz5 qz6 qz153) (Zeta.RiemannSiegel.correction qz154) 19276135 67108864 1 67108864 1518497059345725 2251799813685248 628166650658557 63331869759897600000 29270754313051206772875 151115727451828646838272 

noncomputable def Ns528p1118 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz153 1 1 0 1 19276135 67108864 1 67108864 19276135 67108864 1 67108864 

noncomputable abbrev qz161 := qz470

noncomputable def Ns528p1119 := @Enclosure.Real.IsNear.sqrt_image qz161 4929349213933 33554432000 461519 33554432000 406695829 406695868 33554432 (@Enclosure.Real.IsNear.of_eq qz161 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 4929349213933 33554432000 461519 33554432000 (BSN.t_div_two_pi_mk qz152 923038 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 923038 1000 0 1 10680707 67108864 1 67108864 4929349213933 33554432000 461519 33554432000 (Enclosure.Real.IsNear.const Bool.false 923038 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz749 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 923038 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz653 := qz749

noncomputable abbrev qz477 := qz653

noncomputable abbrev qz162 := qz477

noncomputable def Ns528p1120 := @Enclosure.Real.IsNear.sqrt_image qz162 813391697 67108864 39 67108864 116818010 116818016 33554432 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 813391697 67108864 39 67108864 813391697 67108864 39 67108864 (Ns528p1119 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p1121 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz162) 116818013 33554432 3 33554432 9638067 9638068 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz162) Bool.false 233636026 67108864 6 67108864 116818013 33554432 3 33554432 (Ns528p1120 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p1122 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz162)) Bool.false 19276135 67108864 1 67108864 19276135 67108864 1 67108864 (Ns528p1121 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz471))

noncomputable abbrev qz654 := (@HMul.hMul Real Real Real qz713 qz748 qz748)

noncomputable abbrev qz478 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz654 qz649) qz594)

noncomputable abbrev qz164 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz478))

noncomputable def Ns528p1123 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz163) qz164) Bool.false 1518497059345725 

noncomputable def Ns528p1124 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz163) qz164 92322339 67108864 481 

noncomputable def Ns528p1125 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz163) Bool.false 92322339 67108864 481 67108864 92322339 67108864 481 

noncomputable def Ns528p1126 := @Enclosure.Real.IsNear.recentre' qz163 Bool.false 24390628 33554432 1140554432 301989888000000 6097657 8388608 17821163 4718592000000 

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz355 qz352 qz471)

noncomputable def Ns528p1127 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12700405) qz622) Bool.false 12700405 16777216 123 33554432 Bool.false 24390628 33554432 1 

noncomputable def Ns528p1128 := nat_lit 1052456941022170220016390481 

noncomputable def Ns528p1129 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 8085329 67108864 39 67108864 7149692456171294344595 9444732965739290427392 Ns528p1128 

noncomputable def Ns528p1130 := @Enclosure.Real.IsNear.subLit_ff_p qz162 qz1 813391697 67108864 39 67108864 12 1 0 1 8085329 8085329 67108864 39 

noncomputable def Ns528p1131 := @Ns528p1130 67108864 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 813391697 67108864 39 67108864 813391697 67108864 39 67108864 (Ns528p1119 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p1132 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 7149692456171294344595 9444732965739290427392 Ns528p1128 Ns528p330 12700405 16777216 123 33554432 (@Ns528p1129 Ns528p330 RS529to540.d55 (Ns528p1131 rfl rfl) rfl) 

noncomputable def Ns528p1133 := nat_lit 3463729991827947707690528131269289769099432379468006419190625 

noncomputable def Ns528p1134 := nat_lit 676925013460497073343627292128892560610411639207750390625 

noncomputable def Ns528p1135 := nat_lit 10389836125456922128924897139223611522177076315125603756790625 

noncomputable def Ns528p1136 := BSN.cos_dyadic_bound_f 12700405 16777216 3 2 33554432 9000000 Ns528p1133 Ns528p624 Ns528p1134 Ns528p1135 Ns528p627 Ns528p1134 24390628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 12700405) (BSN.cosEvenQ 16777216) 0 2 Ns528p1133 Ns528p624 Ns528p1134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 12700405) (BSN.cosOddQ 16777216) 0 2 Ns528p1135 Ns528p627 Ns528p1134 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1137 := @Enclosure.Real.IsNear.inv_image qz163 6097657 8388608 17821163 4718592000000 46160929 46161410 33554432 (Ns528p1126 (@Ns528p1127 9000000 (Ns528p1132 rfl) (Enclosure.sfrac_false_div 12700405 16777216) (Ns528p1136 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p1138 := @Enclosure.Real.IsNear.recentre' qz164 Bool.false 16447775 33554432 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz355 qz352 qz478)

noncomputable def Ns528p1139 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 35517295)) qz415) Bool.true 35517295 33554432 

noncomputable def Ns528p1140 := nat_lit 670902736238293433271375425405 

noncomputable def Ns528p1141 := nat_lit 3505926080818497538513961363929729 

noncomputable def Ns528p1142 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns528p1140 Ns528p217 Ns528p1141 

noncomputable def Ns528p1143 := nat_lit 773712524553362671811952640000000000000 

noncomputable abbrev qz167 := qz478

noncomputable def Ns528p1144 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 758699675928671 

noncomputable abbrev qz479 := (@HSub.hSub Real Real Real qz581 qz654 qz649)

noncomputable abbrev qz168 := qz479

noncomputable def Ns528p1145 := @Enclosure.Real.IsNear.subLit_tf qz168 qz31 477224699218015 4503599627370496 3247902879 4503599627370496 1 16 

noncomputable abbrev qz480 := qz654

noncomputable abbrev qz169 := qz480

noncomputable def Ns528p1146 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz154 65372545038241 4503599627370496 630657183 4503599627370496 8085329 67108864 39 67108864 

noncomputable def Ns528p1147 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 8085329 67108864 39 67108864 8085329 67108864 39 67108864 65372545038241 4503599627370496 

noncomputable def Ns528p1148 := nat_lit 3391507423125237411376805231276901195451172628162753135555690625 

noncomputable def Ns528p1149 := nat_lit 2532322767895800524112158871920021717911449333233891062890625 

noncomputable def Ns528p1150 := nat_lit 10169457623839920633082191376086863542917694985821791624541290625 

noncomputable def Ns528p1151 := BSN.cos_dyadic_bound_f 35517295 33554432 3 2 33554432 9000000 Ns528p1148 Ns528p887 Ns528p1149 Ns528p1150 Ns528p890 Ns528p1149 16447775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 35517295) (BSN.cosEvenQ 33554432) 0 2 Ns528p1148 Ns528p887 Ns528p1149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 35517295) (BSN.cosOddQ 33554432) 0 2 Ns528p1150 Ns528p890 Ns528p1149 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1152 := @Ns528p1138 2812108864 603979776000000 16447775 33554432 43939201 9437184000000 (@Ns528p1139 305 67108864 Bool.false 16447775 33554432 1 9000000 (@Ns528p1142 Ns528p1143 35517295 33554432 305 67108864 (@Ns528p1144 4503599627370496 3247902879 4503599627370496 Ns528p1140 Ns528p217 Ns528p1141 Ns528p1143 RS529to540.d55 (@Ns528p1145 0 1 12139194814858736 758699675928671 4503599627370496 3247902879 4503599627370496 (@Ns528p1146 32026007437262674984960 477224699218015 4503599627370496 3247902879 4503599627370496 (@Ns528p1147 630657183 4503599627370496 (Ns528p1131 rfl rfl) (Ns528p1131 rfl rfl) rfl) (Ns528p1131 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 35517295 33554432) (BSN.cos_neg_of_bound 35517295 33554432 Bool.false 16447775 33554432 1 9000000 (Ns528p1151 rfl rfl)) rfl rfl) 

noncomputable def Ns528p1153 := @Ns528p1117 12151333518552932811377 Ns528p1030 (Ns528p1118 qz33 (@Enclosure.Real.IsNear.of_eq qz153 (@Inv.inv Real Real.instInv (Real.sqrt qz162)) Bool.false 19276135 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz161 (BSN.t_div_two_pi_nonneg qz152 923038 1000 qz155)) Ns528p1122) rfl) (@Ns528p1123 2251799813685248 628166650658557 63331869759897600000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 923038 1000 12 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 923038 1000 12 qz155 rfl rfl rfl))) (@Ns528p1124 67108864 16447775 33554432 43939201 9437184000000 1518497059345725 2251799813685248 628166650658557 63331869759897600000 (@Ns528p1125 67108864 (Ns528p1137 rfl rfl rfl rfl rfl) rfl) (Ns528p1152 rfl) rfl)) 

noncomputable def Ns528p1154 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 108667331979750358456181 151115727451828646838272 Ns528p1029 Ns528p1030 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HMul.hMul Real Real Real qz5 (@HMul.hMul Real Real Real qz5 qz6 qz153) (Zeta.RiemannSiegel.correction qz154))) Bool.false 108667331979750358456181 151115727451828646838272 Ns528p1029 Ns528p1030 (BSN.hardyZApproximantRS₀_eq qz152 12 (@BSN.floor_sqrt_eq_dec qz152 923038 1000 12 qz155 rfl rfl rfl)) (@Ns528p1032 108667331979750358456181 151115727451828646838272 Ns528p1029 Ns528p1030 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12)) Bool.false 245027263 268435456 141517 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (Ns528p1116 (Ns528p1115 rfl rfl rfl rfl) rfl rfl)) (Ns528p1153 rfl) rfl rfl)) 

theorem RS529to540.d66 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 108667331979750358456181 151115727451828646838272 Ns528p1029 Ns528p1030 := Ns528p1154 

noncomputable def Ns528p1155 := nat_lit 14443871815642915298959425536 

noncomputable abbrev qz750 := (Enclosure.sfrac Bool.false 924297 1000)

noncomputable abbrev qz655 := qz750

noncomputable abbrev qz481 := qz655

noncomputable abbrev qz170 := qz481

noncomputable abbrev qz171 := qz356

noncomputable abbrev qz751 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 924297 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz656 := qz751

noncomputable abbrev qz482 := qz656

noncomputable abbrev qz172 := qz482

noncomputable abbrev qz173 := qz358

noncomputable abbrev qz752 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 924297 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz657 := qz752

noncomputable abbrev qz483 := qz657

noncomputable abbrev qz174 := qz483

noncomputable abbrev qz658 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz171 qz172 qz173))

noncomputable def Ns528p1156 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HMul.hMul Real Real Real qz5 qz658 (Zeta.RiemannSiegel.correction qz174)) 5719557 2097152 283423 268435456 447726096540301138975 2361183241434822606848 356636040740604170121 Ns528p909 Ns528p1155 

noncomputable def Ns528p1157 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos BSN.quadSignPos 11 12 924297 1000 288 536870912 268435456 9007199254740992 Bool.false 990051304350 4512 1334074092 61 154981288 8 

noncomputable def Ns528p1158 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 924297 1000 180 236 536870912 268435456 9007199254740992 Bool.false 990051304350 4512 

noncomputable def Ns528p1159 := Ns528p1158 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.true 911197730 228198 Bool.true 759613532 Bool.true 829578773 28296951008113761 1 Bool.false 83362653 Bool.false Bool.false 13734584 Bool.false Bool.true 880695011 

noncomputable def Ns528p1160 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 924297 1000 49 118 536870912 268435456 9007199254740992 Bool.false 990051304350 4512 

noncomputable def Ns528p1161 := Ns528p1160 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.true 731190586 186351 Bool.true 503744631 Bool.true 762267437 28296951008113761 1 Bool.false 433014743 Bool.true Bool.false 80739929 Bool.true Bool.true 911197730 

noncomputable def Ns528p1162 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 924297 1000 119 28 536870912 268435456 9007199254740992 Bool.false 990051304350 4512 

noncomputable def Ns528p1163 := Ns528p1162 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.true 931273666 138455 Bool.false 575314701 Bool.false 823063828 28296951008113761 1 Bool.false 471357089 Bool.false Bool.false 20246226 Bool.false Bool.true 731190586 

noncomputable def Ns528p1164 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 924297 1000 358 226 536870912 268435456 9007199254740992 Bool.false 990051304350 4512 

noncomputable def Ns528p1165 := Ns528p1164 744261104 60 268435448 8 864060384 60 240095976 8 Bool.true 673104603 81630 Bool.false 226280067 Bool.false 813726023 28296951008113761 1 Bool.false 489886478 Bool.true Bool.false 29573856 Bool.true Bool.true 931273666 

noncomputable def Ns528p1166 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 924297 1000 766 527 536870912 268435456 9007199254740992 Bool.false 990051304350 4512 

noncomputable def Ns528p1167 := Ns528p1166 372130544 60 379625064 8 589812976 60 309962568 8 Bool.true 536870800 4580 Bool.false 112978818 Bool.false 462010679 28296951008113761 1 Bool.false 525027117 Bool.true Bool.false 407060400 Bool.false Bool.true 673104603 

noncomputable def Ns528p1168 := nat_lit 20714632545553815963195647614363854146180623742674547177919 

noncomputable def Ns528p1169 := nat_lit 11232835730440259299478777739100351257446580786036736000 

noncomputable def Ns528p1170 := nat_lit 323816725318302989571016771803360000 

noncomputable def Ns528p1171 := nat_lit 1795817211806435652748863412353997427520 

noncomputable abbrev qz659 := (@Eq.refl Real qz750)

noncomputable abbrev qz484 := qz659

noncomputable abbrev qz175 := qz484

noncomputable def Ns528p1172 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 924297 1000 3417300776836 16000000 1848594 4000 2000 Ns528p1170 Ns528p1171 qz175 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p1173 := nat_lit 59658141731194989974003465129367899941000196378902695872406720 

noncomputable abbrev qz660 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1848594))))

noncomputable abbrev qz485 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 924297 4000) (Real.log (Enclosure.sfrac Bool.false 3417300776836 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz660))

noncomputable abbrev qz661 := (Enclosure.sfrac Bool.false 924297 2000)

noncomputable abbrev qz176 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz485 qz661) (@HMul.hMul Real Real Real qz355 qz661 (Real.log Real.pi)))

noncomputable def Ns528p1174 := @Enclosure.Real.IsNear.addLit_ft_p qz176 (Enclosure.sfrac Bool.true Ns528p1170 Ns528p1171) 33220612416643242447711 18014398509481984000 1238933902785754711 147456000000000000000000 Ns528p1170 Ns528p1171 0 1 Ns528p1173 

noncomputable def Ns528p1175 := nat_lit 2229397560665222693942464610304000 

noncomputable abbrev qz177 := (@HSub.hSub Real Real Real qz361 qz485 qz661)

noncomputable def Ns528p1176 := @Enclosure.Real.IsNear.subLit_ff_p qz177 (@HMul.hMul Real Real Real qz5 qz661 (Real.log Real.pi)) 42750863300628134810463 18014398509481984000 116537266421941 36000000000000000000 35502951160017 67108864000 2772891 536870912000 Ns528p1175 33220612416643242447711 18014398509481984000 

noncomputable def Ns528p1177 := nat_lit 85501726601256269620926000 

noncomputable abbrev qz178 := qz485

noncomputable def Ns528p1178 := @Enclosure.Real.IsNear.subLit_ff_p qz178 qz661 51076190550187469493087 18014398509481984000 116537266421941 36000000000000000000 924297 2000 0 1 Ns528p1177 42750863300628134810463 18014398509481984000 116537266421941 36000000000000000000 

noncomputable def Ns528p1179 := nat_lit 115013356364664368341611374487929880576 

noncomputable def Ns528p1180 := nat_lit 118685304168340589545259008 

noncomputable def Ns528p1181 := nat_lit 106855507121188362696205862928851207617015754175003186587889054542037978812987936287710705496250271882085271690082287201832641695381788071330308496592690216960 

noncomputable def Ns528p1182 := nat_lit 2114549107339087959204557879453082005074541232443404409095282081607247574789561032383906112521474316530633500552276236224770741981473878644546987839782387712 

noncomputable def Ns528p1183 := nat_lit 291272192955301421366416306602166962880157730701425310233244336972626040867146130820222397157919000879267764765143504493232530489610557479737800785920 

noncomputable def Ns528p1184 := BSN.log_dyadic_bound 1320148776836 5514452776836 7 6 Ns528p1181 268435456 72000000 Ns528p1182 Ns528p1183 131069183 6834601553672 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1320148776836) (BSN.artanhQ 5514452776836) 0 6 Ns528p1182 Ns528p1181 Ns528p1183 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz486 := (Real.log (Enclosure.sfrac Bool.false 3417300776836 16000000))

noncomputable def Ns528p1185 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 924297 4000) qz486 924297 4000 0 1 55267151523540071 4503599627370496 125000153 9000000000000000 51083262351753517005087 18014398509481984000 38512422139147 12000000000000000000 (Enclosure.Real.IsNear.const Bool.false 924297 4000) (BSN.isNear_log_sfrac 3417300776836 16000000 55267151523540071 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3417300776836) qz364)) Bool.false Ns528p1180 Ns528p113 1000001224000000 72000000000000000000000 55267151523540071 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3417300776836 16000000 17 6834601553672 4194304000000 131069183 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p1184 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p1186 := BSN.arctan_dyadic_bound_f 1000 1848594 1 0 33554432 9000000 0 1 1 0 1 1 18151 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1848594) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1848594) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns528p1187 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1848594))) 884279719003555 562949953421312 1 2000000000000000 18151 33554432 1 9000000 29661285595679343771648 883975195755939 562949953421312 2000000009 18000000000000000 qz15 (Ns528p1186 rfl) rfl rfl 

noncomputable abbrev qz487 := (@HMul.hMul Real Real Real qz577 qz582 qz660)

noncomputable abbrev qz179 := qz487

noncomputable abbrev qz488 := qz660

noncomputable abbrev qz180 := qz488

noncomputable def Ns528p1188 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 924297 4000) qz486) qz179 51083262351753517005087 18014398509481984000 38512422139147 12000000000000000000 883975195755939 2251799813685248 2000000009 72000000000000000 Ns528p1179 51076190550187469493087 18014398509481984000 116537266421941 36000000000000000000 (Ns528p1185 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz180 1 4 0 1 883975195755939 562949953421312 2000000009 18000000000000000 883975195755939 2251799813685248 2000000009 72000000000000000 qz372 Ns528p1187 rfl) 

noncomputable def Ns528p1189 := @Ns528p1174 Ns528p1168 Ns528p1169 1238933902785754711 147456000000000000000000 (@Ns528p1176 1238933902785754711 147456000000000000000000 (Ns528p1178 (Ns528p1188 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 924297 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz661 (Real.log Real.pi) 924297 2000 0 1 38410761 33554432 3 268435456 35502951160017 67108864000 2772891 536870912000 (Enclosure.Real.IsNear.const Bool.false 924297 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p1170 Ns528p1171) 

noncomputable def Ns528p1190 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns528p1168 Ns528p1169 1238933902785754711 147456000000000000000000 123756413043 67108864 565 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz373 qz176 (Enclosure.sfrac Bool.true Ns528p1170 Ns528p1171)) Bool.false Ns528p1168 Ns528p1169 1238933902785754711 147456000000000000000000 Ns528p1172 (Ns528p1189 rfl rfl)) 

noncomputable def Ns528p1191 := nat_lit 15185734983547784565620736 

noncomputable def Ns528p1192 := nat_lit 14357348048794098432081709112857179460625328940451062215044097656496620929479565339957507644461570718752693604456112439599120745092005194305536 

noncomputable def Ns528p1193 := nat_lit 10201691605577758025400644179929309524409590517859802905920496966260118356318662982406775920825089791169096456755639651257001263825883136 

noncomputable def Ns528p1194 := nat_lit 71697678738046054368260074157302528838972550324343733277568683850904482941823549151672267583267317025720005552829709302623549627046506238775296 

noncomputable def Ns528p1195 := BSN.sin_dyadic_bound_f 215802273594 137438953472 4 3 67108864 18017579 Ns528p1192 Ns528p687 Ns528p1193 Ns528p1194 Ns528p690 Ns528p1193 67108850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215802273594) (BSN.sinEvenQ 137438953472) 0 3 Ns528p1192 Ns528p687 Ns528p1193 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215802273594) (BSN.sinOddQ 137438953472) 0 3 Ns528p1194 Ns528p690 Ns528p1193 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1196 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123756413043) qz19) Bool.false 123756413043 67108864 565 67108864 Bool.true 67108850 67108864 1 9000000 (Ns528p1190 rfl) (Enclosure.sfrac_false_div 123756413043 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123756413043) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns528p1191) qz374) 226375608064910080 72057594037927936 Bool.false 67108850 67108864 293 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q1 123756413043 67108864 226375608064910080 72057594037927936 293 Ns528p1191 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108850 67108864 Ns528p1191 Ns528p113 215802273594 137438953472 18017579 18000000 (Ns528p1195 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p1197 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns528p1168 Ns528p1169 1238933902785754711 147456000000000000000000 990051304350 536870912 4512 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz373 qz176 (Enclosure.sfrac Bool.true Ns528p1170 Ns528p1171)) Bool.false Ns528p1168 Ns528p1169 1238933902785754711 147456000000000000000000 Ns528p1172 (Ns528p1189 rfl rfl)) 

noncomputable def Ns528p1198 := Ns528p1167 81630 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 766 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 525027117 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 527 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 407060400 536870912) qz175 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 33554425 33554432 80501701 9437184000000 536870800 536870912 4580 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 33554425 33554432 80501701 9437184000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 67108850 67108864 5152108864 603979776000000 33554425 33554432 80501701 9437184000000 (Ns528p1196 rfl rfl) rfl)) rfl) (Ns528p1197 rfl) RS529to540.d7 

noncomputable def Ns528p1199 := nat_lit 162925141593637626211224864911376 

noncomputable def Ns528p1200 := BSN.cos_dyadic_bound_f 112978818 536870912 2 1 536870912 268435456 Ns528p1199 Ns528p141 Ns528p1199 Ns528p1199 Ns528p142 Ns528p1199 525027117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 112978818) qz20 0 1 Ns528p1199 Ns528p141 Ns528p1199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 112978818) qz377 0 1 Ns528p1199 Ns528p142 Ns528p1199 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1201 := nat_lit 11448487056043780898064192790131761163728759288292906040049193159363534145 

noncomputable def Ns528p1202 := nat_lit 2075946286451710449850145050473388090229828863135263214092156711869761 

noncomputable def Ns528p1203 := nat_lit 29980771709936599582773128501215750895714949841655392059686975735085276481 

noncomputable def Ns528p1204 := BSN.sin_dyadic_bound_f 462010679 536870912 3 2 536870912 268435456 Ns528p1201 Ns528p180 Ns528p1202 Ns528p1203 Ns528p183 Ns528p1202 407060400 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 462010679) qz375 0 2 Ns528p1201 Ns528p180 Ns528p1202 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 462010679) qz376 0 2 Ns528p1203 Ns528p183 Ns528p1202 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1205 := nat_lit 365916616280792265832119812530287698759692467195335258407672730964194721 

noncomputable def Ns528p1206 := nat_lit 6873380544583166137622135423151229651359230419305870577796385076641 

noncomputable def Ns528p1207 := nat_lit 1097736102081287631164084193320016793819774683125167163481862600122430881 

noncomputable def Ns528p1208 := BSN.cos_dyadic_bound_f 226280067 536870912 3 2 536870912 268435456 Ns528p1205 Ns528p165 Ns528p1206 Ns528p1207 Ns528p168 Ns528p1206 489886478 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 226280067) qz20 0 2 Ns528p1205 Ns528p165 Ns528p1206 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 226280067) qz377 0 2 Ns528p1207 Ns528p168 Ns528p1206 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1209 := nat_lit 60584328308435063579305893670742797253169415696479544166679049273732948949494348820860961862227923651251400384801 

noncomputable def Ns528p1210 := nat_lit 84282703867515107164063202942337484122033277026359322416413671429970361476851213210641997280011367760044321 

noncomputable def Ns528p1211 := nat_lit 366777171088859592778215048324338099724830571955234042456371339535894081133425320182972025947816675533634729189665 

noncomputable def Ns528p1212 := BSN.cos_dyadic_bound_f 813726023 536870912 4 3 536870912 268435456 Ns528p1209 Ns528p145 Ns528p1210 Ns528p1211 Ns528p148 Ns528p1210 29573856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 813726023) qz20 0 3 Ns528p1209 Ns528p145 Ns528p1210 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 813726023) qz377 0 3 Ns528p1211 Ns528p148 Ns528p1210 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1213 := Ns528p1165 138455 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 358 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 489886478 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 226 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 29573856 536870912) qz175 rfl rfl (Ns528p1198 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p1200 rfl rfl) (Ns528p1204 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p1197 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p1208 rfl rfl) (Ns528p1212 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p1214 := nat_lit 27534203254649795076732561299585561029841961534674437717995465881203525665 

noncomputable def Ns528p1215 := nat_lit 12001727820450422991554291759002543243839895537199776328333025901037601 

noncomputable def Ns528p1216 := nat_lit 72093958107611591182789429788447608103381777521849013433075585742169458721 

noncomputable def Ns528p1217 := BSN.sin_dyadic_bound_f 575314701 536870912 3 2 536870912 268435456 Ns528p1214 Ns528p180 Ns528p1215 Ns528p1216 Ns528p183 Ns528p1215 471357089 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 575314701) qz375 0 2 Ns528p1214 Ns528p180 Ns528p1215 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 575314701) qz376 0 2 Ns528p1216 Ns528p183 Ns528p1215 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1218 := nat_lit 63422754985896660324587893070343505165874166366781410916184546392921572178917410054299073888248017578869701738496 

noncomputable def Ns528p1219 := nat_lit 96650073551297575625137923143908958518014993339748872513388208939192182220822523275723821354981857339375616 

noncomputable def Ns528p1220 := nat_lit 383923558942988876130668343691118566424525648669195962224027523830142554783835035270112247619080234295269345198080 

noncomputable def Ns528p1221 := BSN.cos_dyadic_bound_f 823063828 536870912 4 3 536870912 268435456 Ns528p1218 Ns528p145 Ns528p1219 Ns528p1220 Ns528p148 Ns528p1219 20246226 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 823063828) qz20 0 3 Ns528p1218 Ns528p145 Ns528p1219 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 823063828) qz377 0 3 Ns528p1220 Ns528p148 Ns528p1219 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1222 := Ns528p1163 186351 BSN.abs_quadSignPos (BSN.cos_quad_nat3 119 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 471357089 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 28 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 20246226 536870912) qz175 rfl rfl (Ns528p1213 rfl rfl) (Ns528p1197 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p1217 rfl rfl) (Ns528p1221 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1223 := nat_lit 16181333503905259454036321196980000797796521482506237425654533410567729985 

noncomputable def Ns528p1224 := nat_lit 4146516931572993552667297904983765669323682635738078891702017170322241 

noncomputable def Ns528p1225 := nat_lit 42372969578053132771009856081196695040288175063248950653746736618925437761 

noncomputable def Ns528p1226 := BSN.sin_dyadic_bound_f 503744631 536870912 3 2 536870912 268435456 Ns528p1223 Ns528p180 Ns528p1224 Ns528p1225 Ns528p183 Ns528p1224 433014743 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 503744631) qz375 0 2 Ns528p1223 Ns528p180 Ns528p1224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 503744631) qz376 0 2 Ns528p1225 Ns528p183 Ns528p1224 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1227 := nat_lit 46619095934775386514072696057409827611182336676548530244746296155580508398201806011948720130804532629139008941361 

noncomputable def Ns528p1228 := nat_lit 38484727213677290147166161786213740137265831982908427626434210148596469363247110325609589137983938219109681 

noncomputable def Ns528p1229 := nat_lit 282367317879055439599863727863171194938185973653967603429550433783997518973056949560696339257906126581133833825585 

noncomputable def Ns528p1230 := BSN.cos_dyadic_bound_f 762267437 536870912 4 3 536870912 268435456 Ns528p1227 Ns528p145 Ns528p1228 Ns528p1229 Ns528p148 Ns528p1228 80739929 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 762267437) qz20 0 3 Ns528p1227 Ns528p145 Ns528p1228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 762267437) qz377 0 3 Ns528p1229 Ns528p148 Ns528p1228 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1231 := Ns528p1161 228198 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 433014743 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 80739929 536870912) qz175 rfl rfl (Ns528p1222 rfl) (Ns528p1197 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p1226 rfl rfl) (Ns528p1230 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1232 := nat_lit 45971705735904105438847231182137877946764695449069714438338400707123755928883376816127184859754851582611403309056 

noncomputable def Ns528p1233 := nat_lit 36907303275991248759761476552111266433461295386149040030621598945762628721960972335005391030385213467262976 

noncomputable def Ns528p1234 := nat_lit 278452345040971222186355315703316121384575822432089327371317174421896065018743921814948202608721546513674246553600 

noncomputable def Ns528p1235 := BSN.cos_dyadic_bound_f 759613532 536870912 4 3 536870912 268435456 Ns528p1232 Ns528p145 Ns528p1233 Ns528p1234 Ns528p148 Ns528p1233 83362653 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 759613532) qz20 0 3 Ns528p1232 Ns528p145 Ns528p1233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 759613532) qz377 0 3 Ns528p1234 Ns528p148 Ns528p1233 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1236 := nat_lit 65461689174530032279477406820986597326109407107027977903809690196022729053334924446283529852542955094938815670801 

noncomputable def Ns528p1237 := nat_lit 106240858440219956831782265719333791957371469060627352993630144819724243283978859958901478498939684085410321 

noncomputable def Ns528p1238 := nat_lit 396238311909187769532867656050165235719805095752456836192765018434453011274714671898576677450296575782448927451665 

noncomputable def Ns528p1239 := BSN.cos_dyadic_bound_f 829578773 536870912 4 3 536870912 268435456 Ns528p1236 Ns528p145 Ns528p1237 Ns528p1238 Ns528p148 Ns528p1237 13734584 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 829578773) qz20 0 3 Ns528p1236 Ns528p145 Ns528p1237 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 829578773) qz377 0 3 Ns528p1238 Ns528p148 Ns528p1237 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1240 := Ns528p1159 265834 BSN.abs_quadSignPos (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 83362653 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 236 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 13734584 536870912) qz175 rfl rfl (Ns528p1231 rfl) (Ns528p1197 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p1235 rfl rfl) (Ns528p1239 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1241 := nat_lit 79933557774497906758098157112159307836333027929425893520147045895881121 

noncomputable def Ns528p1242 := nat_lit 328002508594056200190669275822391206023253852822381762107016987041 

noncomputable def Ns528p1243 := nat_lit 239800017318476532161894089997926278726587037280572035796916923653669281 

noncomputable def Ns528p1244 := BSN.cos_dyadic_bound_f 154697981 536870912 3 2 536870912 268435456 Ns528p1241 Ns528p165 Ns528p1242 Ns528p1243 Ns528p168 Ns528p1242 514736783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 154697981) qz20 0 2 Ns528p1241 Ns528p165 Ns528p1242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 154697981) qz377 0 2 Ns528p1243 Ns528p168 Ns528p1242 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1245 := Ns528p1157 Bool.true 880695011 265834 Bool.true 154697981 28296951008113761 1 Bool.false 514736783 Bool.false Bool.true 732103296 283423 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 514736783 536870912) qz175 rfl (Ns528p1240 rfl) (Ns528p1197 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p1244 rfl rfl) rfl 

noncomputable def Ns528p1246 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) 732103296 536870912 283423 536870912 732103296 536870912 283423 536870912 786089928403451904 5719557 2097152 283423 268435456 (Ns528p1245 rfl rfl rfl rfl) 

noncomputable def Ns528p1247 := @Enclosure.Real.IsNear.mulLit_ff qz658 (Zeta.RiemannSiegel.correction qz174) 301087 1048576 1 33554432 1487032308071425 2251799813685248 1103229245154643 105553116266496000000 447726096540301138975 2361183241434822606848 

noncomputable abbrev qz662 := (@HPow.hPow Real Real Real qz171 qz172 qz173)

noncomputable def Ns528p1248 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz662 1 1 0 1 301087 1048576 1 33554432 301087 1048576 1 33554432 

noncomputable def Ns528p1249 := @Enclosure.Real.IsNear.sqrt_image qz172 9872145437979 67108864000 924297 67108864000 406973096 406973135 33554432 (@Enclosure.Real.IsNear.of_eq qz172 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 9872145437979 67108864000 924297 67108864000 (BSN.t_div_two_pi_mk qz170 924297 1000 qz175) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 924297 1000 0 1 10680707 67108864 1 67108864 9872145437979 67108864000 924297 67108864000 (Enclosure.Real.IsNear.const Bool.false 924297 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz753 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 924297 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz663 := qz753

noncomputable abbrev qz489 := qz663

noncomputable abbrev qz181 := qz489

noncomputable def Ns528p1250 := @Enclosure.Real.IsNear.sqrt_image qz181 813946231 67108864 39 67108864 116857824 116857830 33554432 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 813946231 67108864 39 67108864 813946231 67108864 39 67108864 (Ns528p1249 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p1251 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz181) 116857827 33554432 3 33554432 9634783 9634785 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz181) Bool.false 233715654 67108864 6 67108864 116857827 33554432 3 33554432 (Ns528p1250 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p1252 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz181)) Bool.false 19269568 67108864 2 67108864 301087 1048576 1 33554432 (Ns528p1251 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz182 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz483))

noncomputable abbrev qz664 := (@HMul.hMul Real Real Real qz713 qz752 qz752)

noncomputable abbrev qz490 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz664 qz657) qz594)

noncomputable abbrev qz183 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz490))

noncomputable def Ns528p1253 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz174) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz182) qz183) Bool.false 1487032308071425 

noncomputable def Ns528p1254 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz182) qz183 97219975 67108864 533 

noncomputable def Ns528p1255 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz182) Bool.false 97219975 67108864 533 67108864 97219975 67108864 533 

noncomputable def Ns528p1256 := @Enclosure.Real.IsNear.recentre' qz182 Bool.false 23161905 33554432 1140554432 301989888000000 23161905 33554432 17821163 4718592000000 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz355 qz352 qz483)

noncomputable def Ns528p1257 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13571465) qz622) Bool.false 13571465 16777216 123 33554432 Bool.false 23161905 33554432 1 

noncomputable def Ns528p1258 := nat_lit 1052456941026933630805430609 

noncomputable def Ns528p1259 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz174 884279719003555 140737488355328 1 500000000000000 8639863 67108864 39 67108864 7640055625869211712965 9444732965739290427392 Ns528p1258 

noncomputable def Ns528p1260 := @Enclosure.Real.IsNear.subLit_ff_p qz181 qz1 813946231 67108864 39 67108864 12 1 0 1 8639863 8639863 67108864 39 

noncomputable def Ns528p1261 := @Ns528p1260 67108864 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 813946231 67108864 39 67108864 813946231 67108864 39 67108864 (Ns528p1249 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p1262 := @Enclosure.Real.IsNear.recentre' qz184 Bool.false 7640055625869211712965 9444732965739290427392 Ns528p1258 Ns528p330 13571465 16777216 123 33554432 (@Ns528p1259 Ns528p330 RS529to540.d55 (Ns528p1261 rfl rfl) rfl) 

noncomputable def Ns528p1263 := nat_lit 4516546271354817167506191070836535706358415336156968630690625 

noncomputable def Ns528p1264 := nat_lit 1150837084408883691784348658274114947327370543720937890625 

noncomputable def Ns528p1265 := nat_lit 13547337139895633735135004515193058889180591267383464016290625 

noncomputable def Ns528p1266 := BSN.cos_dyadic_bound_f 13571465 16777216 3 2 33554432 9000000 Ns528p1263 Ns528p624 Ns528p1264 Ns528p1265 Ns528p627 Ns528p1264 23161905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 13571465) (BSN.cosEvenQ 16777216) 0 2 Ns528p1263 Ns528p624 Ns528p1264 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 13571465) (BSN.cosOddQ 16777216) 0 2 Ns528p1265 Ns528p627 Ns528p1264 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1267 := @Enclosure.Real.IsNear.inv_image qz182 23161905 33554432 17821163 4718592000000 48609721 48610254 33554432 (Ns528p1256 (@Ns528p1257 9000000 (Ns528p1262 rfl) (Enclosure.sfrac_false_div 13571465 16777216) (Ns528p1266 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p1268 := @Enclosure.Real.IsNear.recentre' qz183 Bool.false 15295543 33554432 

noncomputable abbrev qz185 := (@HMul.hMul Real Real Real qz355 qz352 qz490)

noncomputable def Ns528p1269 := @Enclosure.Real.IsNear.cos_image qz185 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 73650471)) qz19) Bool.true 73650471 67108864 

noncomputable def Ns528p1270 := nat_lit 695609033341233641042432680045 

noncomputable def Ns528p1271 := nat_lit 3552615933411639415377414128082029 

noncomputable def Ns528p1272 := @Enclosure.Real.IsNear.recentre' qz185 Bool.true Ns528p1270 Ns528p217 Ns528p1271 

noncomputable abbrev qz186 := qz490

noncomputable def Ns528p1273 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz186 884279719003555 140737488355328 1 500000000000000 786639135097519 

noncomputable abbrev qz491 := (@HSub.hSub Real Real Real qz581 qz664 qz657)

noncomputable abbrev qz187 := qz491

noncomputable def Ns528p1274 := @Enclosure.Real.IsNear.subLit_tf qz187 qz31 505164158386863 4503599627370496 3291156531 4503599627370496 1 16 

noncomputable abbrev qz492 := qz664

noncomputable abbrev qz188 := qz492

noncomputable def Ns528p1275 := @Enclosure.Real.IsNear.subLit_ff_n qz188 qz174 74647232658769 4503599627370496 673910835 4503599627370496 8639863 67108864 39 67108864 

noncomputable def Ns528p1276 := @Enclosure.Real.IsNear.mulLit_ff qz174 qz174 8639863 67108864 39 67108864 8639863 67108864 39 67108864 74647232658769 4503599627370496 

noncomputable def Ns528p1277 := nat_lit 1003473263867645406698124584688091884942956998205179899357047330241 

noncomputable def Ns528p1278 := nat_lit 865773379713121771547780254735986270473213210610785970925376961 

noncomputable def Ns528p1279 := nat_lit 3008688244843509976551278193554803682287924568194318126129291236801 

noncomputable def Ns528p1280 := BSN.cos_dyadic_bound_f 73650471 67108864 3 2 33554432 9000000 Ns528p1277 Ns528p226 Ns528p1278 Ns528p1279 Ns528p229 Ns528p1278 15295543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 73650471) qz383 0 2 Ns528p1277 Ns528p226 Ns528p1278 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 73650471) (BSN.cosOddQ 67108864) 0 2 Ns528p1279 Ns528p229 Ns528p1278 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1281 := @Ns528p1268 2848108864 603979776000000 15295543 33554432 44501701 9437184000000 (@Ns528p1269 309 67108864 Bool.false 15295543 33554432 1 9000000 (@Ns528p1272 Ns528p1143 73650471 67108864 309 67108864 (@Ns528p1273 4503599627370496 3291156531 4503599627370496 Ns528p1270 Ns528p217 Ns528p1271 Ns528p1143 RS529to540.d55 (@Ns528p1274 0 1 12586226161560304 786639135097519 4503599627370496 3291156531 4503599627370496 (@Ns528p1275 33900992802858448453632 505164158386863 4503599627370496 3291156531 4503599627370496 (@Ns528p1276 673910835 4503599627370496 (Ns528p1261 rfl rfl) (Ns528p1261 rfl rfl) rfl) (Ns528p1261 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 73650471 67108864) (BSN.cos_neg_of_bound 73650471 67108864 Bool.false 15295543 33554432 1 9000000 (Ns528p1280 rfl rfl)) rfl rfl) 

noncomputable def Ns528p1282 := @Ns528p1247 356636040740604170121 Ns528p909 (Ns528p1248 qz33 (@Enclosure.Real.IsNear.of_eq qz662 (@Inv.inv Real Real.instInv (Real.sqrt qz181)) Bool.false 301087 1048576 1 33554432 (BSN.rpow_neg_quarter_mk qz172 (BSN.t_div_two_pi_nonneg qz170 924297 1000 qz175)) Ns528p1252) rfl) (@Ns528p1253 2251799813685248 1103229245154643 105553116266496000000 (BSN.correction_mk qz174 (BSN.cos_two_pi_p_ne_zero_mk qz170 924297 1000 12 qz175 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 924297 1000 12 qz175 rfl rfl rfl))) (@Ns528p1254 67108864 15295543 33554432 44501701 9437184000000 1487032308071425 2251799813685248 1103229245154643 105553116266496000000 (@Ns528p1255 67108864 (Ns528p1267 rfl rfl rfl rfl rfl) rfl) (Ns528p1281 rfl) rfl)) 

noncomputable def Ns528p1283 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 6887374790021379136543 2361183241434822606848 125007389672403503370121 Ns528p909 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HMul.hMul Real Real Real qz5 qz658 (Zeta.RiemannSiegel.correction qz174))) Bool.true 6887374790021379136543 2361183241434822606848 125007389672403503370121 Ns528p909 (BSN.hardyZApproximantRS₀_eq qz170 12 (@BSN.floor_sqrt_eq_dec qz170 924297 1000 12 qz175 rfl rfl rfl)) (@Ns528p1156 6887374790021379136543 2361183241434822606848 125007389672403503370121 Ns528p909 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12)) Bool.true 5719557 2097152 283423 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (Ns528p1246 (Ns528p1245 rfl rfl rfl rfl) rfl rfl)) (Ns528p1282 rfl) rfl rfl)) 

theorem RS529to540.d67 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 6887374790021379136543 2361183241434822606848 125007389672403503370121 Ns528p909 := Ns528p1283 

noncomputable def Ns528p1284 := nat_lit 7511893851273680621545639 

noncomputable def Ns528p1285 := nat_lit 7083549724304467820544000000 

noncomputable def Ns528p1286 := nat_lit 201985890790662738394190446592 

noncomputable abbrev qz754 := (Enclosure.sfrac Bool.false 925556 1000)

noncomputable abbrev qz665 := qz754

noncomputable abbrev qz493 := qz665

noncomputable abbrev qz189 := qz493

noncomputable abbrev qz755 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 925556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz666 := qz755

noncomputable abbrev qz494 := qz666

noncomputable abbrev qz190 := qz494

noncomputable abbrev qz756 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 925556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz667 := qz756

noncomputable abbrev qz495 := qz667

noncomputable abbrev qz191 := qz495

noncomputable abbrev qz668 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz171 qz190 qz173))

noncomputable def Ns528p1287 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz189) qz189 12) (@HMul.hMul Real Real Real qz5 qz668 (Zeta.RiemannSiegel.correction qz191)) 1385301 262144 141905 134217728 28056631332713843915995 151115727451828646838272 22636369375123181545639 Ns528p1285 Ns528p1286 

noncomputable def Ns528p1288 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz189) qz189 Real.cos BSN.quadSignPos 11 12 925556 1000 288 536870912 268435456 9007199254740992 Bool.false 991738346892 4518 1334074092 61 154981288 8 

noncomputable def Ns528p1289 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz189) qz189 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 925556 1000 180 236 536870912 268435456 9007199254740992 Bool.false 991738346892 4518 

noncomputable def Ns528p1290 := Ns528p1289 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.false 1179325370 228510 Bool.true 628935403 Bool.true 763322748 28296951008113761 1 Bool.false 208727541 Bool.false Bool.false 79696465 Bool.false Bool.false 1269360204 

noncomputable def Ns528p1291 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz189) qz189 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 925556 1000 49 118 536870912 268435456 9007199254740992 Bool.false 991738346892 4518 

noncomputable def Ns528p1292 := Ns528p1291 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.false 1345681880 186606 Bool.true 222239209 Bool.true 560373964 28296951008113761 1 Bool.false 215946330 Bool.true Bool.false 270023854 Bool.true Bool.false 1179325370 

noncomputable def Ns528p1293 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz189) qz189 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 925556 1000 120 29 536870912 268435456 9007199254740992 Bool.false 991738346892 4518 

noncomputable def Ns528p1294 := Ns528p1293 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.false 1266310753 138645 Bool.false 207955478 Bool.false 351511014 28296951008113761 1 Bool.false 497096478 Bool.false Bool.false 326929290 Bool.true Bool.false 1345681880 

noncomputable def Ns528p1295 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz189) qz189 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 925556 1000 359 227 536870912 268435456 9007199254740992 Bool.false 991738346892 4518 

noncomputable def Ns528p1296 := Ns528p1295 744261104 60 268435448 8 864060384 60 240095976 8 Bool.false 990934790 81743 Bool.false 132983022 Bool.false 569601685 28296951008113761 1 Bool.false 131627317 Bool.false Bool.false 468595553 Bool.false Bool.false 1266310753 

noncomputable def Ns528p1297 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz189) qz189 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 925556 1000 767 528 536870912 268435456 9007199254740992 Bool.false 991738346892 4518 

noncomputable def Ns528p1298 := Ns528p1297 372130544 60 379625064 8 589812976 60 309962568 8 Bool.false 536870904 4588 Bool.false 488194149 Bool.false 563163828 28296951008113761 1 Bool.false 423641543 Bool.false Bool.false 267608910 Bool.false Bool.false 990934790 

noncomputable def Ns528p1299 := nat_lit 1436468689526211561817519864320501726658594909896255547 

noncomputable def Ns528p1300 := nat_lit 777622704437944040155132917886973913601658585088000 

noncomputable def Ns528p1301 := nat_lit 326028121000665022237029330452480000 

noncomputable def Ns528p1302 := nat_lit 1810543947941493336472504115400309473280 

noncomputable abbrev qz669 := (@Eq.refl Real qz754)

noncomputable abbrev qz496 := qz669

noncomputable abbrev qz192 := qz496

noncomputable def Ns528p1303 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz189 925556 1000 3426616636544 16000000 1851112 4000 2000 Ns528p1301 Ns528p1302 qz192 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p1304 := nat_lit 15062465925886368146443677092497344185327628162393760564510720 

noncomputable abbrev qz670 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1851112))))

noncomputable abbrev qz497 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 925556 4000) (Real.log (Enclosure.sfrac Bool.false 3426616636544 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz670))

noncomputable abbrev qz671 := (Enclosure.sfrac Bool.false 925556 2000)

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz497 qz671) (@HMul.hMul Real Real Real qz355 qz671 (Real.log Real.pi)))

noncomputable def Ns528p1305 := @Enclosure.Real.IsNear.addLit_ft_p qz193 (Enclosure.sfrac Bool.true Ns528p1301 Ns528p1302) 8319305041621241650299 4503599627370496000 310153973901989507 36864000000000000000000 Ns528p1301 Ns528p1302 0 1 Ns528p1304 

noncomputable def Ns528p1306 := nat_lit 139574777653168561355262787584000 

noncomputable abbrev qz194 := (@HSub.hSub Real Real Real qz361 qz497 qz671)

noncomputable def Ns528p1307 := @Enclosure.Real.IsNear.subLit_ff_p qz194 (@HMul.hMul Real Real Real qz5 qz671 (Real.log Real.pi)) 10705113090110396390523 4503599627370496000 14586830201821 4500000000000000000 8887827577029 16777216000 694167 134217728000 Ns528p1306 8319305041621241650299 4503599627370496000 

noncomputable def Ns528p1308 := nat_lit 21410226180220792781046000 

noncomputable abbrev qz195 := qz497

noncomputable def Ns528p1309 := @Enclosure.Real.IsNear.subLit_ff_p qz195 qz671 12789279918465659788411 4503599627370496000 14586830201821 4500000000000000000 925556 2000 0 1 Ns528p1308 10705113090110396390523 4503599627370496000 14586830201821 4500000000000000000 

noncomputable def Ns528p1310 := nat_lit 28798898137569456444034265805832060928 

noncomputable def Ns528p1311 := nat_lit 118711633400712499090685952 

noncomputable def Ns528p1312 := nat_lit 109041948632411400066143895302847899446737447998827652312698343064290299801600883516924196616706738222937019241708437264163433011622984704550146349777404559360 

noncomputable def Ns528p1313 := nat_lit 2181849173989293408609677685236984205129828844277238329279111255976946152411446788848820472419324442931607308531311034605154738756321084927859863805589716992 

noncomputable def Ns528p1314 := nat_lit 316917316525275803092979931656251470007614142104870011804885155989018246884827537186621785272324337009409582837460715886544103234197659870745560350720 

noncomputable def Ns528p1315 := BSN.log_dyadic_bound 1329464636544 5523768636544 7 6 Ns528p1312 268435456 72000000 Ns528p1313 Ns528p1314 131799966 6853233273088 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1329464636544) (BSN.artanhQ 5523768636544) 0 6 Ns528p1313 Ns528p1312 Ns528p1314 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz498 := (Real.log (Enclosure.sfrac Bool.false 3426616636544 16000000))

noncomputable def Ns528p1316 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 925556 4000) qz498 925556 4000 0 1 55279412027780199 4503599627370496 125000153 9000000000000000 12791047869696032466411 4503599627370496000 28923660402517 9000000000000000000 (Enclosure.Real.IsNear.const Bool.false 925556 4000) (BSN.isNear_log_sfrac 3426616636544 16000000 55279412027780199 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3426616636544) qz364)) Bool.false Ns528p1311 Ns528p113 1000001224000000 72000000000000000000000 55279412027780199 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3426616636544 16000000 17 6853233273088 4194304000000 131799966 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p1315 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p1317 := BSN.arctan_dyadic_bound_f 1000 1851112 1 0 33554432 9000000 0 1 1 0 1 1 18126 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1851112) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1851112) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns528p1318 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1851112))) 884279719003555 562949953421312 1 2000000000000000 18126 33554432 1 9000000 29661299669428179304448 883975615186339 562949953421312 2000000009 18000000000000000 qz15 (Ns528p1317 rfl) rfl rfl 

noncomputable abbrev qz499 := (@HMul.hMul Real Real Real qz577 qz582 qz670)

noncomputable abbrev qz196 := qz499

noncomputable abbrev qz500 := qz670

noncomputable abbrev qz197 := qz500

noncomputable def Ns528p1319 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 925556 4000) qz498) qz196 12791047869696032466411 4503599627370496000 28923660402517 9000000000000000000 883975615186339 2251799813685248 2000000009 72000000000000000 Ns528p1310 12789279918465659788411 4503599627370496000 14586830201821 4500000000000000000 (Ns528p1316 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz197 1 4 0 1 883975615186339 562949953421312 2000000009 18000000000000000 883975615186339 2251799813685248 2000000009 72000000000000000 qz372 Ns528p1318 rfl) 

noncomputable def Ns528p1320 := @Ns528p1305 Ns528p1299 Ns528p1300 310153973901989507 36864000000000000000000 (@Ns528p1307 310153973901989507 36864000000000000000000 (Ns528p1309 (Ns528p1319 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 925556 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz671 (Real.log Real.pi) 925556 2000 0 1 38410761 33554432 3 268435456 8887827577029 16777216000 694167 134217728000 (Enclosure.Real.IsNear.const Bool.false 925556 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p1301 Ns528p1302) 

noncomputable def Ns528p1321 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz189) Bool.false Ns528p1299 Ns528p1300 310153973901989507 36864000000000000000000 123967293361 67108864 283 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz189) (@HAdd.hAdd Real Real Real qz373 qz193 (Enclosure.sfrac Bool.true Ns528p1301 Ns528p1302)) Bool.false Ns528p1299 Ns528p1300 310153973901989507 36864000000000000000000 Ns528p1303 (Ns528p1320 rfl rfl)) 

noncomputable def Ns528p1322 := BSN.cos_dyadic_bound_f 19355041 137438953472 1 0 67108864 18017579 0 1 1 0 1 1 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 19355041) qz588 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 19355041) qz589 0 0 rfl) rfl rfl 

noncomputable def Ns528p1323 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz189) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123967293361) qz19) Bool.false 123967293361 67108864 283 33554432 Bool.false 67108863 67108864 1 9000000 (Ns528p1321 rfl) (Enclosure.sfrac_false_div 123967293361 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 123967293361) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 1361989978017782300672) qz374) 226375608064910080 72057594037927936 Bool.false 67108863 67108864 294 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q0 123967293361 67108864 226375608064910080 72057594037927936 294 1361989978017782300672 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108863 67108864 1361989978017782300672 Ns528p113 19355041 137438953472 18017579 18000000 (Ns528p1322 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p1324 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz189) Bool.false Ns528p1299 Ns528p1300 310153973901989507 36864000000000000000000 991738346892 536870912 4518 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz189) (@HAdd.hAdd Real Real Real qz373 qz193 (Enclosure.sfrac Bool.true Ns528p1301 Ns528p1302)) Bool.false Ns528p1299 Ns528p1300 310153973901989507 36864000000000000000000 Ns528p1303 (Ns528p1320 rfl rfl)) 

noncomputable def Ns528p1325 := Ns528p1298 81743 BSN.abs_quadSignPos (BSN.cos_quad_nat3 767 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 423641543 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 528 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 267608910 536870912) qz192 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 1) Bool.false 67108863 67108864 40321163 4718592000000 536870904 536870912 4588 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz189)) Bool.false 67108863 67108864 40321163 4718592000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz189) qz189) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz189)) Bool.false 67108863 67108864 2580554432 301989888000000 67108863 67108864 40321163 4718592000000 (Ns528p1323 rfl rfl) rfl)) rfl) (Ns528p1324 rfl) RS529to540.d7 

noncomputable def Ns528p1326 := nat_lit 14273475996837622900273858739226275188403607883285354921278167973654359265 

noncomputable def Ns528p1327 := nat_lit 3226566057099105824190623602502046939912479045434828216426740961176801 

noncomputable def Ns528p1328 := nat_lit 37377689360958470948430464259760003131725781394911892214806701398014749921 

noncomputable def Ns528p1329 := BSN.sin_dyadic_bound_f 488194149 536870912 3 2 536870912 268435456 Ns528p1326 Ns528p180 Ns528p1327 Ns528p1328 Ns528p183 Ns528p1327 423641543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 488194149) qz375 0 2 Ns528p1326 Ns528p180 Ns528p1327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 488194149) qz376 0 2 Ns528p1328 Ns528p183 Ns528p1327 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1330 := nat_lit 13865535200559362046431511433962332444200382500282163436902868793955783999913303748194900375013153554442796138496 

noncomputable def Ns528p1331 := nat_lit 1017693563198775212082583242934512511175594307696352166998980876854439595531481407610319647222234785775616 

noncomputable def Ns528p1332 := nat_lit 84077188875415792256238535911901184866325076689532536489680069416038667224361977454672101070132304449070253998080 

noncomputable def Ns528p1333 := BSN.cos_dyadic_bound_f 563163828 536870912 4 3 536870912 268435456 Ns528p1330 Ns528p145 Ns528p1331 Ns528p1332 Ns528p148 Ns528p1331 267608910 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 563163828) qz20 0 3 Ns528p1330 Ns528p145 Ns528p1331 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 563163828) qz377 0 3 Ns528p1332 Ns528p148 Ns528p1331 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1334 := nat_lit 312740979306841638187271268170256 

noncomputable def Ns528p1335 := BSN.sin_dyadic_bound_f 132983022 536870912 2 1 536870912 268435456 Ns528p1334 Ns528p160 Ns528p1334 Ns528p1334 Ns528p161 Ns528p1334 131627317 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 132983022) qz375 0 1 Ns528p1334 Ns528p160 Ns528p1334 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 132983022) qz376 0 1 Ns528p1334 Ns528p161 Ns528p1334 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1336 := nat_lit 26456249686276696937791610021373585227209974165313145770290133177543830625 

noncomputable def Ns528p1337 := nat_lit 11080774655178313148022068272926877034604996786424161266466458250390625 

noncomputable def Ns528p1338 := nat_lit 69272237447949631853881228612107984460827238533404028375376069770685590625 

noncomputable def Ns528p1339 := BSN.sin_dyadic_bound_f 569601685 536870912 3 2 536870912 268435456 Ns528p1336 Ns528p180 Ns528p1337 Ns528p1338 Ns528p183 Ns528p1337 468595553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 569601685) qz375 0 2 Ns528p1336 Ns528p180 Ns528p1337 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 569601685) qz376 0 2 Ns528p1338 Ns528p183 Ns528p1337 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1340 := Ns528p1296 138645 BSN.abs_quadSignPos (BSN.cos_quad_nat3 359 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131627317 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 227 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 468595553 536870912) qz192 rfl rfl (Ns528p1325 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p1329 rfl rfl) (Ns528p1333 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p1324 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p1335 rfl rfl) (Ns528p1339 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p1341 := nat_lit 261021366252011198098708252794911959635411977626128089827745632119644416 

noncomputable def Ns528p1342 := nat_lit 3497541859213135740572131258357442819893924147488887560169740001536 

noncomputable def Ns528p1343 := nat_lit 783057103672315168024643614122219164020596145030089291708116556878930176 

noncomputable def Ns528p1344 := BSN.cos_dyadic_bound_f 207955478 536870912 3 2 536870912 268435456 Ns528p1341 Ns528p165 Ns528p1342 Ns528p1343 Ns528p168 Ns528p1342 497096478 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 207955478) qz20 0 2 Ns528p1341 Ns528p165 Ns528p1342 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 207955478) qz377 0 2 Ns528p1343 Ns528p168 Ns528p1342 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1345 := nat_lit 3835689337122466731623367371793663580400449901667383860967468566256820480 

noncomputable def Ns528p1346 := nat_lit 233083483211770683637010271906886446671694393468349840140647080141056 

noncomputable def Ns528p1347 := nat_lit 10045475652538403335049597480924126799182757475348961355173618530638110976 

noncomputable def Ns528p1348 := BSN.sin_dyadic_bound_f 351511014 536870912 3 2 536870912 268435456 Ns528p1345 Ns528p180 Ns528p1346 Ns528p1347 Ns528p183 Ns528p1346 326929290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 351511014) qz375 0 2 Ns528p1345 Ns528p180 Ns528p1346 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 351511014) qz376 0 2 Ns528p1347 Ns528p183 Ns528p1346 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1349 := Ns528p1294 186606 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 497096478 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 326929290 536870912) qz192 rfl rfl (Ns528p1340 rfl rfl) (Ns528p1324 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p1344 rfl rfl) (Ns528p1348 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1350 := nat_lit 612841591065632427473111660199267074289144216868954644534121238525058625 

noncomputable def Ns528p1351 := nat_lit 5950664442806301605243532939143464962394096226066319119344939245121 

noncomputable def Ns528p1352 := nat_lit 1605051675524701337941264906230464676575914787072419961644124304330661441 

noncomputable def Ns528p1353 := BSN.sin_dyadic_bound_f 222239209 536870912 3 2 536870912 268435456 Ns528p1350 Ns528p180 Ns528p1351 Ns528p1352 Ns528p183 Ns528p1351 215946330 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 222239209) qz375 0 2 Ns528p1350 Ns528p180 Ns528p1351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 222239209) qz376 0 2 Ns528p1352 Ns528p183 Ns528p1351 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1354 := nat_lit 13592622989228600526220541987364334209513666351275247939468650053486617155709462871278074302866323014223581413376 

noncomputable def Ns528p1355 := nat_lit 958816253869983442470661879772863216439959382055753944524902382854576019367039156366990900270533911248896 

noncomputable def Ns528p1356 := nat_lit 82423094836846986157228706730809701780029582172802808450039622699256365936933167024402272002850827313891183165440 

noncomputable def Ns528p1357 := BSN.cos_dyadic_bound_f 560373964 536870912 4 3 536870912 268435456 Ns528p1354 Ns528p145 Ns528p1355 Ns528p1356 Ns528p148 Ns528p1355 270023854 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 560373964) qz20 0 3 Ns528p1354 Ns528p145 Ns528p1355 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 560373964) qz377 0 3 Ns528p1356 Ns528p148 Ns528p1355 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1358 := Ns528p1292 228510 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 215946330 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 270023854 536870912) qz192 rfl rfl (Ns528p1349 rfl) (Ns528p1324 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p1353 rfl rfl) (Ns528p1357 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1359 := nat_lit 21577223811023223914896817655639609778745638594774231296093289437726575395142333523741053407509881832795407035921 

noncomputable def Ns528p1360 := nat_lit 3830650274009558652595798207028493101412438501139989097927006374906888160626776986100433766108794711617041 

noncomputable def Ns528p1361 := nat_lit 130804080614471791117122892547444286915486718973962353285997240928500538598145923274396735349919486918164699852305 

noncomputable def Ns528p1362 := BSN.cos_dyadic_bound_f 628935403 536870912 4 3 536870912 268435456 Ns528p1359 Ns528p145 Ns528p1360 Ns528p1361 Ns528p148 Ns528p1360 208727541 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 628935403) qz20 0 3 Ns528p1359 Ns528p145 Ns528p1360 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 628935403) qz377 0 3 Ns528p1361 Ns528p148 Ns528p1360 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1363 := nat_lit 46878425484435311067975405469326182915117608169779946547212569862099040545044238547266330774322030273122141208576 

noncomputable def Ns528p1364 := nat_lit 39128974079457629040650842338756563602331925747579387702360312898604558982909869411774011323136477124100096 

noncomputable def Ns528p1365 := nat_lit 283935516686437457260784959622878988761790796002448031319777394484449101775875824435659880620227709687002132643840 

noncomputable def Ns528p1366 := BSN.cos_dyadic_bound_f 763322748 536870912 4 3 536870912 268435456 Ns528p1363 Ns528p145 Ns528p1364 Ns528p1365 Ns528p148 Ns528p1364 79696465 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 763322748) qz20 0 3 Ns528p1363 Ns528p145 Ns528p1364 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 763322748) qz377 0 3 Ns528p1365 Ns528p148 Ns528p1364 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1367 := Ns528p1290 266197 BSN.abs_quadSignPos (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 208727541 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 236 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 79696465 536870912) qz192 rfl rfl (Ns528p1358 rfl) (Ns528p1324 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p1362 rfl rfl) (Ns528p1366 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1368 := nat_lit 470193811495397570940668485441281 

noncomputable def Ns528p1369 := BSN.cos_dyadic_bound_f 147254721 536870912 2 1 536870912 268435456 Ns528p1368 Ns528p141 Ns528p1368 Ns528p1368 Ns528p142 Ns528p1368 516802446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 147254721) qz20 0 1 Ns528p1368 Ns528p141 Ns528p1368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 147254721) qz377 0 1 Ns528p1368 Ns528p142 Ns528p1368 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1370 := Ns528p1288 Bool.false 1269360204 266197 Bool.true 147254721 28296951008113761 1 Bool.false 516802446 Bool.false Bool.false 1418548224 283810 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 516802446 536870912) qz192 rfl (Ns528p1367 rfl) (Ns528p1324 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p1369 rfl rfl) rfl 

noncomputable def Ns528p1371 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 12) 1418548224 536870912 283810 536870912 1418548224 536870912 283810 536870912 1523154557469720576 1385301 262144 141905 134217728 (Ns528p1370 rfl rfl rfl rfl) 

noncomputable def Ns528p1372 := @Enclosure.Real.IsNear.mulLit_ff qz668 (Zeta.RiemannSiegel.correction qz191) 19263011 67108864 1 67108864 1456502897325545 2251799813685248 3514730064303191 316659348799488000000 28056631332713843915995 151115727451828646838272 

noncomputable abbrev qz672 := (@HPow.hPow Real Real Real qz171 qz190 qz173)

noncomputable def Ns528p1373 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz672 1 1 0 1 19263011 67108864 1 67108864 19263011 67108864 1 67108864 

noncomputable def Ns528p1374 := @Enclosure.Real.IsNear.sqrt_image qz190 2471398112023 16777216000 231389 16777216000 407250174 407250213 33554432 (@Enclosure.Real.IsNear.of_eq qz190 (@HMul.hMul Real Real Real qz5 qz189 qz3) Bool.false 2471398112023 16777216000 231389 16777216000 (BSN.t_div_two_pi_mk qz189 925556 1000 qz192) (@Enclosure.Real.IsNear.mulLit_ff qz189 qz3 925556 1000 0 1 10680707 67108864 1 67108864 2471398112023 16777216000 231389 16777216000 (Enclosure.Real.IsNear.const Bool.false 925556 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz757 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 925556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz673 := qz757

noncomputable abbrev qz501 := qz673

noncomputable abbrev qz198 := qz501

noncomputable def Ns528p1375 := @Enclosure.Real.IsNear.sqrt_image qz198 814500387 67108864 39 67108864 116897597 116897603 33554432 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 814500387 67108864 39 67108864 814500387 67108864 39 67108864 (Ns528p1374 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p1376 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz198) 1826525 524288 3 33554432 9631505 9631506 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz198) Bool.false 233795200 67108864 6 67108864 1826525 524288 3 33554432 (Ns528p1375 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p1377 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz198)) Bool.false 19263011 67108864 1 67108864 19263011 67108864 1 67108864 (Ns528p1376 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz495))

noncomputable abbrev qz674 := (@HMul.hMul Real Real Real qz713 qz756 qz756)

noncomputable abbrev qz502 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz674 qz667) qz594)

noncomputable abbrev qz200 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz502))

noncomputable def Ns528p1378 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz191) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz199) qz200) Bool.false 1456502897325545 

noncomputable def Ns528p1379 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz199) qz200 102955135 67108864 597 

noncomputable def Ns528p1380 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz199) Bool.false 102955135 67108864 597 67108864 102955135 67108864 597 

noncomputable def Ns528p1381 := @Enclosure.Real.IsNear.recentre' qz199 Bool.false 21871661 33554432 1140554432 301989888000000 21871661 33554432 17821163 4718592000000 

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz355 qz352 qz495)

noncomputable def Ns528p1382 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 57767725) qz19) Bool.false 57767725 67108864 123 33554432 Bool.false 21871661 33554432 1 

noncomputable def Ns528p1383 := nat_lit 1052456941031693794599194961 

noncomputable def Ns528p1384 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz191 884279719003555 140737488355328 1 500000000000000 9194019 67108864 39 67108864 8130084537833345737545 9444732965739290427392 Ns528p1383 

noncomputable def Ns528p1385 := @Enclosure.Real.IsNear.subLit_ff_p qz198 qz1 814500387 67108864 39 67108864 12 1 0 1 9194019 9194019 67108864 39 

noncomputable def Ns528p1386 := @Ns528p1385 67108864 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 814500387 67108864 39 67108864 814500387 67108864 39 67108864 (Ns528p1374 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p1387 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 8130084537833345737545 9444732965739290427392 Ns528p1383 Ns528p330 57767725 67108864 123 33554432 (@Ns528p1384 Ns528p330 RS529to540.d55 (Ns528p1386 rfl rfl) rfl) 

noncomputable def Ns528p1388 := nat_lit 379587413169900077317031949422581170230846348596173373041525390625 

noncomputable def Ns528p1389 := nat_lit 124017255577171763914901222907715857416378279008960113525390625 

noncomputable def Ns528p1390 := nat_lit 1138514204998545888423266045821928078977706289230502198897525390625 

noncomputable def Ns528p1391 := BSN.cos_dyadic_bound_f 57767725 67108864 3 2 33554432 9000000 Ns528p1388 Ns528p226 Ns528p1389 Ns528p1390 Ns528p229 Ns528p1389 21871661 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 57767725) qz383 0 2 Ns528p1388 Ns528p226 Ns528p1389 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 57767725) (BSN.cosOddQ 67108864) 0 2 Ns528p1390 Ns528p229 Ns528p1389 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1392 := @Enclosure.Real.IsNear.inv_image qz199 21871661 33554432 17821163 4718592000000 51477269 51477866 33554432 (Ns528p1381 (@Ns528p1382 9000000 (Ns528p1387 rfl) (Enclosure.sfrac_false_div 57767725 67108864) (Ns528p1391 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p1393 := @Enclosure.Real.IsNear.recentre' qz200 Bool.false 14146967 33554432 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz355 qz352 qz502)

noncomputable def Ns528p1394 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 76207045)) qz19) Bool.true 76207045 67108864 

noncomputable def Ns528p1395 := nat_lit 719755199157745929749199737605 

noncomputable def Ns528p1396 := nat_lit 17996369798533346181968800651417369 

noncomputable def Ns528p1397 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns528p1395 Ns528p217 Ns528p1396 

noncomputable abbrev qz203 := qz502

noncomputable def Ns528p1398 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 813945162022711 

noncomputable abbrev qz503 := (@HSub.hSub Real Real Real qz581 qz674 qz667)

noncomputable abbrev qz204 := qz503

noncomputable def Ns528p1399 := @Enclosure.Real.IsNear.subLit_tf qz204 qz31 532470185312055 4503599627370496 3334380699 4503599627370496 1 16 

noncomputable abbrev qz504 := qz674

noncomputable abbrev qz205 := qz504

noncomputable def Ns528p1400 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz191 84529985372361 4503599627370496 717135003 4503599627370496 9194019 67108864 39 67108864 

noncomputable def Ns528p1401 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz191 9194019 67108864 39 67108864 9194019 67108864 39 67108864 84529985372361 4503599627370496 

noncomputable def Ns528p1402 := nat_lit 1150373779111211408120391938499691208718134312386593961719845190625 

noncomputable def Ns528p1403 := nat_lit 1137525062977601715844979896047917141582773300985807367000390625 

noncomputable def Ns528p1404 := nat_lit 3448846287207679020929485855706977791871237390557810270425534790625 

noncomputable def Ns528p1405 := BSN.cos_dyadic_bound_f 76207045 67108864 3 2 33554432 9000000 Ns528p1402 Ns528p226 Ns528p1403 Ns528p1404 Ns528p229 Ns528p1403 14146967 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 76207045) qz383 0 2 Ns528p1402 Ns528p226 Ns528p1403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 76207045) (BSN.cosOddQ 67108864) 0 2 Ns528p1404 Ns528p229 Ns528p1403 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1406 := @Ns528p1393 1446554432 301989888000000 14146967 33554432 22602413 4718592000000 (@Ns528p1394 157 33554432 Bool.false 14146967 33554432 1 9000000 (@Ns528p1397 Ns528p345 76207045 67108864 157 33554432 (@Ns528p1398 4503599627370496 3334380699 4503599627370496 Ns528p1395 Ns528p217 Ns528p1396 Ns528p345 RS529to540.d55 (@Ns528p1399 0 1 13023122592363376 813945162022711 4503599627370496 3334380699 4503599627370496 (@Ns528p1400 35733469250161496555520 532470185312055 4503599627370496 3334380699 4503599627370496 (@Ns528p1401 717135003 4503599627370496 (Ns528p1386 rfl rfl) (Ns528p1386 rfl rfl) rfl) (Ns528p1386 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 76207045 67108864) (BSN.cos_neg_of_bound 76207045 67108864 Bool.false 14146967 33554432 1 9000000 (Ns528p1405 rfl rfl)) rfl rfl) 

noncomputable def Ns528p1407 := @Ns528p1372 22636369375123181545639 Ns528p1285 (Ns528p1373 qz33 (@Enclosure.Real.IsNear.of_eq qz672 (@Inv.inv Real Real.instInv (Real.sqrt qz198)) Bool.false 19263011 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz190 (BSN.t_div_two_pi_nonneg qz189 925556 1000 qz192)) Ns528p1377) rfl) (@Ns528p1378 2251799813685248 3514730064303191 316659348799488000000 (BSN.correction_mk qz191 (BSN.cos_two_pi_p_ne_zero_mk qz189 925556 1000 12 qz192 rfl rfl (@BSN.floor_sqrt_eq_dec qz189 925556 1000 12 qz192 rfl rfl rfl))) (@Ns528p1379 67108864 14146967 33554432 22602413 4718592000000 1456502897325545 2251799813685248 3514730064303191 316659348799488000000 (@Ns528p1380 67108864 (Ns528p1392 rfl rfl rfl rfl rfl) rfl) (Ns528p1406 rfl) rfl)) 

noncomputable def Ns528p1408 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz189) (hardyZApproximantRS₀ qz189) Bool.false 770515025293971017433893 151115727451828646838272 Ns528p1284 Ns528p1285 (@Eq.refl Real (hardyZApproximantRS₀ qz189)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz189) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz189) qz189 12) (@HMul.hMul Real Real Real qz5 qz668 (Zeta.RiemannSiegel.correction qz191))) Bool.false 770515025293971017433893 151115727451828646838272 Ns528p1284 Ns528p1285 (BSN.hardyZApproximantRS₀_eq qz189 12 (@BSN.floor_sqrt_eq_dec qz189 925556 1000 12 qz192 rfl rfl rfl)) (@Ns528p1287 770515025293971017433893 151115727451828646838272 Ns528p1284 Ns528p1285 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz189) qz189 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz189) qz189 12)) Bool.false 1385301 262144 141905 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz189) qz189 12) (Ns528p1371 (Ns528p1370 rfl rfl rfl rfl) rfl rfl)) (Ns528p1407 rfl) rfl rfl)) 

theorem RS529to540.d68 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz189) Bool.false 770515025293971017433893 151115727451828646838272 Ns528p1284 Ns528p1285 := Ns528p1408 

noncomputable def Ns528p1409 := nat_lit 455019079907593155283376930816 

noncomputable abbrev qz758 := (Enclosure.sfrac Bool.false 926814 1000)

noncomputable abbrev qz675 := qz758

noncomputable abbrev qz505 := qz675

noncomputable abbrev qz206 := qz505

noncomputable abbrev qz759 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 926814 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz676 := qz759

noncomputable abbrev qz506 := qz676

noncomputable abbrev qz207 := qz506

noncomputable abbrev qz760 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 926814 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz677 := qz760

noncomputable abbrev qz507 := qz677

noncomputable abbrev qz208 := qz507

noncomputable abbrev qz678 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz171 qz207 qz173))

noncomputable def Ns528p1410 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HMul.hMul Real Real Real qz5 qz678 (Zeta.RiemannSiegel.correction qz208)) 168303133 134217728 71047 67108864 429336300395556503919 2361183241434822606848 2264926985958176800997 Ns528p234 Ns528p1409 

noncomputable def Ns528p1411 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos BSN.quadSignPos 11 12 926814 1000 288 536870912 268435456 9007199254740992 Bool.false 993424508456 4524 1334074092 61 154981288 8 

noncomputable def Ns528p1412 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 926814 1000 180 236 536870912 268435456 9007199254740992 Bool.false 993424508456 4524 

noncomputable def Ns528p1413 := Ns528p1412 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.true 631913515 228813 Bool.true 497902062 Bool.true 696660341 28296951008113761 1 Bool.false 322071158 Bool.false Bool.false 144837432 Bool.false Bool.true 486395541 

noncomputable def Ns528p1414 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 926814 1000 48 118 536870912 268435456 9007199254740992 Bool.false 993424508456 4524 

noncomputable def Ns528p1415 := Ns528p1414 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.true 512322712 186852 Bool.true 783813230 Bool.true 358181842 28296951008113761 1 Bool.false 59379887 Bool.false Bool.false 421754296 Bool.true Bool.true 631913515 

noncomputable def Ns528p1416 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 5 6 7 926814 1000 120 29 536870912 268435456 9007199254740992 Bool.false 993424508456 4524 

noncomputable def Ns528p1417 := Ns528p1416 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.true 378534943 138826 Bool.false 683992078 Bool.false 723436782 28296951008113761 1 Bool.false 156994526 Bool.false Bool.false 523542621 Bool.true Bool.true 512322712 

noncomputable def Ns528p1418 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 926814 1000 360 228 536870912 268435456 9007199254740992 Bool.false 993424508456 4524 

noncomputable def Ns528p1419 := Ns528p1418 744261104 60 268435448 8 864060384 60 240095976 8 Bool.true 843555425 81847 Bool.false 39549261 Bool.false 325460429 28296951008113761 1 Bool.false 535414847 Bool.false Bool.false 441205422 Bool.false Bool.true 378534943 

noncomputable def Ns528p1420 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 926814 1000 769 529 536870912 268435456 9007199254740992 Bool.false 993424508456 4524 

noncomputable def Ns528p1421 := Ns528p1420 372130544 60 379625064 8 589812976 60 309962568 8 Bool.true 536870768 4588 Bool.false 19585775 Bool.false 664025811 28296951008113761 1 Bool.false 19581430 Bool.true Bool.false 507211147 Bool.true Bool.true 843555425 

noncomputable def Ns528p1422 := nat_lit 165055759653646340364021410393771141970429603986250825893 

noncomputable def Ns528p1423 := nat_lit 89200171187467808717840781063479904118538825105408000 

noncomputable def Ns528p1424 := nat_lit 328249810939404114254033799275520000 

noncomputable def Ns528p1425 := nat_lit 1825359369575404067428660322483026759680 

noncomputable abbrev qz761 := (@Eq.refl Real (Enclosure.sfrac Bool.false 926814 1000))

noncomputable abbrev qz679 := qz761

noncomputable abbrev qz508 := qz679

noncomputable abbrev qz209 := qz508

noncomputable def Ns528p1426 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 926814 1000 3435937762384 16000000 1853628 4000 2000 Ns528p1424 Ns528p1425 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p1427 := nat_lit 30423077619360093455896426363779896887989584606745752228597760 

noncomputable abbrev qz680 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1853628))))

noncomputable abbrev qz509 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 926814 4000) (Real.log (Enclosure.sfrac Bool.false 3435937762384 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz680))

noncomputable abbrev qz681 := (Enclosure.sfrac Bool.false 926814 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz509 qz681) (@HMul.hMul Real Real Real qz355 qz681 (Real.log Real.pi)))

noncomputable def Ns528p1428 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns528p1424 Ns528p1425) 16666899177803132277257 9007199254740992000 621148276227462641 73728000000000000000000 Ns528p1424 Ns528p1425 0 1 Ns528p1427 

noncomputable def Ns528p1429 := nat_lit 559248335112451111384225153024000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz361 qz509 qz681)

noncomputable def Ns528p1430 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz681 (Real.log Real.pi)) 21445000774362232885769 9007199254740992000 58425945903521 18000000000000000000 17799815522727 33554432000 1390221 268435456000 Ns528p1429 16666899177803132277257 9007199254740992000 

noncomputable def Ns528p1431 := nat_lit 42890001548724465771538000 

noncomputable abbrev qz212 := qz509

noncomputable def Ns528p1432 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz681 25618999959403991765513 9007199254740992000 58425945903521 18000000000000000000 926814 2000 0 1 Ns528p1431 21445000774362232885769 9007199254740992000 58425945903521 18000000000000000000 

noncomputable def Ns528p1433 := nat_lit 57688859335388284733217379798403252224 

noncomputable def Ns528p1434 := nat_lit 118737905959786697805791232 

noncomputable def Ns528p1435 := nat_lit 111270601327701255125378989348992832000222596369151802578385363023328658618876352744865454975326764804320748499841404785985255072191753595265142493217879490560 

noncomputable def Ns528p1436 := nat_lit 2251047912202794706960993314626933880216598228772137530093893507035617141266015409270961064845831859999195063817776651330821456525476387565882013027382853632 

noncomputable def Ns528p1437 := nat_lit 344633519313416012063368402714510356274971709657989884740620107935703424430793319881058852751514802364264212028518054898996221218083488938484427653120 

noncomputable def Ns528p1438 := BSN.log_dyadic_bound 1338785762384 5533089762384 7 6 Ns528p1435 268435456 72000000 Ns528p1436 Ns528p1437 132529176 6871875524768 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1338785762384) (BSN.artanhQ 5533089762384) 0 6 Ns528p1436 Ns528p1435 Ns528p1437 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz510 := (Real.log (Enclosure.sfrac Bool.false 3435937762384 16000000))

noncomputable def Ns528p1439 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 926814 4000) qz510 926814 4000 0 1 55291646141459559 4503599627370496 125000153 9000000000000000 25622535863475349857513 9007199254740992000 19308648633757 6000000000000000000 (Enclosure.Real.IsNear.const Bool.false 926814 4000) (BSN.isNear_log_sfrac 3435937762384 16000000 55291646141459559 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3435937762384) qz364)) Bool.false Ns528p1434 Ns528p113 1000001224000000 72000000000000000000000 55291646141459559 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3435937762384 16000000 17 6871875524768 4194304000000 132529176 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p1438 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p1440 := BSN.arctan_dyadic_bound_f 1000 1853628 1 0 33554432 9000000 0 1 1 0 1 1 18102 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1853628) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1853628) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns528p1441 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1853628))) 884279719003555 562949953421312 1 2000000000000000 18102 33554432 1 9000000 29661313180227061415936 883976017839523 562949953421312 2000000009 18000000000000000 qz15 (Ns528p1440 rfl) rfl rfl 

noncomputable abbrev qz511 := (@HMul.hMul Real Real Real qz577 qz582 qz680)

noncomputable abbrev qz213 := qz511

noncomputable abbrev qz512 := qz680

noncomputable abbrev qz214 := qz512

noncomputable def Ns528p1442 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 926814 4000) qz510) qz213 25622535863475349857513 9007199254740992000 19308648633757 6000000000000000000 883976017839523 2251799813685248 2000000009 72000000000000000 Ns528p1433 25618999959403991765513 9007199254740992000 58425945903521 18000000000000000000 (Ns528p1439 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz214 1 4 0 1 883976017839523 562949953421312 2000000009 18000000000000000 883976017839523 2251799813685248 2000000009 72000000000000000 qz372 Ns528p1441 rfl) 

noncomputable def Ns528p1443 := @Ns528p1428 Ns528p1422 Ns528p1423 621148276227462641 73728000000000000000000 (@Ns528p1430 621148276227462641 73728000000000000000000 (Ns528p1432 (Ns528p1442 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 926814 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz681 (Real.log Real.pi) 926814 2000 0 1 38410761 33554432 3 268435456 17799815522727 33554432000 1390221 268435456000 (Enclosure.Real.IsNear.const Bool.false 926814 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p1424 Ns528p1425) 

noncomputable def Ns528p1444 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns528p1422 Ns528p1423 621148276227462641 73728000000000000000000 124178063557 67108864 283 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz373 qz210 (Enclosure.sfrac Bool.true Ns528p1424 Ns528p1425)) Bool.false Ns528p1422 Ns528p1423 621148276227462641 73728000000000000000000 Ns528p1426 (Ns528p1443 rfl rfl)) 

noncomputable def Ns528p1445 := nat_lit 15184738532757669060542464 

noncomputable def Ns528p1446 := nat_lit 14353572481551736654001002787415693394232014943018671775170224278252106890862424572289717980943676162126886631575230158065621415538497701833121 

noncomputable def Ns528p1447 := nat_lit 10193661583592450812779085442484311139309289892861641044509594605441246089067963647265066016651787885251022470489923286682605471837743521 

noncomputable def Ns528p1448 := nat_lit 71678847653786681654300706479701663905739775563620695937741424690403205194447531358031360984588861277387395227744005501277440888657947108338081 

noncomputable def Ns528p1449 := BSN.sin_dyadic_bound_f 215788113177 137438953472 4 3 67108864 18017579 Ns528p1446 Ns528p687 Ns528p1447 Ns528p1448 Ns528p690 Ns528p1447 67108846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215788113177) (BSN.sinEvenQ 137438953472) 0 3 Ns528p1446 Ns528p687 Ns528p1447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215788113177) (BSN.sinOddQ 137438953472) 0 3 Ns528p1448 Ns528p690 Ns528p1447 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1450 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 124178063557) qz19) Bool.false 124178063557 67108864 283 33554432 Bool.true 67108846 67108864 1 9000000 (Ns528p1444 rfl) (Enclosure.sfrac_false_div 124178063557 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 124178063557) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns528p1445) qz374) 226375608064910080 72057594037927936 Bool.false 67108846 67108864 294 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q1 124178063557 67108864 226375608064910080 72057594037927936 294 Ns528p1445 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108846 67108864 Ns528p1445 Ns528p113 215788113177 137438953472 18017579 18000000 (Ns528p1449 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p1451 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns528p1422 Ns528p1423 621148276227462641 73728000000000000000000 993424508456 536870912 4524 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz373 qz210 (Enclosure.sfrac Bool.true Ns528p1424 Ns528p1425)) Bool.false Ns528p1422 Ns528p1423 621148276227462641 73728000000000000000000 Ns528p1426 (Ns528p1443 rfl rfl)) 

noncomputable def Ns528p1452 := Ns528p1421 81847 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 769 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 19581430 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 529 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 507211147 536870912) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.true 33554423 33554432 40321163 4718592000000 536870768 536870912 4588 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 33554423 33554432 40321163 4718592000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 67108846 67108864 2580554432 301989888000000 33554423 33554432 40321163 4718592000000 (Ns528p1450 rfl rfl) rfl)) rfl) (Ns528p1451 rfl) RS529to540.d7 

noncomputable def Ns528p1453 := BSN.sin_dyadic_bound_f 19585775 536870912 1 0 536870912 268435456 0 1 1 0 1 1 19581430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 19585775) qz375 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 19585775) qz376 0 0 rfl) rfl rfl 

noncomputable def Ns528p1454 := nat_lit 69684135980341515351613149506897332375426026523121847460435414424013305710188602307474933485503469504532097955121 

noncomputable def Ns528p1455 := nat_lit 7348852508199695411512441858973144734620535793488816386945642531973149422693880597610960656637817773782321 

noncomputable def Ns528p1456 := nat_lit 348254093579138783034435887077407202403664353729204589120940039336497630316117109438140646690163551531228307813681 

noncomputable def Ns528p1457 := BSN.sin_dyadic_bound_f 664025811 536870912 4 3 536870912 268435456 Ns528p1454 Ns528p135 Ns528p1455 Ns528p1456 Ns528p138 Ns528p1455 507211147 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 664025811) qz375 0 3 Ns528p1454 Ns528p135 Ns528p1455 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 664025811) qz376 0 3 Ns528p1456 Ns528p138 Ns528p1455 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1458 := nat_lit 2446546595530214654416362346641 

noncomputable def Ns528p1459 := BSN.cos_dyadic_bound_f 39549261 536870912 2 1 536870912 268435456 Ns528p1458 Ns528p141 Ns528p1458 Ns528p1458 Ns528p142 Ns528p1458 535414847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 39549261) qz20 0 1 Ns528p1458 Ns528p141 Ns528p1458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 39549261) qz377 0 1 Ns528p1458 Ns528p142 Ns528p1458 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1460 := nat_lit 1566089077653331346317187382133270468675159594022023801852190916932228641 

noncomputable def Ns528p1461 := nat_lit 125888349751093328968817336502267605198447956142451971945602145801761 

noncomputable def Ns528p1462 := nat_lit 4698015456260491852293624511726806870815081886153786501612681546505082401 

noncomputable def Ns528p1463 := BSN.cos_dyadic_bound_f 325460429 536870912 3 2 536870912 268435456 Ns528p1460 Ns528p165 Ns528p1461 Ns528p1462 Ns528p168 Ns528p1461 441205422 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 325460429) qz20 0 2 Ns528p1460 Ns528p165 Ns528p1461 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 325460429) qz377 0 2 Ns528p1462 Ns528p168 Ns528p1461 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1464 := Ns528p1419 138826 BSN.abs_quadSignPos (BSN.cos_quad_nat0 360 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535414847 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 228 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 441205422 536870912) qz209 rfl rfl (Ns528p1452 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p1453 rfl rfl) (Ns528p1457 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p1451 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p1459 rfl rfl) (Ns528p1463 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p1465 := nat_lit 30197410542269935651297493594061432747243004755322979439762490022413478973443432190988105085630066176120563306496 

noncomputable def Ns528p1466 := nat_lit 10486072618483474615291313961113480810199889538318374865462852251521517895656405332273917585412961702383616 

noncomputable def Ns528p1467 := nat_lit 183006337585831233017644401074461010159362015059540685884961569761976511026486846745731392229438017552387682734080 

noncomputable def Ns528p1468 := BSN.cos_dyadic_bound_f 683992078 536870912 4 3 536870912 268435456 Ns528p1465 Ns528p145 Ns528p1466 Ns528p1467 Ns528p148 Ns528p1466 156994526 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 683992078) qz20 0 3 Ns528p1465 Ns528p145 Ns528p1466 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 683992078) qz377 0 3 Ns528p1467 Ns528p148 Ns528p1466 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1469 := nat_lit 98205033293187777276112641412014722657383566526761766782708328067512072471754837589968157480723162217080240869376 

noncomputable def Ns528p1470 := nat_lit 20549773150183631982232479001459789600319916794715377681265084695053771354318703039320148462301893547134976 

noncomputable def Ns528p1471 := nat_lit 490694495798427207401459862165142019200695098382336776020286253219044690269514044874618739509037164452637559361536 

noncomputable def Ns528p1472 := BSN.sin_dyadic_bound_f 723436782 536870912 4 3 536870912 268435456 Ns528p1469 Ns528p135 Ns528p1470 Ns528p1471 Ns528p138 Ns528p1470 523542621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 723436782) qz375 0 3 Ns528p1469 Ns528p135 Ns528p1470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 723436782) qz376 0 3 Ns528p1471 Ns528p138 Ns528p1470 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1473 := Ns528p1417 186852 BSN.abs_quadSignPos (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 156994526 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 29 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 523542621 536870912) qz209 rfl rfl (Ns528p1464 rfl rfl) (Ns528p1451 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p1468 rfl rfl) (Ns528p1472 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1474 := nat_lit 52132483988704407998889937209472868541477924699604734802388886240268413506817744427612810762613837631260224000000 

noncomputable def Ns528p1475 := nat_lit 53771366825133169075135496488844251453855026360635331624751247874705391226703638763902189861521000000000000 

noncomputable def Ns528p1476 := nat_lit 315701466693372553266842920215778353458235583924731061537122416755494263163530418167931462653535186456715225600000 

noncomputable def Ns528p1477 := BSN.cos_dyadic_bound_f 783813230 536870912 4 3 536870912 268435456 Ns528p1474 Ns528p145 Ns528p1475 Ns528p1476 Ns528p148 Ns528p1475 59379887 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 783813230) qz20 0 3 Ns528p1474 Ns528p145 Ns528p1475 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 783813230) qz377 0 3 Ns528p1476 Ns528p148 Ns528p1475 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1478 := nat_lit 2297493304455721179094969609083178688478005504909967737135077740016189696 

noncomputable def Ns528p1479 := nat_lit 270912175859132784210025391370439126205633971183649912670829095567616 

noncomputable def Ns528p1480 := nat_lit 6891938089015445271716488776466795187181605246787535911579891561857433856 

noncomputable def Ns528p1481 := BSN.cos_dyadic_bound_f 358181842 536870912 3 2 536870912 268435456 Ns528p1478 Ns528p165 Ns528p1479 Ns528p1480 Ns528p168 Ns528p1479 421754296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 358181842) qz20 0 2 Ns528p1478 Ns528p165 Ns528p1479 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 358181842) qz377 0 2 Ns528p1480 Ns528p168 Ns528p1479 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1482 := Ns528p1415 228813 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59379887 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 421754296 536870912) qz209 rfl rfl (Ns528p1473 rfl) (Ns528p1451 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p1477 rfl rfl) (Ns528p1481 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1483 := nat_lit 8581351131324584072414921895581098093603241859508289822112949811331154176 

noncomputable def Ns528p1484 := nat_lit 3777038388346631574790456022962089427833969408649706529127306118512896 

noncomputable def Ns528p1485 := nat_lit 25736499317197058954095184774697370101954057639707570053280594821756436736 

noncomputable def Ns528p1486 := BSN.cos_dyadic_bound_f 497902062 536870912 3 2 536870912 268435456 Ns528p1483 Ns528p165 Ns528p1484 Ns528p1485 Ns528p168 Ns528p1484 322071158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 497902062) qz20 0 2 Ns528p1483 Ns528p165 Ns528p1484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 497902062) qz377 0 2 Ns528p1485 Ns528p168 Ns528p1484 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1487 := nat_lit 32501363780230436170645142902655636873664058046306888513941986916898193330317371431172038485327435563493118345361 

noncomputable def Ns528p1488 := nat_lit 13069321942107025734255614908195348229386994732928542988948944559043571986848228448159573490072296583233681 

noncomputable def Ns528p1489 := nat_lit 196953399657889400042043142858380507257468196334490861627754579135232768360853219403814946859519104462786468413585 

noncomputable def Ns528p1490 := BSN.cos_dyadic_bound_f 696660341 536870912 4 3 536870912 268435456 Ns528p1487 Ns528p145 Ns528p1488 Ns528p1489 Ns528p148 Ns528p1488 144837432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 696660341) qz20 0 3 Ns528p1487 Ns528p145 Ns528p1488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 696660341) qz377 0 3 Ns528p1489 Ns528p148 Ns528p1488 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1491 := Ns528p1413 266551 BSN.abs_quadSignPos (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 322071158 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 236 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 144837432 536870912) qz209 rfl rfl (Ns528p1482 rfl) (Ns528p1451 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p1486 rfl rfl) (Ns528p1490 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1492 := nat_lit 377165681868538443549146691900625 

noncomputable def Ns528p1493 := BSN.cos_dyadic_bound_f 139358365 536870912 2 1 536870912 268435456 Ns528p1492 Ns528p141 Ns528p1492 Ns528p1492 Ns528p142 Ns528p1492 518885254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 139358365) qz20 0 1 Ns528p1492 Ns528p141 Ns528p1492 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 139358365) qz377 0 1 Ns528p1492 Ns528p142 Ns528p1492 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1494 := Ns528p1411 Bool.true 486395541 266551 Bool.true 139358365 28296951008113761 1 Bool.false 518885254 Bool.false Bool.true 336606266 284188 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 518885254 536870912) qz209 rfl (Ns528p1491 rfl) (Ns528p1451 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p1493 rfl rfl) rfl 

noncomputable def Ns528p1495 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) 336606266 536870912 284188 536870912 336606266 536870912 284188 536870912 361428226024669184 168303133 134217728 71047 67108864 (Ns528p1494 rfl rfl rfl rfl) 

noncomputable def Ns528p1496 := @Enclosure.Real.IsNear.mulLit_ff qz678 (Zeta.RiemannSiegel.correction qz208) 2407059 8388608 1 33554432 178365507615541 281474976710656 467870838909337 39582418599936000000 429336300395556503919 2361183241434822606848 

noncomputable abbrev qz682 := (@HPow.hPow Real Real Real qz171 qz207 qz173)

noncomputable def Ns528p1497 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz682 1 1 0 1 2407059 8388608 1 33554432 2407059 8388608 1 33554432 

noncomputable def Ns528p1498 := @Enclosure.Real.IsNear.sqrt_image qz207 4949514388749 33554432000 463407 33554432000 407526843 407526882 33554432 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 4949514388749 33554432000 463407 33554432000 (BSN.t_div_two_pi_mk qz206 926814 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 926814 1000 0 1 10680707 67108864 1 67108864 4949514388749 33554432000 463407 33554432000 (Enclosure.Real.IsNear.const Bool.false 926814 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz762 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 926814 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz683 := qz762

noncomputable abbrev qz513 := qz683

noncomputable abbrev qz215 := qz513

noncomputable def Ns528p1499 := @Enclosure.Real.IsNear.sqrt_image qz215 815053725 67108864 39 67108864 116937298 116937304 33554432 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 815053725 67108864 39 67108864 815053725 67108864 39 67108864 (Ns528p1498 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p1500 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 116937301 33554432 3 33554432 9628235 9628237 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 233874602 67108864 6 67108864 116937301 33554432 3 33554432 (Ns528p1499 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p1501 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 19256472 67108864 2 67108864 2407059 8388608 1 33554432 (Ns528p1500 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz507))

noncomputable abbrev qz684 := (@HMul.hMul Real Real Real qz713 qz760 qz760)

noncomputable abbrev qz514 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz684 qz677) qz594)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz514))

noncomputable def Ns528p1502 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 178365507615541 

noncomputable def Ns528p1503 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz216) qz217 54856157 33554432 339 

noncomputable def Ns528p1504 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz216) Bool.false 109712314 67108864 678 67108864 54856157 33554432 339 

noncomputable def Ns528p1505 := @Enclosure.Real.IsNear.recentre' qz216 Bool.false 20524586 33554432 1140554432 301989888000000 10262293 16777216 17821163 4718592000000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz355 qz352 qz507)

noncomputable def Ns528p1506 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 30622225) qz415) Bool.false 30622225 33554432 123 33554432 Bool.false 20524586 33554432 1 

noncomputable def Ns528p1507 := nat_lit 1052456941036446931826463057 

noncomputable def Ns528p1508 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 9747357 67108864 39 67108864 8619390108987334854135 9444732965739290427392 Ns528p1507 

noncomputable def Ns528p1509 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 815053725 67108864 39 67108864 12 1 0 1 9747357 9747357 67108864 39 

noncomputable def Ns528p1510 := @Ns528p1509 67108864 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 815053725 67108864 39 67108864 815053725 67108864 39 67108864 (Ns528p1498 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p1511 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 8619390108987334854135 9444732965739290427392 Ns528p1507 Ns528p330 30622225 33554432 123 33554432 (@Ns528p1508 Ns528p330 RS529to540.d55 (Ns528p1510 rfl rfl) rfl) 

noncomputable def Ns528p1512 := nat_lit 1873419779923663579027882044447652083279562726601763847462890625 

noncomputable def Ns528p1513 := nat_lit 773203739076707625187788065678295310265268154248199462890625 

noncomputable def Ns528p1514 := nat_lit 5618712932292837321833270557211599659218157643496795143462890625 

noncomputable def Ns528p1515 := BSN.cos_dyadic_bound_f 30622225 33554432 3 2 33554432 9000000 Ns528p1512 Ns528p887 Ns528p1513 Ns528p1514 Ns528p890 Ns528p1513 20524586 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 30622225) (BSN.cosEvenQ 33554432) 0 2 Ns528p1512 Ns528p887 Ns528p1513 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 30622225) (BSN.cosOddQ 33554432) 0 2 Ns528p1514 Ns528p890 Ns528p1513 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1516 := @Enclosure.Real.IsNear.inv_image qz216 10262293 16777216 17821163 4718592000000 54855818 54856496 33554432 (Ns528p1505 (@Ns528p1506 9000000 (Ns528p1511 rfl) (Enclosure.sfrac_false_div 30622225 33554432) (Ns528p1515 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p1517 := @Enclosure.Real.IsNear.recentre' qz217 Bool.false 13006052 33554432 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz355 qz352 qz514)

noncomputable def Ns528p1518 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 39351235)) qz415) Bool.true 39351235 33554432 

noncomputable def Ns528p1519 := nat_lit 743323819384638846674679163525 

noncomputable def Ns528p1520 := nat_lit 91146577830481467484078430841173681 

noncomputable def Ns528p1521 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns528p1519 Ns528p217 Ns528p1520 

noncomputable abbrev qz220 := qz514

noncomputable def Ns528p1522 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 840598063497655 

noncomputable abbrev qz515 := (@HSub.hSub Real Real Real qz581 qz684 qz677)

noncomputable abbrev qz221 := qz515

noncomputable def Ns528p1523 := @Enclosure.Real.IsNear.subLit_tf qz221 qz31 559123086786999 4503599627370496 3377541063 4503599627370496 1 16 

noncomputable abbrev qz516 := qz684

noncomputable abbrev qz222 := qz516

noncomputable def Ns528p1524 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 95010968485449 4503599627370496 760295367 4503599627370496 9747357 67108864 39 67108864 

noncomputable def Ns528p1525 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 9747357 67108864 39 67108864 9747357 67108864 39 67108864 95010968485449 4503599627370496 

noncomputable def Ns528p1526 := nat_lit 5112473152478213582706758459231030771731056729793491685004190625 

noncomputable def Ns528p1527 := nat_lit 5749987949624492713908915825597328253131636076527485375390625 

noncomputable def Ns528p1528 := nat_lit 15325919481535391762692457546041897658686906917227420084261790625 

noncomputable def Ns528p1529 := BSN.cos_dyadic_bound_f 39351235 33554432 3 2 33554432 9000000 Ns528p1526 Ns528p887 Ns528p1527 Ns528p1528 Ns528p890 Ns528p1527 13006052 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 39351235) (BSN.cosEvenQ 33554432) 0 2 Ns528p1526 Ns528p887 Ns528p1527 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 39351235) (BSN.cosOddQ 33554432) 0 2 Ns528p1528 Ns528p890 Ns528p1527 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1530 := @Ns528p1517 2920108864 603979776000000 3251513 8388608 45626701 9437184000000 (@Ns528p1518 317 67108864 Bool.false 13006052 33554432 1 9000000 (@Ns528p1521 Ns528p220 39351235 33554432 317 67108864 (@Ns528p1522 4503599627370496 3377541063 4503599627370496 Ns528p1519 Ns528p217 Ns528p1520 Ns528p220 RS529to540.d55 (@Ns528p1523 0 1 13449569015962480 840598063497655 4503599627370496 3377541063 4503599627370496 (@Ns528p1524 37522115190448912859136 559123086786999 4503599627370496 3377541063 4503599627370496 (@Ns528p1525 760295367 4503599627370496 (Ns528p1510 rfl rfl) (Ns528p1510 rfl rfl) rfl) (Ns528p1510 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 39351235 33554432) (BSN.cos_neg_of_bound 39351235 33554432 Bool.false 13006052 33554432 1 9000000 (Ns528p1529 rfl rfl)) rfl rfl) 

noncomputable def Ns528p1531 := @Ns528p1496 2264926985958176800997 Ns528p234 (Ns528p1497 qz33 (@Enclosure.Real.IsNear.of_eq qz682 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 2407059 8388608 1 33554432 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 926814 1000 qz209)) Ns528p1501) rfl) (@Ns528p1502 281474976710656 467870838909337 39582418599936000000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 926814 1000 12 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 926814 1000 12 qz209 rfl rfl rfl))) (@Ns528p1503 33554432 3251513 8388608 45626701 9437184000000 178365507615541 281474976710656 467870838909337 39582418599936000000 (@Ns528p1504 33554432 (Ns528p1516 rfl rfl rfl rfl rfl) rfl) (Ns528p1530 rfl) rfl)) 

noncomputable def Ns528p1532 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 3390156327989646459247 2361183241434822606848 705317950553371424800997 Ns528p234 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HMul.hMul Real Real Real qz5 qz678 (Zeta.RiemannSiegel.correction qz208))) Bool.true 3390156327989646459247 2361183241434822606848 705317950553371424800997 Ns528p234 (BSN.hardyZApproximantRS₀_eq qz206 12 (@BSN.floor_sqrt_eq_dec qz206 926814 1000 12 qz209 rfl rfl rfl)) (@Ns528p1410 3390156327989646459247 2361183241434822606848 705317950553371424800997 Ns528p234 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12)) Bool.true 168303133 134217728 71047 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (Ns528p1495 (Ns528p1494 rfl rfl rfl rfl) rfl rfl)) (Ns528p1531 rfl) rfl rfl)) 

theorem RS529to540.d69 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 3390156327989646459247 2361183241434822606848 705317950553371424800997 Ns528p234 := Ns528p1532 

noncomputable def Ns528p1533 := nat_lit 321455541759939961478279331840 

noncomputable abbrev qz763 := (Enclosure.sfrac Bool.false 928072 1000)

noncomputable abbrev qz685 := qz763

noncomputable abbrev qz517 := qz685

noncomputable abbrev qz223 := qz517

noncomputable abbrev qz764 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 928072 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz686 := qz764

noncomputable abbrev qz518 := qz686

noncomputable abbrev qz224 := qz518

noncomputable abbrev qz765 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 928072 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz687 := qz765

noncomputable abbrev qz519 := qz687

noncomputable abbrev qz225 := qz519

noncomputable abbrev qz688 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz171 qz224 qz173))

noncomputable def Ns528p1534 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HMul.hMul Real Real Real qz5 qz688 (Zeta.RiemannSiegel.correction qz225)) 183954957 268435456 142287 134217728 420569702563149666291 2361183241434822606848 3316708006461864657553 Ns528p648 Ns528p1533 

noncomputable def Ns528p1535 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos BSN.quadSignPos 11 12 928072 1000 288 536870912 268435456 9007199254740992 Bool.false 995111128429 4530 1334074092 61 154981288 8 

noncomputable def Ns528p1536 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 928072 1000 180 236 536870912 268435456 9007199254740992 Bool.false 995111128429 4530 

noncomputable def Ns528p1537 := Ns528p1536 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.true 160945815 229124 Bool.true 366410311 Bool.true 629539525 28296951008113761 1 Bool.false 416613496 Bool.false Bool.false 208170814 Bool.false Bool.false 33564804 

noncomputable def Ns528p1538 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 928072 1000 48 118 536870912 268435456 9007199254740992 Bool.false 995111128429 4530 

noncomputable def Ns528p1539 := Ns528p1538 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.true 102262688 187107 Bool.true 501613986 Bool.true 155531312 28296951008113761 1 Bool.false 319093678 Bool.false Bool.false 514499350 Bool.true Bool.true 160945815 

noncomputable def Ns528p1540 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 928072 1000 121 30 536870912 268435456 9007199254740992 Bool.false 995111128429 4530 

noncomputable def Ns528p1541 := Ns528p1540 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.false 200705647 139016 Bool.false 317172230 Bool.false 252506102 28296951008113761 1 Bool.false 299041617 Bool.true Bool.false 478576995 Bool.true Bool.true 102262688 

noncomputable def Ns528p1542 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 928072 1000 360 229 536870912 268435456 9007199254740992 Bool.false 995111128429 4530 

noncomputable def Ns528p1543 := Ns528p1542 744261104 60 268435448 8 864060384 60 240095976 8 Bool.false 210467457 81960 Bool.false 789888765 Bool.false 81777583 28296951008113761 1 Bool.false 53337955 Bool.false Bool.false 81461713 Bool.true Bool.false 200705647 

noncomputable def Ns528p1544 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 928072 1000 770 530 536870912 268435456 9007199254740992 Bool.false 995111128429 4530 

noncomputable def Ns528p1545 := Ns528p1544 372130544 60 379625064 8 589812976 60 309962568 8 Bool.false 536870760 4596 Bool.false 394750667 Bool.false 765346204 28296951008113761 1 Bool.false 398166382 Bool.true Bool.false 77694866 Bool.true Bool.false 210467457 

noncomputable def Ns528p1546 := nat_lit 5860092189865942900675098091451186277148695049173420203 

noncomputable def Ns528p1547 := nat_lit 3161569545847313781130302080329745366316868435968000 

noncomputable def Ns528p1548 := nat_lit 330483596014466103807105835663360000 

noncomputable def Ns528p1549 := nat_lit 1840275680790255882969534769846211051520 

noncomputable abbrev qz766 := (@Eq.refl Real (Enclosure.sfrac Bool.false 928072 1000))

noncomputable abbrev qz689 := qz766

noncomputable abbrev qz520 := qz689

noncomputable abbrev qz226 := qz520

noncomputable def Ns528p1550 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 928072 1000 3445271548736 16000000 1856144 4000 2000 Ns528p1548 Ns528p1549 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p1551 := nat_lit 7680940035101088678772864570426898877184337574852585328476160 

noncomputable abbrev qz690 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1856144))))

noncomputable abbrev qz521 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 928072 4000) (Real.log (Enclosure.sfrac Bool.false 3445271548736 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz690))

noncomputable abbrev qz691 := (Enclosure.sfrac Bool.false 928072 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz521 qz691) (@HMul.hMul Real Real Real qz355 qz691 (Real.log Real.pi)))

noncomputable def Ns528p1552 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns528p1548 Ns528p1549) 4173798990804257872583 2251799813685248000 17277461240304063 2048000000000000000000 Ns528p1548 Ns528p1549 0 1 Ns528p1551 

noncomputable def Ns528p1553 := nat_lit 35012363604652524024012734464000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz361 qz521 qz691)

noncomputable def Ns528p1554 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz691 (Real.log Real.pi)) 5369945764839230806727 2251799813685248000 3250253944431 1000000000000000000 4455993972849 8388608000 348027 67108864000 Ns528p1553 4173798990804257872583 2251799813685248000 

noncomputable def Ns528p1555 := nat_lit 2147978305935692322690800 

noncomputable abbrev qz229 := qz521

noncomputable def Ns528p1556 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz691 1282972388636495709531 450359962737049600 3250253944431 1000000000000000000 928072 2000 0 1 Ns528p1555 5369945764839230806727 2251799813685248000 3250253944431 1000000000000000000 

noncomputable def Ns528p1557 := nat_lit 2888996985694978627065589529667698688 

noncomputable def Ns528p1558 := nat_lit 118764142886380644765532160 

noncomputable def Ns528p1559 := nat_lit 113544049967948133439341886965867564520494836736761742966061682578102133882775821389084170348265436285004353943938830170203841648264733588798652739163741224960 

noncomputable def Ns528p1560 := nat_lit 2322250390611496679978884367008684059908332695445954152325157667443666484181448976596793621053583112690452879565556077032607323662166092742219619552368525312 

noncomputable def Ns528p1561 := nat_lit 374597926993359899405979939161768960734916932384458040339207799549140721959517675688195568455989030823285666836759152416994505986632445704733112401920 

noncomputable def Ns528p1562 := BSN.log_dyadic_bound 1348119548736 5542423548736 7 6 Ns528p1559 268435456 72000000 Ns528p1560 Ns528p1561 133257397 6890543097472 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1348119548736) (BSN.artanhQ 5542423548736) 0 6 Ns528p1560 Ns528p1559 Ns528p1561 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz522 := (Real.log (Enclosure.sfrac Bool.false 3445271548736 16000000))

noncomputable def Ns528p1563 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 928072 4000) qz522 928072 4000 0 1 55303863662472295 4503599627370496 125000153 9000000000000000 1283149183923949694131 450359962737049600 14501142749377 4500000000000000000 (Enclosure.Real.IsNear.const Bool.false 928072 4000) (BSN.isNear_log_sfrac 3445271548736 16000000 55303863662472295 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3445271548736) qz364)) Bool.false Ns528p1558 Ns528p113 1000001224000000 72000000000000000000000 55303863662472295 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3445271548736 16000000 17 6890543097472 4194304000000 133257397 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p1562 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p1564 := BSN.arctan_dyadic_bound_f 1000 1856144 1 0 33554432 9000000 0 1 1 0 1 1 18077 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1856144) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1856144) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns528p1565 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1856144))) 884279719003555 562949953421312 1 2000000000000000 18077 33554432 1 9000000 29661327253975896948736 883976437269923 562949953421312 2000000009 18000000000000000 qz15 (Ns528p1564 rfl) rfl rfl 

noncomputable abbrev qz523 := (@HMul.hMul Real Real Real qz577 qz582 qz690)

noncomputable abbrev qz230 := qz523

noncomputable abbrev qz524 := qz690

noncomputable abbrev qz231 := qz524

noncomputable def Ns528p1566 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 928072 4000) qz522) qz230 1283149183923949694131 450359962737049600 14501142749377 4500000000000000000 883976437269923 2251799813685248 2000000009 72000000000000000 Ns528p1557 1282972388636495709531 450359962737049600 3250253944431 1000000000000000000 (Ns528p1563 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz231 1 4 0 1 883976437269923 562949953421312 2000000009 18000000000000000 883976437269923 2251799813685248 2000000009 72000000000000000 qz372 Ns528p1565 rfl) 

noncomputable def Ns528p1567 := @Ns528p1552 Ns528p1546 Ns528p1547 17277461240304063 2048000000000000000000 (@Ns528p1554 17277461240304063 2048000000000000000000 (Ns528p1556 (Ns528p1566 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 928072 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz691 (Real.log Real.pi) 928072 2000 0 1 38410761 33554432 3 268435456 4455993972849 8388608000 348027 67108864000 (Enclosure.Real.IsNear.const Bool.false 928072 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p1548 Ns528p1549) 

noncomputable def Ns528p1568 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns528p1546 Ns528p1547 17277461240304063 2048000000000000000000 124388891053 67108864 567 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz373 qz227 (Enclosure.sfrac Bool.true Ns528p1548 Ns528p1549)) Bool.false Ns528p1546 Ns528p1547 17277461240304063 2048000000000000000000 Ns528p1550 (Ns528p1567 rfl rfl)) 

noncomputable def Ns528p1569 := nat_lit 15184562981268713149300736 

noncomputable def Ns528p1570 := nat_lit 14352907391600414667888397126437965358398100945224644623184843670361292019954510248244028166746370455914505518203296365648829908517283430400000 

noncomputable def Ns528p1571 := nat_lit 10192247480430543382646664983170852186801135763765841322572996812025681746931363447995097224014129750515780196443187247579136000000000000 

noncomputable def Ns528p1572 := nat_lit 71675530438413956478369496270560896321159209636610636993889329965976609875789629873644209603977293613176314017465138902730114706704433152000000 

noncomputable def Ns528p1573 := BSN.sin_dyadic_bound_f 215785618440 137438953472 4 3 67108864 18017579 Ns528p1570 Ns528p687 Ns528p1571 Ns528p1572 Ns528p690 Ns528p1571 67108845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215785618440) (BSN.sinEvenQ 137438953472) 0 3 Ns528p1570 Ns528p687 Ns528p1571 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215785618440) (BSN.sinOddQ 137438953472) 0 3 Ns528p1572 Ns528p690 Ns528p1571 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1574 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 124388891053) qz19) Bool.false 124388891053 67108864 567 67108864 Bool.false 67108845 67108864 1 9000000 (Ns528p1568 rfl) (Enclosure.sfrac_false_div 124388891053 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 124388891053) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns528p1569) qz374) 226375608064910080 72057594037927936 Bool.false 67108845 67108864 294 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q3 124388891053 67108864 226375608064910080 72057594037927936 294 Ns528p1569 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108845 67108864 Ns528p1569 Ns528p113 215785618440 137438953472 18017579 18000000 (Ns528p1573 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p1575 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns528p1546 Ns528p1547 17277461240304063 2048000000000000000000 995111128429 536870912 4530 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz373 qz227 (Enclosure.sfrac Bool.true Ns528p1548 Ns528p1549)) Bool.false Ns528p1546 Ns528p1547 17277461240304063 2048000000000000000000 Ns528p1550 (Ns528p1567 rfl rfl)) 

noncomputable def Ns528p1576 := Ns528p1545 81960 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 770 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 398166382 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 530 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 77694866 536870912) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.false 67108845 67108864 80782951 9437184000000 536870760 536870912 4596 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 67108845 67108864 80782951 9437184000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.false 67108845 67108864 5170108864 603979776000000 67108845 67108864 80782951 9437184000000 (Ns528p1574 rfl rfl) rfl)) rfl) (Ns528p1575 rfl) RS529to540.d7 

noncomputable def Ns528p1577 := nat_lit 3389657524626499578976756889782051734249702898056348619819609532873121121 

noncomputable def Ns528p1578 := nat_lit 589634626882089868421344927593622345756189969323072502743730352627041 

noncomputable def Ns528p1579 := nat_lit 10167793304625734557193427979490967958057596314230399714453341137914109281 

noncomputable def Ns528p1580 := BSN.cos_dyadic_bound_f 394750667 536870912 3 2 536870912 268435456 Ns528p1577 Ns528p165 Ns528p1578 Ns528p1579 Ns528p168 Ns528p1578 398166382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 394750667) qz20 0 2 Ns528p1577 Ns528p165 Ns528p1578 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 394750667) qz377 0 2 Ns528p1579 Ns528p168 Ns528p1578 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1581 := nat_lit 47378701343771509368465419105009680288107655025766175431093817839797581768875814869223378136227221344845557661696 

noncomputable def Ns528p1582 := nat_lit 40391984411810486406232190285583574526115367653752011403325419980646518645903810159362266591049450904354816 

noncomputable def Ns528p1583 := nat_lit 286960669620767781084541461844420051373729604271194601078554955804860769331580334768912316582690941080854572564480 

noncomputable def Ns528p1584 := BSN.cos_dyadic_bound_f 765346204 536870912 4 3 536870912 268435456 Ns528p1581 Ns528p145 Ns528p1582 Ns528p1583 Ns528p148 Ns528p1582 77694866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 765346204) qz20 0 3 Ns528p1581 Ns528p145 Ns528p1582 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 765346204) qz377 0 3 Ns528p1583 Ns528p148 Ns528p1582 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1585 := nat_lit 53772295240521629558091053963067139070573847223611323949681178356109079542274266074811096949700468324405430640625 

noncomputable def Ns528p1586 := nat_lit 58991744606632711927700230115451761433319097181721834271010849370254922679151269635599572046547226806640625 

noncomputable def Ns528p1587 := nat_lit 325613394016104132233818079339160300719287144770166259558851101677763150737777064099455374434418965360486992240625 

noncomputable def Ns528p1588 := BSN.cos_dyadic_bound_f 789888765 536870912 4 3 536870912 268435456 Ns528p1585 Ns528p145 Ns528p1586 Ns528p1587 Ns528p148 Ns528p1586 53337955 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 789888765) qz20 0 3 Ns528p1585 Ns528p145 Ns528p1586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 789888765) qz377 0 3 Ns528p1587 Ns528p148 Ns528p1586 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1589 := nat_lit 44723633718021144984043630528321 

noncomputable def Ns528p1590 := BSN.sin_dyadic_bound_f 81777583 536870912 2 1 536870912 268435456 Ns528p1589 Ns528p160 Ns528p1589 Ns528p1589 Ns528p161 Ns528p1589 81461713 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 81777583) qz375 0 1 Ns528p1589 Ns528p160 Ns528p1589 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 81777583) qz376 0 1 Ns528p1589 Ns528p161 Ns528p1589 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1591 := Ns528p1543 139016 BSN.abs_quadSignPos (BSN.cos_quad_nat0 360 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 53337955 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 81461713 536870912) qz226 rfl rfl (Ns528p1576 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p1580 rfl rfl) (Ns528p1584 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p1575 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p1588 rfl rfl) (Ns528p1590 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p1592 := nat_lit 2542490862565898475018308112778841572234260387963121461971777523310240000 

noncomputable def Ns528p1593 := nat_lit 102414451975727480695434489542555889891641910823353224497248100000000 

noncomputable def Ns528p1594 := nat_lit 6658738826178916256745871496675801884410857405381127923753088445079200000 

noncomputable def Ns528p1595 := BSN.sin_dyadic_bound_f 317172230 536870912 3 2 536870912 268435456 Ns528p1592 Ns528p180 Ns528p1593 Ns528p1594 Ns528p183 Ns528p1593 299041617 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 317172230) qz375 0 2 Ns528p1592 Ns528p180 Ns528p1593 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 317172230) qz376 0 2 Ns528p1594 Ns528p183 Ns528p1593 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1596 := nat_lit 567399487104531190938221762135778706688172989090087035243542485906350336 

noncomputable def Ns528p1597 := nat_lit 16526276745202044835360063947592669613828902808504108864403198566656 

noncomputable def Ns528p1598 := nat_lit 1702165408760103168724994566279440934725291309464644097512898651321917696 

noncomputable def Ns528p1599 := BSN.cos_dyadic_bound_f 252506102 536870912 3 2 536870912 268435456 Ns528p1596 Ns528p165 Ns528p1597 Ns528p1598 Ns528p168 Ns528p1597 478576995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 252506102) qz20 0 2 Ns528p1596 Ns528p165 Ns528p1597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 252506102) qz377 0 2 Ns528p1598 Ns528p168 Ns528p1597 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1600 := Ns528p1541 187107 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 299041617 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 478576995 536870912) qz226 rfl rfl (Ns528p1591 rfl rfl) (Ns528p1575 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p1595 rfl rfl) (Ns528p1599 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1601 := nat_lit 8840244680631558802125271521552543981685665213526118022355810809822740736 

noncomputable def Ns528p1602 := nat_lit 4008271178362849124942051998007990913342798613844497064387082280141056 

noncomputable def Ns528p1603 := nat_lit 26512717499537950708125930460661615963230310043350665072938658264907940096 

noncomputable def Ns528p1604 := BSN.cos_dyadic_bound_f 501613986 536870912 3 2 536870912 268435456 Ns528p1601 Ns528p165 Ns528p1602 Ns528p1603 Ns528p168 Ns528p1602 319093678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 501613986) qz20 0 2 Ns528p1601 Ns528p165 Ns528p1602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 501613986) qz377 0 2 Ns528p1603 Ns528p168 Ns528p1602 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1605 := nat_lit 81669884567819472097093409124833776045899699999961557423600012598706176 

noncomputable def Ns528p1606 := nat_lit 342407039255312484345089557188298680913553519842171057551909584896 

noncomputable def Ns528p1607 := nat_lit 245008968889379905666311537195386951540337272892844987928684933976948736 

noncomputable def Ns528p1608 := BSN.cos_dyadic_bound_f 155531312 536870912 3 2 536870912 268435456 Ns528p1605 Ns528p165 Ns528p1606 Ns528p1607 Ns528p168 Ns528p1606 514499350 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 155531312) qz20 0 2 Ns528p1605 Ns528p165 Ns528p1606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 155531312) qz377 0 2 Ns528p1607 Ns528p168 Ns528p1606 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1609 := Ns528p1539 229124 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 319093678 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 118 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 514499350 536870912) qz226 rfl rfl (Ns528p1600 rfl) (Ns528p1575 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p1604 rfl rfl) (Ns528p1608 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1610 := nat_lit 2516028803025414513377188933675266313030774920485486400358037083753632961 

noncomputable def Ns528p1611 := nat_lit 324893850893119268780173590232061229678800892106189868648485006169281 

noncomputable def Ns528p1612 := nat_lit 7547436621374457301594006453845334816632967159672246821336814281248560321 

noncomputable def Ns528p1613 := BSN.cos_dyadic_bound_f 366410311 536870912 3 2 536870912 268435456 Ns528p1610 Ns528p165 Ns528p1611 Ns528p1612 Ns528p168 Ns528p1611 416613496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 366410311) qz20 0 2 Ns528p1610 Ns528p165 Ns528p1611 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 366410311) qz377 0 2 Ns528p1612 Ns528p168 Ns528p1611 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1614 := nat_lit 21660340443958428815710007737737603716537269042168227330331270519503207977749135688686552528572602355052744140625 

noncomputable def Ns528p1615 := nat_lit 3875038524178888199876631674020419530681944182350709941170592912455774496547161639522395193576812744140625 

noncomputable def Ns528p1616 := nat_lit 131307567815305364381004085562886140522199091512895483537914919815028738727174013021044595276301126831468744140625 

noncomputable def Ns528p1617 := BSN.cos_dyadic_bound_f 629539525 536870912 4 3 536870912 268435456 Ns528p1614 Ns528p145 Ns528p1615 Ns528p1616 Ns528p148 Ns528p1615 208170814 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 629539525) qz20 0 3 Ns528p1614 Ns528p145 Ns528p1615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 629539525) qz377 0 3 Ns528p1616 Ns528p148 Ns528p1615 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1618 := Ns528p1537 266913 BSN.abs_quadSignPos (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 416613496 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 236 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 208170814 536870912) qz226 rfl rfl (Ns528p1609 rfl) (Ns528p1575 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p1613 rfl rfl) (Ns528p1617 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1619 := nat_lit 294532294844863807911961600000000 

noncomputable def Ns528p1620 := BSN.cos_dyadic_bound_f 131003600 536870912 2 1 536870912 268435456 Ns528p1619 Ns528p141 Ns528p1619 Ns528p1619 Ns528p142 Ns528p1619 520966756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 131003600) qz20 0 1 Ns528p1619 Ns528p141 Ns528p1619 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 131003600) qz377 0 1 Ns528p1619 Ns528p142 Ns528p1619 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1621 := Ns528p1535 Bool.false 33564804 266913 Bool.true 131003600 28296951008113761 1 Bool.false 520966756 Bool.false Bool.false 183954957 284574 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 520966756 536870912) qz226 rfl (Ns528p1618 rfl) (Ns528p1575 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p1620 rfl rfl) rfl 

noncomputable def Ns528p1622 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) 183954957 536870912 284574 536870912 183954957 536870912 284574 536870912 197520131063021568 183954957 268435456 142287 134217728 (Ns528p1621 rfl rfl rfl rfl) 

noncomputable def Ns528p1623 := @Enclosure.Real.IsNear.mulLit_ff qz688 (Zeta.RiemannSiegel.correction qz225) 19249943 67108864 1 67108864 21847841448837 35184372088832 4124913900115513 316659348799488000000 420569702563149666291 2361183241434822606848 

noncomputable abbrev qz692 := (@HPow.hPow Real Real Real qz171 qz224 qz173)

noncomputable def Ns528p1624 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz692 1 1 0 1 19249943 67108864 1 67108864 19249943 67108864 1 67108864 

noncomputable def Ns528p1625 := @Enclosure.Real.IsNear.sqrt_image qz224 1239058138363 8388608000 116009 8388608000 407803325 407803365 33554432 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 1239058138363 8388608000 116009 8388608000 (BSN.t_div_two_pi_mk qz223 928072 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 928072 1000 0 1 10680707 67108864 1 67108864 1239058138363 8388608000 116009 8388608000 (Enclosure.Real.IsNear.const Bool.false 928072 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz767 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 928072 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz693 := qz767

noncomputable abbrev qz525 := qz693

noncomputable abbrev qz232 := qz525

noncomputable def Ns528p1626 := @Enclosure.Real.IsNear.sqrt_image qz232 407803345 33554432 5 8388608 116976959 116976965 33554432 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 815606690 67108864 40 67108864 407803345 33554432 5 8388608 (Ns528p1625 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p1627 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 58488481 16777216 3 33554432 9624971 9624972 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 233953924 67108864 6 67108864 58488481 16777216 3 33554432 (Ns528p1626 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p1628 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 19249943 67108864 1 67108864 19249943 67108864 1 67108864 (Ns528p1627 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz519))

noncomputable abbrev qz694 := (@HMul.hMul Real Real Real qz713 qz765 qz765)

noncomputable abbrev qz526 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz694 qz687) qz594)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz526))

noncomputable def Ns528p1629 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 21847841448837 

noncomputable def Ns528p1630 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz233) qz234 7359439 4194304 401 

noncomputable def Ns528p1631 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz233) Bool.false 117751024 67108864 802 67108864 7359439 4194304 401 

noncomputable def Ns528p1632 := @Enclosure.Real.IsNear.recentre' qz233 Bool.false 19123399 33554432 2344108864 603979776000000 19123399 33554432 36626701 9437184000000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz355 qz352 qz519)

noncomputable def Ns528p1633 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 64718831) qz19) Bool.false 64718831 67108864 253 67108864 Bool.false 19123399 33554432 1 

noncomputable def Ns528p1634 := nat_lit 134930377056280113807912163 

noncomputable def Ns528p1635 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns528p1636 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 5150161 33554432 5 8388608 4554182921903067822355 4722366482869645213696 Ns528p1634 

noncomputable def Ns528p1637 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 407803345 33554432 5 8388608 12 1 0 1 5150161 5150161 33554432 5 

noncomputable def Ns528p1638 := @Ns528p1637 8388608 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 815606690 67108864 40 67108864 407803345 33554432 5 8388608 (Ns528p1625 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p1639 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 4554182921903067822355 4722366482869645213696 Ns528p1634 Ns528p1635 64718831 67108864 253 67108864 (@Ns528p1636 Ns528p1635 RS529to540.d55 (Ns528p1638 rfl rfl) rfl) 

noncomputable def Ns528p1640 := nat_lit 598101694726725064402130679959682865357312230117083743979494792321 

noncomputable def Ns528p1641 := nat_lit 307783485120598618708292502524625534955646018985323517652851841 

noncomputable def Ns528p1642 := nat_lit 1793689517209933995968975454873999345002025398313280584903178673281 

noncomputable def Ns528p1643 := BSN.cos_dyadic_bound_f 64718831 67108864 3 2 33554432 9000000 Ns528p1640 Ns528p226 Ns528p1641 Ns528p1642 Ns528p229 Ns528p1641 19123399 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 64718831) qz383 0 2 Ns528p1640 Ns528p226 Ns528p1641 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 64718831) (BSN.cosOddQ 67108864) 0 2 Ns528p1642 Ns528p229 Ns528p1641 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1644 := @Enclosure.Real.IsNear.inv_image qz233 19123399 33554432 36626701 9437184000000 58875111 58875913 33554432 (Ns528p1632 (@Ns528p1633 9000000 (Ns528p1639 rfl) (Enclosure.sfrac_false_div 64718831 67108864) (Ns528p1643 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p1645 := @Enclosure.Real.IsNear.recentre' qz234 Bool.false 11874732 33554432 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz355 qz352 qz526)

noncomputable def Ns528p1646 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 81138937)) qz19) Bool.true 81138937 67108864 

noncomputable def Ns528p1647 := nat_lit 191583899225364343039518873725 

noncomputable def Ns528p1648 := nat_lit 158456325028528675187087900672 

noncomputable def Ns528p1649 := nat_lit 118346823830363691782974602391769 

noncomputable def Ns528p1650 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns528p1647 Ns528p1648 Ns528p1649 

noncomputable def Ns528p1651 := nat_lit 24178516392292583494123520000000000000 

noncomputable abbrev qz237 := qz526

noncomputable def Ns528p1652 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 216655312915295 

noncomputable abbrev qz527 := (@HSub.hSub Real Real Real qz581 qz694 qz687)

noncomputable abbrev qz238 := qz527

noncomputable def Ns528p1653 := @Enclosure.Real.IsNear.subLit_tf qz238 qz31 146286568737631 1125899906842624 109636935 140737488355328 1 16 

noncomputable abbrev qz528 := qz694

noncomputable abbrev qz239 := qz528

noncomputable def Ns528p1654 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 26524158325921 1125899906842624 25750855 140737488355328 5150161 33554432 5 8388608 

noncomputable def Ns528p1655 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 5150161 33554432 5 8388608 5150161 33554432 5 8388608 26524158325921 1125899906842624 

noncomputable def Ns528p1656 := nat_lit 1478761581054967611204681437837181239368134851292217046580215275201 

noncomputable def Ns528p1657 := nat_lit 1878600829484071903188533287910401492533728977671855331302563521 

noncomputable def Ns528p1658 := nat_lit 4432527541505934689807667246935722915119337095921307429078040698561 

noncomputable def Ns528p1659 := BSN.cos_dyadic_bound_f 81138937 67108864 3 2 33554432 9000000 Ns528p1656 Ns528p226 Ns528p1657 Ns528p1658 Ns528p229 Ns528p1657 11874732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 81138937) qz383 0 2 Ns528p1656 Ns528p226 Ns528p1657 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 81138937) (BSN.cosOddQ 67108864) 0 2 Ns528p1658 Ns528p229 Ns528p1657 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1660 := @Ns528p1645 3028108864 603979776000000 2968683 8388608 47314201 9437184000000 (@Ns528p1646 329 67108864 Bool.false 11874732 33554432 1 9000000 (@Ns528p1650 Ns528p1651 81138937 67108864 329 67108864 (@Ns528p1652 1125899906842624 109636935 140737488355328 Ns528p1647 Ns528p1648 Ns528p1649 Ns528p1651 RS529to540.d55 (@Ns528p1653 0 1 3466485006644720 216655312915295 1125899906842624 109636935 140737488355328 (@Ns528p1654 4908562723220165230592 146286568737631 1125899906842624 109636935 140737488355328 (@Ns528p1655 25750855 140737488355328 (Ns528p1638 rfl rfl) (Ns528p1638 rfl rfl) rfl) (Ns528p1638 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 81138937 67108864) (BSN.cos_neg_of_bound 81138937 67108864 Bool.false 11874732 33554432 1 9000000 (Ns528p1659 rfl rfl)) rfl rfl) 

noncomputable def Ns528p1661 := @Ns528p1623 3316708006461864657553 Ns528p648 (Ns528p1624 qz33 (@Enclosure.Real.IsNear.of_eq qz692 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 19249943 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 928072 1000 qz226)) Ns528p1628) rfl) (@Ns528p1629 35184372088832 4124913900115513 316659348799488000000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 928072 1000 12 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 928072 1000 12 qz226 rfl rfl rfl))) (@Ns528p1630 33554432 2968683 8388608 47314201 9437184000000 21847841448837 35184372088832 4124913900115513 316659348799488000000 (@Ns528p1631 33554432 (Ns528p1644 rfl rfl rfl rfl rfl) rfl) (Ns528p1660 rfl) rfl)) 

noncomputable def Ns528p1662 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 1197515211105123018765 2361183241434822606848 941993973894644136657553 Ns528p648 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HMul.hMul Real Real Real qz5 qz688 (Zeta.RiemannSiegel.correction qz225))) Bool.false 1197515211105123018765 2361183241434822606848 941993973894644136657553 Ns528p648 (BSN.hardyZApproximantRS₀_eq qz223 12 (@BSN.floor_sqrt_eq_dec qz223 928072 1000 12 qz226 rfl rfl rfl)) (@Ns528p1534 1197515211105123018765 2361183241434822606848 941993973894644136657553 Ns528p648 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12)) Bool.false 183954957 268435456 142287 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (Ns528p1622 (Ns528p1621 rfl rfl rfl rfl) rfl rfl)) (Ns528p1661 rfl) rfl rfl)) 

theorem RS529to540.d70 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 1197515211105123018765 2361183241434822606848 941993973894644136657553 Ns528p648 := Ns528p1662 

noncomputable def Ns528p1663 := nat_lit 2264308475641323255453839 

noncomputable def Ns528p1664 := nat_lit 2125064917291340346163200000 

noncomputable def Ns528p1665 := nat_lit 2856235047161775026375374143488 

noncomputable abbrev qz768 := (Enclosure.sfrac Bool.false 929330 1000)

noncomputable abbrev qz695 := qz768

noncomputable abbrev qz529 := qz695

noncomputable abbrev qz240 := qz529

noncomputable abbrev qz769 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 929330 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz696 := qz769

noncomputable abbrev qz530 := qz696

noncomputable abbrev qz241 := qz530

noncomputable abbrev qz770 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 929330 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz697 := qz770

noncomputable abbrev qz531 := qz697

noncomputable abbrev qz242 := qz531

noncomputable abbrev qz698 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz171 qz241 qz173))

noncomputable def Ns528p1666 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HMul.hMul Real Real Real qz5 qz698 (Zeta.RiemannSiegel.correction qz242)) 63891841 67108864 142481 134217728 6593309930322799989825 37778931862957161709568 8411441826330769053839 Ns528p1664 Ns528p1665 

noncomputable def Ns528p1667 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos BSN.quadSignPos 11 12 929330 1000 288 536870912 268435456 9007199254740992 Bool.false 996798206349 4536 1334074092 61 154981288 8 

noncomputable def Ns528p1668 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 929330 1000 180 236 536870912 268435456 9007199254740992 Bool.false 996798206349 4536 

noncomputable def Ns528p1669 := Ns528p1668 1236190956 61 169773496 8 1287360220 61 161872664 8 Bool.true 641392671 229436 Bool.true 234460614 Bool.true 561960761 28296951008113761 1 Bool.false 486482986 Bool.false Bool.false 268651191 Bool.false Bool.true 406551859 

noncomputable def Ns528p1670 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 929330 1000 48 117 536870912 268435456 9007199254740992 Bool.false 996798206349 4536 

noncomputable def Ns528p1671 := Ns528p1670 1116391676 61 189812536 8 1179625948 61 178956968 8 Bool.true 637382093 187362 Bool.true 218956794 Bool.true 795737691 28296951008113761 1 Bool.false 492836840 Bool.false Bool.false 534764161 Bool.true Bool.true 641392671 

noncomputable def Ns528p1672 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 929330 1000 121 30 536870912 268435456 9007199254740992 Bool.false 996798206349 4536 

noncomputable def Ns528p1673 := Ns528p1672 961943533 61 219176632 8 1044702541 61 202918136 8 Bool.true 338985797 139206 Bool.false 794125185 Bool.false 625348225 28296951008113761 1 Bool.false 534619037 Bool.true Bool.false 212027826 Bool.true Bool.true 637382093 

noncomputable def Ns528p1674 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 929330 1000 361 229 536870912 268435456 9007199254740992 Bool.false 996798206349 4536 

noncomputable def Ns528p1675 := Ns528p1674 744261104 60 268435448 8 864060384 60 240095976 8 Bool.false 148913593 82073 Bool.false 697371360 Bool.false 681867540 28296951008113761 1 Bool.false 517156059 Bool.true Bool.false 512778156 Bool.true Bool.true 338985797 

noncomputable def Ns528p1676 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 929330 1000 771 532 536870912 268435456 9007199254740992 Bool.false 996798206349 4536 

noncomputable def Ns528p1677 := Ns528p1676 372130544 60 379625064 8 589812976 60 309962568 8 Bool.true 536870904 4604 Bool.false 770373506 Bool.false 23809687 28296951008113761 1 Bool.false 531923482 Bool.false Bool.false 536343030 Bool.false Bool.false 148913593 

noncomputable def Ns528p1678 := nat_lit 19391873430232703471784834669794815172893891792831271 

noncomputable def Ns528p1679 := nat_lit 10444373502641615006612090166316599062546507366400 

noncomputable def Ns528p1680 := nat_lit 332729525544264562106762864000000000 

noncomputable def Ns528p1681 := nat_lit 1855293430466818273070133600966720000000 

noncomputable abbrev qz771 := (@Eq.refl Real (Enclosure.sfrac Bool.false 929330 1000))

noncomputable abbrev qz699 := qz771

noncomputable abbrev qz532 := qz699

noncomputable abbrev qz243 := qz532

noncomputable def Ns528p1682 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 929330 1000 3454617995600 16000000 1858660 4000 2000 Ns528p1680 Ns528p1681 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns528p1683 := nat_lit 6205399497674465110971147094334340855326045373706006720000000 

noncomputable abbrev qz700 := (@HSub.hSub Real Real Real qz717 qz718 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz719 (@Nat.cast Real Real.instNatCast 1858660))))

noncomputable abbrev qz533 := (@HSub.hSub Real Real Real qz581 (@HMul.hMul Real Real Real qz577 (Enclosure.sfrac Bool.false 929330 4000) (Real.log (Enclosure.sfrac Bool.false 3454617995600 16000000))) (@HMul.hMul Real Real Real qz577 qz582 qz700))

noncomputable abbrev qz701 := (Enclosure.sfrac Bool.false 929330 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz361 (@HSub.hSub Real Real Real qz361 qz533 qz701) (@HMul.hMul Real Real Real qz355 qz701 (Real.log Real.pi)))

noncomputable def Ns528p1684 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns528p1680 Ns528p1681) 3344700086339078393251 1801439850948198400 124565786614885979 14745600000000000000000 Ns528p1680 Ns528p1681 0 1 Ns528p1683 

noncomputable def Ns528p1685 := nat_lit 22445902321491746977801987686400 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz361 qz533 qz701)

noncomputable def Ns528p1686 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz701 (Real.log Real.pi)) 4302914605483214966179 1801439850948198400 11716639219199 3600000000000000000 3569627252013 6710886400 278799 53687091200 Ns528p1685 3344700086339078393251 1801439850948198400 

noncomputable def Ns528p1687 := nat_lit 1721165842193285986471600 

noncomputable abbrev qz246 := qz533

noncomputable def Ns528p1688 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz701 1027996130764811915143 360287970189639680 11716639219199 3600000000000000000 929330 2000 0 1 Ns528p1687 4302914605483214966179 1801439850948198400 11716639219199 3600000000000000000 

noncomputable def Ns528p1689 := nat_lit 2314841495725359310113505103486910464 

noncomputable def Ns528p1690 := nat_lit 118790344288580731026800640 

noncomputable def Ns528p1691 := nat_lit 115863176536306064547583955184197435012353291719106923720053719921163095688586932844186159344592163399618290217634167787361483997839360000000000000000000000000 

noncomputable def Ns528p1692 := nat_lit 2395510299876717185029492059002086818961929257734722632059783786595471874554130465274103091822896851673793839013941338168944589012992000000000000000000000000 

noncomputable def Ns528p1693 := nat_lit 406979005297041695591414094958463684067561455578586888620087646506442395922671967616458487907694975747051295384080625665310720000000000000000000000000 

noncomputable def Ns528p1694 := BSN.log_dyadic_bound 1357465995600 5551769995600 7 6 Ns528p1691 268435456 72000000 Ns528p1692 Ns528p1693 133984632 6909235991200 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1357465995600) (BSN.artanhQ 5551769995600) 0 6 Ns528p1692 Ns528p1691 Ns528p1693 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz534 := (Real.log (Enclosure.sfrac Bool.false 3454617995600 16000000))

noncomputable def Ns528p1695 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 929330 4000) qz534 929330 4000 0 1 55316064641150055 4503599627370496 125000153 9000000000000000 1028137567059199612263 360287970189639680 11616639218749 3600000000000000000 (Enclosure.Real.IsNear.const Bool.false 929330 4000) (BSN.isNear_log_sfrac 3454617995600 16000000 55316064641150055 4503599627370496 125000153 9000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3454617995600) qz364)) Bool.false Ns528p1690 Ns528p113 1000001224000000 72000000000000000000000 55316064641150055 4503599627370496 125000153 9000000000000000 (BSN.log_rat_reduce_isNear 3454617995600 16000000 17 6909235991200 4194304000000 133984632 268435456 24973259072661432 36028797018963968 72000000 1000000000000000 rfl rfl rfl rfl (Ns528p1694 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns528p1696 := BSN.arctan_dyadic_bound_f 1000 1858660 1 0 33554432 9000000 0 1 1 0 1 1 18053 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1858660) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1858660) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns528p1697 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz14 (@Nat.cast Real Real.instNatCast 1858660))) 884279719003555 562949953421312 1 2000000000000000 18053 33554432 1 9000000 29661340764774779060224 883976839923107 562949953421312 2000000009 18000000000000000 qz15 (Ns528p1696 rfl) rfl rfl 

noncomputable abbrev qz535 := (@HMul.hMul Real Real Real qz577 qz582 qz700)

noncomputable abbrev qz247 := qz535

noncomputable abbrev qz536 := qz700

noncomputable abbrev qz248 := qz536

noncomputable def Ns528p1698 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 929330 4000) qz534) qz247 1028137567059199612263 360287970189639680 11616639218749 3600000000000000000 883976839923107 2251799813685248 2000000009 72000000000000000 Ns528p1689 1027996130764811915143 360287970189639680 11716639219199 3600000000000000000 (Ns528p1695 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz17 qz248 1 4 0 1 883976839923107 562949953421312 2000000009 18000000000000000 883976839923107 2251799813685248 2000000009 72000000000000000 qz372 Ns528p1697 rfl) 

noncomputable def Ns528p1699 := @Ns528p1684 Ns528p1678 Ns528p1679 124565786614885979 14745600000000000000000 (@Ns528p1686 124565786614885979 14745600000000000000000 (Ns528p1688 (Ns528p1698 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 929330 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz701 (Real.log Real.pi) 929330 2000 0 1 38410761 33554432 3 268435456 3569627252013 6710886400 278799 53687091200 (Enclosure.Real.IsNear.const Bool.false 929330 2000) RS529to540.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns528p1680 Ns528p1681) 

noncomputable def Ns528p1700 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns528p1678 Ns528p1679 124565786614885979 14745600000000000000000 124599775793 67108864 71 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz373 qz244 (Enclosure.sfrac Bool.true Ns528p1680 Ns528p1681)) Bool.false Ns528p1678 Ns528p1679 124565786614885979 14745600000000000000000 Ns528p1682 (Ns528p1699 rfl rfl)) 

noncomputable def Ns528p1701 := BSN.cos_dyadic_bound_f 11756143 137438953472 1 0 67108864 18017579 0 1 1 0 1 1 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 11756143) qz588 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 11756143) qz589 0 0 rfl) rfl rfl 

noncomputable def Ns528p1702 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 124599775793) qz19) Bool.false 124599775793 67108864 71 8388608 Bool.true 67108863 67108864 1 9000000 (Ns528p1700 rfl) (Enclosure.sfrac_false_div 124599775793 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 124599775793) qz19) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 827265060617800646656) qz374) 226375608064910080 72057594037927936 Bool.false 67108863 67108864 295 1000000000000000 18000000 9000000 (BSN.sin_reduce_arg_pos_rat_q2 124599775793 67108864 226375608064910080 72057594037927936 295 827265060617800646656 Ns528p113 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108863 67108864 827265060617800646656 Ns528p113 11756143 137438953472 18017579 18000000 (Ns528p1701 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns528p1703 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns528p1678 Ns528p1679 124565786614885979 14745600000000000000000 996798206349 536870912 4536 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz373 qz244 (Enclosure.sfrac Bool.true Ns528p1680 Ns528p1681)) Bool.false Ns528p1678 Ns528p1679 124565786614885979 14745600000000000000000 Ns528p1682 (Ns528p1699 rfl rfl)) 

noncomputable def Ns528p1704 := Ns528p1677 82073 BSN.abs_quadSignPos (BSN.cos_quad_nat3 771 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 531923482 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 532 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536343030 536870912) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 67108863 67108864 10115447 1179648000000 536870904 536870912 4604 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 67108863 67108864 10115447 1179648000000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 67108863 67108864 647388608 75497472000000 67108863 67108864 10115447 1179648000000 (Ns528p1702 rfl rfl) rfl)) rfl) (Ns528p1703 rfl) RS529to540.d7 

noncomputable def Ns528p1705 := nat_lit 126319971069987943774448538089793229469848707807826280917744270541295615574375857376288411270242655973654098087936 

noncomputable def Ns528p1706 := nat_lit 43693422276319769556787344303867440803944317361541459773904811775430240678273381581847816216570275157774336 

noncomputable def Ns528p1707 := nat_lit 631053050252009920976808359164588676424585173811806851938314276881743568086983789647787646047082092118221861687296 

noncomputable def Ns528p1708 := BSN.sin_dyadic_bound_f 770373506 536870912 4 3 536870912 268435456 Ns528p1705 Ns528p135 Ns528p1706 Ns528p1707 Ns528p138 Ns528p1706 531923482 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 770373506) qz375 0 3 Ns528p1705 Ns528p135 Ns528p1706 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 770373506) qz376 0 3 Ns528p1707 Ns528p138 Ns528p1706 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1709 := nat_lit 321376964935477367947351644961 

noncomputable def Ns528p1710 := BSN.cos_dyadic_bound_f 23809687 536870912 2 1 536870912 268435456 Ns528p1709 Ns528p141 Ns528p1709 Ns528p1709 Ns528p142 Ns528p1709 536343030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 23809687) qz20 0 1 Ns528p1709 Ns528p141 Ns528p1709 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 23809687) qz377 0 1 Ns528p1709 Ns528p142 Ns528p1709 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1711 := nat_lit 84785821935465223341395252631692463089199265819631757871152487533090800433026851180506552821312828538775142400000 

noncomputable def Ns528p1712 := nat_lit 13230287782270762660478002051402126568098414027300316685548090657387856552384595511739307524096000000000000 

noncomputable def Ns528p1713 := nat_lit 423682568703908719510416522237221711581961226209149807857517901743528638927865168996083972762593375092211712000000 

noncomputable def Ns528p1714 := BSN.sin_dyadic_bound_f 697371360 536870912 4 3 536870912 268435456 Ns528p1711 Ns528p135 Ns528p1712 Ns528p1713 Ns528p138 Ns528p1712 517156059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 697371360) qz375 0 3 Ns528p1711 Ns528p135 Ns528p1712 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 697371360) qz376 0 3 Ns528p1713 Ns528p138 Ns528p1712 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1715 := nat_lit 77487513759684598365981781878929803881652404678486332071270408673667228811656136574946764996457701420197478400000 

noncomputable def Ns528p1716 := nat_lit 10101833322627132414815217099641131959246510108637434654255526137633935230089066983815900041216000000000000 

noncomputable def Ns528p1717 := nat_lit 387231615685641552314888983489035163991469182551165173855805091540795531405984111800620994238155452211003392000000 

noncomputable def Ns528p1718 := BSN.sin_dyadic_bound_f 681867540 536870912 4 3 536870912 268435456 Ns528p1715 Ns528p135 Ns528p1716 Ns528p1717 Ns528p138 Ns528p1716 512778156 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 681867540) qz375 0 3 Ns528p1715 Ns528p135 Ns528p1716 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 681867540) qz376 0 3 Ns528p1717 Ns528p138 Ns528p1716 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1719 := Ns528p1675 139206 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 361 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 517156059 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 229 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 512778156 536870912) qz243 rfl rfl (Ns528p1704 RS529to540.d9 RS529to540.d11 RS529to540.d13 RS529to540.d17 (Ns528p1708 rfl rfl) (Ns528p1710 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns528p1703 rfl) RS529to540.d19 RS529to540.d21 RS529to540.d23 RS529to540.d25 RS529to540.d17 (Ns528p1714 rfl rfl) (Ns528p1718 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns528p1720 := nat_lit 142659632250525231010265285056071315187402147058373155531768060280715749542245053714520876473951078142230867290625 

noncomputable def Ns528p1721 := nat_lit 62902460574088228803615818408730136993509243704849565684678190172652928415414320547736156793636543212890625 

noncomputable def Ns528p1722 := nat_lit 712600970641700909841655997736954616166120015533872041460336451451940196341270935410393256610176437353077484890625 

noncomputable def Ns528p1723 := BSN.sin_dyadic_bound_f 794125185 536870912 4 3 536870912 268435456 Ns528p1720 Ns528p135 Ns528p1721 Ns528p1722 Ns528p138 Ns528p1721 534619037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 794125185) qz375 0 3 Ns528p1720 Ns528p135 Ns528p1721 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 794125185) qz376 0 3 Ns528p1722 Ns528p138 Ns528p1721 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1724 := nat_lit 21088616047587072364509915038974000948537496468222370753451635900068679327656327820703722145969984897433212890625 

noncomputable def Ns528p1725 := nat_lit 3576539762299393868603714474394949609984510472459530498457432524006885363726051609611883223056793212890625 

noncomputable def Ns528p1726 := nat_lit 127844232491484796985061512913794276671484396890633668194303748460522432642690373353803432596210964890009212890625 

noncomputable def Ns528p1727 := BSN.cos_dyadic_bound_f 625348225 536870912 4 3 536870912 268435456 Ns528p1724 Ns528p145 Ns528p1725 Ns528p1726 Ns528p148 Ns528p1725 212027826 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 625348225) qz20 0 3 Ns528p1724 Ns528p145 Ns528p1725 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 625348225) qz377 0 3 Ns528p1726 Ns528p148 Ns528p1725 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1728 := Ns528p1673 187362 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 534619037 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 30 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 212027826 536870912) qz243 rfl rfl (Ns528p1719 rfl rfl) (Ns528p1703 rfl) RS529to540.d27 RS529to540.d29 RS529to540.d31 RS529to540.d33 RS529to540.d17 (Ns528p1723 rfl rfl) (Ns528p1727 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1729 := nat_lit 320796508230038585201982518609158994022394479093651552291999244412887296 

noncomputable def Ns528p1730 := nat_lit 5282839343121337560910015067890597379127036107105034476123299881216 

noncomputable def Ns528p1731 := nat_lit 962378959011429512930825735797341200872425183208740446807045486638899456 

noncomputable def Ns528p1732 := BSN.cos_dyadic_bound_f 218956794 536870912 3 2 536870912 268435456 Ns528p1729 Ns528p165 Ns528p1730 Ns528p1731 Ns528p168 Ns528p1730 492836840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 218956794) qz20 0 2 Ns528p1729 Ns528p165 Ns528p1730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 218956794) qz377 0 2 Ns528p1731 Ns528p168 Ns528p1730 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1733 := nat_lit 143823725764266389412624100564423663996343084626949194062119210426905208799572472982328252935386792544532760700881 

noncomputable def Ns528p1734 := nat_lit 64452408748390145670534683260744311688807931333093547323509379229444315203237825907959162756796310947964881 

noncomputable def Ns528p1735 := nat_lit 718410029901945296262363054902503746687459916019629600975636791956147065054507790589816232906886718172182688114641 

noncomputable def Ns528p1736 := BSN.sin_dyadic_bound_f 795737691 536870912 4 3 536870912 268435456 Ns528p1733 Ns528p135 Ns528p1734 Ns528p1735 Ns528p138 Ns528p1734 534764161 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 795737691) qz375 0 3 Ns528p1733 Ns528p135 Ns528p1734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 795737691) qz376 0 3 Ns528p1735 Ns528p138 Ns528p1734 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1737 := Ns528p1671 229436 BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 492836840 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 117 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 534764161 536870912) qz243 rfl rfl (Ns528p1728 rfl) (Ns528p1703 rfl) RS529to540.d35 RS529to540.d37 RS529to540.d39 RS529to540.d41 RS529to540.d17 (Ns528p1732 rfl rfl) (Ns528p1736 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1738 := nat_lit 421772027858471753411692093303394238692732917939074595591670566438215936 

noncomputable def Ns528p1739 := nat_lit 9131858718371717178470467840534871014492148596203870285144286208256 

noncomputable def Ns528p1740 := nat_lit 1265297819857978516800719338974501646336169769520031379034441410742231296 

noncomputable def Ns528p1741 := BSN.cos_dyadic_bound_f 234460614 536870912 3 2 536870912 268435456 Ns528p1738 Ns528p165 Ns528p1739 Ns528p1740 Ns528p168 Ns528p1739 486482986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 234460614) qz20 0 2 Ns528p1738 Ns528p165 Ns528p1739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 234460614) qz377 0 2 Ns528p1740 Ns528p168 Ns528p1739 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1742 := nat_lit 13747348162817451288549061839703454823170206965623673092937275777072306708722416916720354502892694267567272679201 

noncomputable def Ns528p1743 := nat_lit 991909165678436855224337960853175609143479375996526241588949351351403379355709577043895633351883637970721 

noncomputable def Ns528p1744 := nat_lit 83360872709784062311259996370523579624765082271173173312154608948300187623927247477881679901421743640198209394465 

noncomputable def Ns528p1745 := BSN.cos_dyadic_bound_f 561960761 536870912 4 3 536870912 268435456 Ns528p1742 Ns528p145 Ns528p1743 Ns528p1744 Ns528p148 Ns528p1743 268651191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 561960761) qz20 0 3 Ns528p1742 Ns528p145 Ns528p1743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 561960761) qz377 0 3 Ns528p1744 Ns528p148 Ns528p1743 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1746 := Ns528p1669 267277 BSN.abs_quadSignPos (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 486482986 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 236 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268651191 536870912) qz243 rfl rfl (Ns528p1737 rfl) (Ns528p1703 rfl) RS529to540.d43 RS529to540.d45 RS529to540.d47 RS529to540.d49 RS529to540.d17 (Ns528p1741 rfl rfl) (Ns528p1745 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns528p1747 := nat_lit 222923200549789068475883387739361 

noncomputable def Ns528p1748 := BSN.cos_dyadic_bound_f 122190887 536870912 2 1 536870912 268435456 Ns528p1747 Ns528p141 Ns528p1747 Ns528p1747 Ns528p142 Ns528p1747 523025616 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 122190887) qz20 0 1 Ns528p1747 Ns528p141 Ns528p1747 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 122190887) qz377 0 1 Ns528p1747 Ns528p142 Ns528p1747 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1749 := Ns528p1667 Bool.true 406551859 267277 Bool.true 122190887 28296951008113761 1 Bool.false 523025616 Bool.false Bool.true 255567364 284962 BSN.abs_quadSignPos qz378 (BSN.sfrac_eq_quadSignPos_mul Bool.false 523025616 536870912) qz243 rfl (Ns528p1746 rfl) (Ns528p1703 rfl) RS529to540.d51 RS529to540.d53 RS529to540.d17 (Ns528p1748 rfl rfl) rfl 

noncomputable def Ns528p1750 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) 255567364 536870912 284962 536870912 255567364 536870912 284962 536870912 274413367576231936 63891841 67108864 142481 134217728 (Ns528p1749 rfl rfl rfl rfl) 

noncomputable def Ns528p1751 := @Enclosure.Real.IsNear.mulLit_ff qz698 (Zeta.RiemannSiegel.correction qz242) 19243425 67108864 1 67108864 342626633789089 562949953421312 872211536363653 63331869759897600000 6593309930322799989825 37778931862957161709568 

noncomputable abbrev qz702 := (@HPow.hPow Real Real Real qz171 qz241 qz173)

noncomputable def Ns528p1752 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz702 1 1 0 1 19243425 67108864 1 67108864 19243425 67108864 1 67108864 

noncomputable def Ns528p1753 := @Enclosure.Real.IsNear.sqrt_image qz241 992590143631 6710886400 92933 6710886400 408079620 408079659 33554432 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 992590143631 6710886400 92933 6710886400 (BSN.t_div_two_pi_mk qz240 929330 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 929330 1000 0 1 10680707 67108864 1 67108864 992590143631 6710886400 92933 6710886400 (Enclosure.Real.IsNear.const Bool.false 929330 1000) RS529to540.d56 rfl)) 

noncomputable abbrev qz772 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 929330 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz703 := qz772

noncomputable abbrev qz537 := qz703

noncomputable abbrev qz249 := qz537

noncomputable def Ns528p1754 := @Enclosure.Real.IsNear.sqrt_image qz249 816159279 67108864 39 67108864 117016579 117016586 33554432 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 816159279 67108864 39 67108864 816159279 67108864 39 67108864 (Ns528p1753 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns528p1755 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 234033165 67108864 7 67108864 9621712 9621713 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 234033165 67108864 7 67108864 234033165 67108864 7 67108864 (Ns528p1754 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns528p1756 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 19243425 67108864 1 67108864 19243425 67108864 1 67108864 (Ns528p1755 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz531))

noncomputable abbrev qz704 := (@HMul.hMul Real Real Real qz713 qz770 qz770)

noncomputable abbrev qz538 := (@HSub.hSub Real Real Real qz581 (@HSub.hSub Real Real Real qz581 qz704 qz697) qz594)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz538))

noncomputable def Ns528p1757 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 342626633789089 

noncomputable def Ns528p1758 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv qz250) qz251 31855529 16777216 457 

noncomputable def Ns528p1759 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz250) Bool.false 127422116 67108864 914 67108864 31855529 16777216 457 

noncomputable def Ns528p1760 := @Enclosure.Real.IsNear.recentre' qz250 Bool.false 17671970 33554432 1140554432 301989888000000 8835985 16777216 17821163 4718592000000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz355 qz352 qz531)

noncomputable def Ns528p1761 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 34095425) qz415) Bool.false 34095425 33554432 123 33554432 Bool.false 17671970 33554432 1 

noncomputable def Ns528p1762 := nat_lit 42098277641837742734975481 

noncomputable def Ns528p1763 := nat_lit 11529215046068469760000000000000 

noncomputable def Ns528p1764 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 10852911 67108864 39 67108864 9597009089450591098605 9444732965739290427392 Ns528p1762 

noncomputable def Ns528p1765 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 816159279 67108864 39 67108864 12 1 0 1 10852911 10852911 67108864 39 

noncomputable def Ns528p1766 := @Ns528p1765 67108864 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 816159279 67108864 39 67108864 816159279 67108864 39 67108864 (Ns528p1753 rfl rfl rfl rfl rfl rfl) rfl) qz382 

noncomputable def Ns528p1767 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 9597009089450591098605 9444732965739290427392 Ns528p1762 Ns528p1763 34095425 33554432 123 33554432 (@Ns528p1764 Ns528p1763 RS529to540.d55 (Ns528p1766 rfl rfl) rfl) 

noncomputable def Ns528p1768 := nat_lit 2879842798669557208045480493410311761802999821478900431212890625 

noncomputable def Ns528p1769 := nat_lit 1826286321761458310952933902571129332958939779150543212890625 

noncomputable def Ns528p1770 := nat_lit 8635875823365148707514535612425793026743081584878400207212890625 

noncomputable def Ns528p1771 := BSN.cos_dyadic_bound_f 34095425 33554432 3 2 33554432 9000000 Ns528p1768 Ns528p887 Ns528p1769 Ns528p1770 Ns528p890 Ns528p1769 17671970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 34095425) (BSN.cosEvenQ 33554432) 0 2 Ns528p1768 Ns528p887 Ns528p1769 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 34095425) (BSN.cosOddQ 33554432) 0 2 Ns528p1770 Ns528p890 Ns528p1769 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1772 := @Enclosure.Real.IsNear.inv_image qz250 8835985 16777216 17821163 4718592000000 63710601 63711515 33554432 (Ns528p1760 (@Ns528p1761 9000000 (Ns528p1767 rfl) (Enclosure.sfrac_false_div 34095425 33554432) (Ns528p1771 rfl rfl) rfl rfl) rfl) rfl 

noncomputable def Ns528p1773 := @Enclosure.Real.IsNear.recentre' qz251 Bool.false 10755641 33554432 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz355 qz352 qz538)

noncomputable def Ns528p1774 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 83516549)) qz19) Bool.true 83516549 67108864 

noncomputable def Ns528p1775 := nat_lit 788791505588936324193211627645 

noncomputable def Ns528p1776 := nat_lit 93473673792719224605717883334734613 

noncomputable def Ns528p1777 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns528p1775 Ns528p217 Ns528p1776 

noncomputable abbrev qz254 := qz538

noncomputable def Ns528p1778 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 892015827839839 

noncomputable abbrev qz539 := (@HSub.hSub Real Real Real qz581 qz704 qz697)

noncomputable abbrev qz255 := qz539

noncomputable def Ns528p1779 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 610540851129183 4503599627370496 3463774275 4503599627370496 1 16 

noncomputable abbrev qz540 := qz704

noncomputable abbrev qz256 := qz540

noncomputable def Ns528p1780 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 117785677173921 4503599627370496 846528579 4503599627370496 10852911 67108864 39 67108864 

noncomputable def Ns528p1781 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 10852911 67108864 39 67108864 10852911 67108864 39 67108864 117785677173921 4503599627370496 

noncomputable def Ns528p1782 := nat_lit 400013586290040779370528267032680558636716156951340774236871300261608100388175180265173132421833164881 

noncomputable def Ns528p1783 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns528p1784 := nat_lit 115151734965787103441949693518036014178349733946711212937524926334171137794736439417985266616401 

noncomputable def Ns528p1785 := nat_lit 2424441891321425199546660954759514433253799286675621967531650987014114107209335888324854260369939236945 

noncomputable def Ns528p1786 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable def Ns528p1787 := BSN.cos_dyadic_bound_f 83516549 67108864 4 3 33554432 9000000 Ns528p1782 Ns528p1783 Ns528p1784 Ns528p1785 Ns528p1786 Ns528p1784 10755641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 83516549) qz383 0 3 Ns528p1782 Ns528p1783 Ns528p1784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 83516549) (BSN.cosOddQ 67108864) 0 3 Ns528p1785 Ns528p1786 Ns528p1784 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns528p1788 := @Ns528p1773 2992108864 603979776000000 10755641 33554432 46751701 9437184000000 (@Ns528p1774 325 67108864 Bool.false 10755641 33554432 1 9000000 (@Ns528p1777 Ns528p220 83516549 67108864 325 67108864 (@Ns528p1778 4503599627370496 3463774275 4503599627370496 Ns528p1775 Ns528p217 Ns528p1776 Ns528p220 RS529to540.d55 (@Ns528p1779 0 1 14272253245437424 892015827839839 4503599627370496 3463774275 4503599627370496 (@Ns528p1780 40972702944872588378112 610540851129183 4503599627370496 3463774275 4503599627370496 (@Ns528p1781 846528579 4503599627370496 (Ns528p1766 rfl rfl) (Ns528p1766 rfl rfl) rfl) (Ns528p1766 rfl rfl) rfl rfl) qz387 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 83516549 67108864) (BSN.cos_neg_of_bound 83516549 67108864 Bool.false 10755641 33554432 1 9000000 (Ns528p1787 rfl rfl)) rfl rfl) 

noncomputable def Ns528p1789 := @Ns528p1751 8411441826330769053839 Ns528p1664 (Ns528p1752 qz33 (@Enclosure.Real.IsNear.of_eq qz702 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 19243425 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 929330 1000 qz243)) Ns528p1756) rfl) (@Ns528p1757 562949953421312 872211536363653 63331869759897600000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 929330 1000 12 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 929330 1000 12 qz243 rfl rfl rfl))) (@Ns528p1758 33554432 10755641 33554432 46751701 9437184000000 342626633789089 562949953421312 872211536363653 63331869759897600000 (@Ns528p1759 33554432 (Ns528p1772 rfl rfl rfl rfl rfl) rfl) (Ns528p1788 rfl) rfl)) 

noncomputable def Ns528p1790 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 42561218845274672305217 37778931862957161709568 Ns528p1663 Ns528p1664 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HMul.hMul Real Real Real qz5 qz698 (Zeta.RiemannSiegel.correction qz242))) Bool.true 42561218845274672305217 37778931862957161709568 Ns528p1663 Ns528p1664 (BSN.hardyZApproximantRS₀_eq qz240 12 (@BSN.floor_sqrt_eq_dec qz240 929330 1000 12 qz243 rfl rfl rfl)) (@Ns528p1666 42561218845274672305217 37778931862957161709568 Ns528p1663 Ns528p1664 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HAdd.hAdd Real Real Real qz373 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12)) Bool.true 63891841 67108864 142481 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (Ns528p1750 (Ns528p1749 rfl rfl rfl rfl) rfl rfl)) (Ns528p1789 rfl) rfl rfl)) 

theorem RS529to540.d71 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 42561218845274672305217 37778931862957161709568 Ns528p1663 Ns528p1664 := Ns528p1790 

noncomputable def RS529to540.d72 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz541 := (RS529to540.d3 qz578 qz595 (@Enclosure.dec_le_dec qz578 qz595 913584 1000 915477 1000 (@Eq.refl Real qz578) qz598 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz541)

noncomputable def Ns528p1791 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 259305943499235714045743 75557863725914323419136 Ns528p85 Ns528p86 

noncomputable abbrev qz542 := (@Enclosure.dec_le_dec qz578 qz595 913584 1000 915477 1000 (@Eq.refl Real qz578) qz598 rfl rfl rfl)

noncomputable abbrev qz258 := qz542

noncomputable def Ns528p1792 := @Enclosure.Real.IsNear.neg_val qz257 259305943499235714045743 75557863725914323419136 Ns528p85 Ns528p86 (Ns528p1791 (RS529to540.d4 qz4 qz35 qz258) RS529to540.d57) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz541)

noncomputable def Ns528p1793 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 23293063551938105778887 4722366482869645213696 696014028380964863877799 Ns528p234 

noncomputable def Ns528p1794 := @Enclosure.Real.IsNear.pos_val qz259 23293063551938105778887 4722366482869645213696 696014028380964863877799 Ns528p234 (Ns528p1793 (RS529to540.d58 qz4 qz35 qz258) RS529to540.d59) rfl 

noncomputable def Ns528p1795 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 913584 1000 913584 1000 

noncomputable def Ns528p1796 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 259305943499235714045743 75557863725914323419136 Ns528p85 

noncomputable def Ns528p1797 := @Ns528p1796 Ns528p86 93255129 2147483648 1213 10737418240 (Ns528p1791 (RS529to540.d4 qz4 qz35 qz258) RS529to540.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1798 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 913584 1000 915477 1000 

noncomputable def Ns528p1799 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 23293063551938105778887 4722366482869645213696 696014028380964863877799 

noncomputable def Ns528p1800 := @Ns528p1799 Ns528p234 93255129 2147483648 1213 10737418240 (Ns528p1793 (RS529to540.d58 qz4 qz35 qz258) RS529to540.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz541

noncomputable def Ns528p1801 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 913584 1000 qz9 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns528p1792 rfl rfl) (Ns528p1794 rfl rfl)) (Ns528p1795 qz9 qz9 rfl rfl rfl rfl (Ns528p1797 rfl)) (Ns528p1798 qz9 qz38 rfl rfl rfl rfl (Ns528p1800 rfl)) 

noncomputable abbrev qz543 := (RS529to540.d3 qz595 qz606 (@Enclosure.dec_le_dec qz595 qz606 915477 1000 916738 1000 qz598 qz609 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz543)

noncomputable def Ns528p1802 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 23293063551938105778887 4722366482869645213696 696014028380964863877799 Ns528p234 

noncomputable abbrev qz544 := (@Enclosure.dec_le_dec qz595 qz606 915477 1000 916738 1000 qz598 qz609 rfl rfl rfl)

noncomputable abbrev qz262 := qz544

noncomputable def Ns528p1803 := @Enclosure.Real.IsNear.pos_val qz261 23293063551938105778887 4722366482869645213696 696014028380964863877799 Ns528p234 (Ns528p1802 (RS529to540.d4 qz35 qz62 qz262) RS529to540.d59) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz543)

noncomputable def Ns528p1804 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 11358269322817122722857 4722366482869645213696 743465301978112708678757 Ns528p389 

noncomputable def Ns528p1805 := @Enclosure.Real.IsNear.neg_val qz263 11358269322817122722857 4722366482869645213696 743465301978112708678757 Ns528p389 (Ns528p1804 (RS529to540.d58 qz35 qz62 qz262) RS529to540.d61) rfl 

noncomputable def Ns528p1806 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 913584 1000 915477 1000 

noncomputable def Ns528p1807 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 23293063551938105778887 4722366482869645213696 696014028380964863877799 

noncomputable def Ns528p1808 := @Ns528p1807 Ns528p234 93255129 2147483648 1213 10737418240 (Ns528p1802 (RS529to540.d4 qz35 qz62 qz262) RS529to540.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1809 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 913584 1000 916738 1000 

noncomputable def Ns528p1810 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 11358269322817122722857 4722366482869645213696 743465301978112708678757 

noncomputable def Ns528p1811 := @Ns528p1810 Ns528p389 93255129 2147483648 1213 10737418240 (Ns528p1804 (RS529to540.d58 qz35 qz62 qz262) RS529to540.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz543

noncomputable def Ns528p1812 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 915477 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns528p1803 rfl rfl) (Ns528p1805 rfl rfl)) (Ns528p1806 qz9 qz38 rfl rfl rfl rfl (Ns528p1808 rfl)) (Ns528p1809 qz9 qz65 rfl rfl rfl rfl (Ns528p1811 rfl)) 

noncomputable abbrev qz545 := (RS529to540.d3 qz606 qz614 (@Enclosure.dec_le_dec qz606 qz614 916738 1000 917999 1000 qz609 qz617 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz545)

noncomputable def Ns528p1813 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 11358269322817122722857 4722366482869645213696 743465301978112708678757 Ns528p389 

noncomputable abbrev qz546 := (@Enclosure.dec_le_dec qz606 qz614 916738 1000 917999 1000 qz609 qz617 rfl rfl rfl)

noncomputable abbrev qz266 := qz546

noncomputable def Ns528p1814 := @Enclosure.Real.IsNear.neg_val qz265 11358269322817122722857 4722366482869645213696 743465301978112708678757 Ns528p389 (Ns528p1813 (RS529to540.d4 qz62 qz80 qz266) RS529to540.d61) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz545)

noncomputable def Ns528p1815 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 41310161512041559252339 75557863725914323419136 620441969260777144346971 Ns528p520 

noncomputable def Ns528p1816 := @Enclosure.Real.IsNear.pos_val qz267 41310161512041559252339 75557863725914323419136 620441969260777144346971 Ns528p520 (Ns528p1815 (RS529to540.d58 qz62 qz80 qz266) RS529to540.d62) rfl 

noncomputable def Ns528p1817 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 913584 1000 916738 1000 

noncomputable def Ns528p1818 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 11358269322817122722857 4722366482869645213696 743465301978112708678757 

noncomputable def Ns528p1819 := @Ns528p1818 Ns528p389 93255129 2147483648 1213 10737418240 (Ns528p1813 (RS529to540.d4 qz62 qz80 qz266) RS529to540.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1820 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 913584 1000 917999 1000 

noncomputable def Ns528p1821 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 41310161512041559252339 75557863725914323419136 620441969260777144346971 

noncomputable def Ns528p1822 := @Ns528p1821 Ns528p520 93255129 2147483648 1213 10737418240 (Ns528p1815 (RS529to540.d58 qz62 qz80 qz266) RS529to540.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz545

noncomputable def Ns528p1823 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 916738 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns528p1814 rfl rfl) (Ns528p1816 rfl rfl)) (Ns528p1817 qz9 qz65 rfl rfl rfl rfl (Ns528p1819 rfl)) (Ns528p1820 qz9 qz83 rfl rfl rfl rfl (Ns528p1822 rfl)) 

noncomputable abbrev qz547 := (RS529to540.d3 qz614 qz623 (@Enclosure.dec_le_dec qz614 qz623 917999 1000 919259 1000 qz617 qz626 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz547)

noncomputable def Ns528p1824 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 41310161512041559252339 75557863725914323419136 620441969260777144346971 Ns528p520 

noncomputable abbrev qz548 := (@Enclosure.dec_le_dec qz614 qz623 917999 1000 919259 1000 qz617 qz626 rfl rfl rfl)

noncomputable abbrev qz270 := qz548

noncomputable def Ns528p1825 := @Enclosure.Real.IsNear.pos_val qz269 41310161512041559252339 75557863725914323419136 620441969260777144346971 Ns528p520 (Ns528p1824 (RS529to540.d4 qz80 qz98 qz270) RS529to540.d62) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz547)

noncomputable def Ns528p1826 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 2863677479744352656751 9444732965739290427392 931990697442939365621539 Ns528p648 

noncomputable def Ns528p1827 := @Enclosure.Real.IsNear.neg_val qz271 2863677479744352656751 9444732965739290427392 931990697442939365621539 Ns528p648 (Ns528p1826 (RS529to540.d58 qz80 qz98 qz270) RS529to540.d63) rfl 

noncomputable def Ns528p1828 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 913584 1000 917999 1000 

noncomputable def Ns528p1829 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 41310161512041559252339 75557863725914323419136 620441969260777144346971 

noncomputable def Ns528p1830 := @Ns528p1829 Ns528p520 93255129 2147483648 1213 10737418240 (Ns528p1824 (RS529to540.d4 qz80 qz98 qz270) RS529to540.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1831 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 913584 1000 919259 1000 

noncomputable def Ns528p1832 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2863677479744352656751 9444732965739290427392 931990697442939365621539 

noncomputable def Ns528p1833 := @Ns528p1832 Ns528p648 93255129 2147483648 1213 10737418240 (Ns528p1826 (RS529to540.d58 qz80 qz98 qz270) RS529to540.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz547

noncomputable def Ns528p1834 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 917999 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns528p1825 rfl rfl) (Ns528p1827 rfl rfl)) (Ns528p1828 qz9 qz83 rfl rfl rfl rfl (Ns528p1830 rfl)) (Ns528p1831 qz9 qz101 rfl rfl rfl rfl (Ns528p1833 rfl)) 

noncomputable abbrev qz549 := (RS529to540.d3 qz623 qz631 (@Enclosure.dec_le_dec qz623 qz631 919259 1000 920519 1000 qz626 qz634 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz549)

noncomputable def Ns528p1835 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 2863677479744352656751 9444732965739290427392 931990697442939365621539 Ns528p648 

noncomputable abbrev qz550 := (@Enclosure.dec_le_dec qz623 qz631 919259 1000 920519 1000 qz626 qz634 rfl rfl rfl)

noncomputable abbrev qz274 := qz550

noncomputable def Ns528p1836 := @Enclosure.Real.IsNear.neg_val qz273 2863677479744352656751 9444732965739290427392 931990697442939365621539 Ns528p648 (Ns528p1835 (RS529to540.d4 qz98 qz116 qz274) RS529to540.d63) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz549)

noncomputable def Ns528p1837 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 387381530719352119836263 151115727451828646838272 Ns528p776 Ns528p777 

noncomputable def Ns528p1838 := @Enclosure.Real.IsNear.pos_val qz275 387381530719352119836263 151115727451828646838272 Ns528p776 Ns528p777 (Ns528p1837 (RS529to540.d58 qz98 qz116 qz274) RS529to540.d64) rfl 

noncomputable def Ns528p1839 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 913584 1000 919259 1000 

noncomputable def Ns528p1840 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2863677479744352656751 9444732965739290427392 931990697442939365621539 

noncomputable def Ns528p1841 := @Ns528p1840 Ns528p648 93255129 2147483648 1213 10737418240 (Ns528p1835 (RS529to540.d4 qz98 qz116 qz274) RS529to540.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1842 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 913584 1000 920519 1000 

noncomputable def Ns528p1843 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 387381530719352119836263 151115727451828646838272 Ns528p776 

noncomputable def Ns528p1844 := @Ns528p1843 Ns528p777 93255129 2147483648 1213 10737418240 (Ns528p1837 (RS529to540.d58 qz98 qz116 qz274) RS529to540.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz549

noncomputable def Ns528p1845 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 919259 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns528p1836 rfl rfl) (Ns528p1838 rfl rfl)) (Ns528p1839 qz9 qz101 rfl rfl rfl rfl (Ns528p1841 rfl)) (Ns528p1842 qz9 qz119 rfl rfl rfl rfl (Ns528p1844 rfl)) 

noncomputable abbrev qz551 := (RS529to540.d3 qz631 qz639 (@Enclosure.dec_le_dec qz631 qz639 920519 1000 921779 1000 qz634 qz642 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns528p1846 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 387381530719352119836263 151115727451828646838272 Ns528p776 Ns528p777 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz631 qz639 920519 1000 921779 1000 qz634 qz642 rfl rfl rfl)

noncomputable abbrev qz278 := qz552

noncomputable def Ns528p1847 := @Enclosure.Real.IsNear.pos_val qz277 387381530719352119836263 151115727451828646838272 Ns528p776 Ns528p777 (Ns528p1846 (RS529to540.d4 qz116 qz134 qz278) RS529to540.d64) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns528p1848 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 37772037226298547322957 18889465931478580854784 124633193993212151389047 Ns528p909 

noncomputable def Ns528p1849 := @Enclosure.Real.IsNear.neg_val qz279 37772037226298547322957 18889465931478580854784 124633193993212151389047 Ns528p909 (Ns528p1848 (RS529to540.d58 qz116 qz134 qz278) RS529to540.d65) rfl 

noncomputable def Ns528p1850 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 913584 1000 920519 1000 

noncomputable def Ns528p1851 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 387381530719352119836263 151115727451828646838272 Ns528p776 

noncomputable def Ns528p1852 := @Ns528p1851 Ns528p777 93255129 2147483648 1213 10737418240 (Ns528p1846 (RS529to540.d4 qz116 qz134 qz278) RS529to540.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1853 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 913584 1000 921779 1000 

noncomputable def Ns528p1854 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 37772037226298547322957 18889465931478580854784 124633193993212151389047 

noncomputable def Ns528p1855 := @Ns528p1854 Ns528p909 93255129 2147483648 1213 10737418240 (Ns528p1848 (RS529to540.d58 qz116 qz134 qz278) RS529to540.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz551

noncomputable def Ns528p1856 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 920519 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns528p1847 rfl rfl) (Ns528p1849 rfl rfl)) (Ns528p1850 qz9 qz119 rfl rfl rfl rfl (Ns528p1852 rfl)) (Ns528p1853 qz9 qz137 rfl rfl rfl rfl (Ns528p1855 rfl)) 

noncomputable abbrev qz553 := (RS529to540.d3 qz639 qz647 (@Enclosure.dec_le_dec qz639 qz647 921779 1000 923038 1000 qz642 qz650 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns528p1857 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 37772037226298547322957 18889465931478580854784 124633193993212151389047 Ns528p909 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz639 qz647 921779 1000 923038 1000 qz642 qz650 rfl rfl rfl)

noncomputable abbrev qz282 := qz554

noncomputable def Ns528p1858 := @Enclosure.Real.IsNear.neg_val qz281 37772037226298547322957 18889465931478580854784 124633193993212151389047 Ns528p909 (Ns528p1857 (RS529to540.d4 qz134 qz152 qz282) RS529to540.d65) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns528p1859 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz152) Bool.false 108667331979750358456181 151115727451828646838272 Ns528p1029 Ns528p1030 

noncomputable def Ns528p1860 := @Enclosure.Real.IsNear.pos_val qz283 108667331979750358456181 151115727451828646838272 Ns528p1029 Ns528p1030 (Ns528p1859 (RS529to540.d58 qz134 qz152 qz282) RS529to540.d66) rfl 

noncomputable def Ns528p1861 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 913584 1000 921779 1000 

noncomputable def Ns528p1862 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 37772037226298547322957 18889465931478580854784 124633193993212151389047 

noncomputable def Ns528p1863 := @Ns528p1862 Ns528p909 93255129 2147483648 1213 10737418240 (Ns528p1857 (RS529to540.d4 qz134 qz152 qz282) RS529to540.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1864 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz152 913584 1000 923038 1000 

noncomputable def Ns528p1865 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 108667331979750358456181 151115727451828646838272 Ns528p1029 

noncomputable def Ns528p1866 := @Ns528p1865 Ns528p1030 93255129 2147483648 1213 10737418240 (Ns528p1859 (RS529to540.d58 qz134 qz152 qz282) RS529to540.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz553

noncomputable def Ns528p1867 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 921779 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns528p1858 rfl rfl) (Ns528p1860 rfl rfl)) (Ns528p1861 qz9 qz137 rfl rfl rfl rfl (Ns528p1863 rfl)) (Ns528p1864 qz9 qz155 rfl rfl rfl rfl (Ns528p1866 rfl)) 

noncomputable abbrev qz555 := (RS529to540.d3 qz647 qz655 (@Enclosure.dec_le_dec qz647 qz655 923038 1000 924297 1000 qz650 qz659 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns528p1868 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz152) Bool.false 108667331979750358456181 151115727451828646838272 Ns528p1029 Ns528p1030 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz647 qz655 923038 1000 924297 1000 qz650 qz659 rfl rfl rfl)

noncomputable abbrev qz286 := qz556

noncomputable def Ns528p1869 := @Enclosure.Real.IsNear.pos_val qz285 108667331979750358456181 151115727451828646838272 Ns528p1029 Ns528p1030 (Ns528p1868 (RS529to540.d4 qz152 qz170 qz286) RS529to540.d66) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns528p1870 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 6887374790021379136543 2361183241434822606848 125007389672403503370121 Ns528p909 

noncomputable def Ns528p1871 := @Enclosure.Real.IsNear.neg_val qz287 6887374790021379136543 2361183241434822606848 125007389672403503370121 Ns528p909 (Ns528p1870 (RS529to540.d58 qz152 qz170 qz286) RS529to540.d67) rfl 

noncomputable def Ns528p1872 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz152 913584 1000 923038 1000 

noncomputable def Ns528p1873 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 108667331979750358456181 151115727451828646838272 Ns528p1029 

noncomputable def Ns528p1874 := @Ns528p1873 Ns528p1030 93255129 2147483648 1213 10737418240 (Ns528p1868 (RS529to540.d4 qz152 qz170 qz286) RS529to540.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1875 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 913584 1000 924297 1000 

noncomputable def Ns528p1876 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6887374790021379136543 2361183241434822606848 125007389672403503370121 

noncomputable def Ns528p1877 := @Ns528p1876 Ns528p909 93255129 2147483648 1213 10737418240 (Ns528p1870 (RS529to540.d58 qz152 qz170 qz286) RS529to540.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz555

noncomputable def Ns528p1878 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz152 923038 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns528p1869 rfl rfl) (Ns528p1871 rfl rfl)) (Ns528p1872 qz9 qz155 rfl rfl rfl rfl (Ns528p1874 rfl)) (Ns528p1875 qz9 qz175 rfl rfl rfl rfl (Ns528p1877 rfl)) 

noncomputable abbrev qz705 := (@Enclosure.dec_le_dec qz750 qz754 924297 1000 925556 1000 (@Eq.refl Real qz750) (@Eq.refl Real qz754) rfl rfl rfl)

noncomputable abbrev qz557 := (RS529to540.d3 qz655 qz665 qz705)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns528p1879 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 6887374790021379136543 2361183241434822606848 125007389672403503370121 Ns528p909 

noncomputable abbrev qz558 := qz705

noncomputable abbrev qz290 := qz558

noncomputable def Ns528p1880 := @Enclosure.Real.IsNear.neg_val qz289 6887374790021379136543 2361183241434822606848 125007389672403503370121 Ns528p909 (Ns528p1879 (RS529to540.d4 qz170 qz189 qz290) RS529to540.d67) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns528p1881 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz189) Bool.false 770515025293971017433893 151115727451828646838272 Ns528p1284 Ns528p1285 

noncomputable def Ns528p1882 := @Enclosure.Real.IsNear.pos_val qz291 770515025293971017433893 151115727451828646838272 Ns528p1284 Ns528p1285 (Ns528p1881 (RS529to540.d58 qz170 qz189 qz290) RS529to540.d68) rfl 

noncomputable def Ns528p1883 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 913584 1000 924297 1000 

noncomputable def Ns528p1884 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 6887374790021379136543 2361183241434822606848 125007389672403503370121 

noncomputable def Ns528p1885 := @Ns528p1884 Ns528p909 93255129 2147483648 1213 10737418240 (Ns528p1879 (RS529to540.d4 qz170 qz189 qz290) RS529to540.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1886 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz189 913584 1000 925556 1000 

noncomputable def Ns528p1887 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 770515025293971017433893 151115727451828646838272 Ns528p1284 

noncomputable def Ns528p1888 := @Ns528p1887 Ns528p1285 93255129 2147483648 1213 10737418240 (Ns528p1881 (RS529to540.d58 qz170 qz189 qz290) RS529to540.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz557

noncomputable def Ns528p1889 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 924297 1000 qz175 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns528p1880 rfl rfl) (Ns528p1882 rfl rfl)) (Ns528p1883 qz9 qz175 rfl rfl rfl rfl (Ns528p1885 rfl)) (Ns528p1886 qz9 qz192 rfl rfl rfl rfl (Ns528p1888 rfl)) 

noncomputable abbrev qz706 := (@Enclosure.dec_le_dec qz754 qz758 925556 1000 926814 1000 (@Eq.refl Real qz754) qz761 rfl rfl rfl)

noncomputable abbrev qz559 := (RS529to540.d3 qz665 qz675 qz706)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns528p1890 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz189) Bool.false 770515025293971017433893 151115727451828646838272 Ns528p1284 Ns528p1285 

noncomputable abbrev qz560 := qz706

noncomputable abbrev qz294 := qz560

noncomputable def Ns528p1891 := @Enclosure.Real.IsNear.pos_val qz293 770515025293971017433893 151115727451828646838272 Ns528p1284 Ns528p1285 (Ns528p1890 (RS529to540.d4 qz189 qz206 qz294) RS529to540.d68) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns528p1892 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz206) Bool.true 3390156327989646459247 2361183241434822606848 705317950553371424800997 Ns528p234 

noncomputable def Ns528p1893 := @Enclosure.Real.IsNear.neg_val qz295 3390156327989646459247 2361183241434822606848 705317950553371424800997 Ns528p234 (Ns528p1892 (RS529to540.d58 qz189 qz206 qz294) RS529to540.d69) rfl 

noncomputable def Ns528p1894 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz189 913584 1000 925556 1000 

noncomputable def Ns528p1895 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 770515025293971017433893 151115727451828646838272 Ns528p1284 

noncomputable def Ns528p1896 := @Ns528p1895 Ns528p1285 93255129 2147483648 1213 10737418240 (Ns528p1890 (RS529to540.d4 qz189 qz206 qz294) RS529to540.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1897 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz206 913584 1000 926814 1000 

noncomputable def Ns528p1898 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3390156327989646459247 2361183241434822606848 705317950553371424800997 

noncomputable def Ns528p1899 := @Ns528p1898 Ns528p234 93255129 2147483648 1213 10737418240 (Ns528p1892 (RS529to540.d58 qz189 qz206 qz294) RS529to540.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz559

noncomputable def Ns528p1900 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz189 925556 1000 qz192 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns528p1891 rfl rfl) (Ns528p1893 rfl rfl)) (Ns528p1894 qz9 qz192 rfl rfl rfl rfl (Ns528p1896 rfl)) (Ns528p1897 qz9 qz209 rfl rfl rfl rfl (Ns528p1899 rfl)) 

noncomputable abbrev qz707 := (@Enclosure.dec_le_dec qz758 qz763 926814 1000 928072 1000 qz761 qz766 rfl rfl rfl)

noncomputable abbrev qz561 := (RS529to540.d3 qz675 qz685 qz707)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns528p1901 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz206) Bool.true 3390156327989646459247 2361183241434822606848 705317950553371424800997 Ns528p234 

noncomputable abbrev qz562 := qz707

noncomputable abbrev qz298 := qz562

noncomputable def Ns528p1902 := @Enclosure.Real.IsNear.neg_val qz297 3390156327989646459247 2361183241434822606848 705317950553371424800997 Ns528p234 (Ns528p1901 (RS529to540.d4 qz206 qz223 qz298) RS529to540.d69) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns528p1903 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 1197515211105123018765 2361183241434822606848 941993973894644136657553 Ns528p648 

noncomputable def Ns528p1904 := @Enclosure.Real.IsNear.pos_val qz299 1197515211105123018765 2361183241434822606848 941993973894644136657553 Ns528p648 (Ns528p1903 (RS529to540.d58 qz206 qz223 qz298) RS529to540.d70) rfl 

noncomputable def Ns528p1905 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz206 913584 1000 926814 1000 

noncomputable def Ns528p1906 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 3390156327989646459247 2361183241434822606848 705317950553371424800997 

noncomputable def Ns528p1907 := @Ns528p1906 Ns528p234 93255129 2147483648 1213 10737418240 (Ns528p1901 (RS529to540.d4 qz206 qz223 qz298) RS529to540.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1908 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 913584 1000 928072 1000 

noncomputable def Ns528p1909 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1197515211105123018765 2361183241434822606848 941993973894644136657553 

noncomputable def Ns528p1910 := @Ns528p1909 Ns528p648 93255129 2147483648 1213 10737418240 (Ns528p1903 (RS529to540.d58 qz206 qz223 qz298) RS529to540.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz561

noncomputable def Ns528p1911 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz206 926814 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns528p1902 rfl rfl) (Ns528p1904 rfl rfl)) (Ns528p1905 qz9 qz209 rfl rfl rfl rfl (Ns528p1907 rfl)) (Ns528p1908 qz9 qz226 rfl rfl rfl rfl (Ns528p1910 rfl)) 

noncomputable abbrev qz773 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 928072 1000) (Enclosure.sfrac Bool.false 929330 1000) 928072 1000 929330 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 928072 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 929330 1000)) rfl rfl rfl)

noncomputable abbrev qz708 := qz773

noncomputable abbrev qz563 := (RS529to540.d3 qz685 qz695 qz708)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns528p1912 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 1197515211105123018765 2361183241434822606848 941993973894644136657553 Ns528p648 

noncomputable abbrev qz564 := qz708

noncomputable abbrev qz302 := qz564

noncomputable def Ns528p1913 := @Enclosure.Real.IsNear.pos_val qz301 1197515211105123018765 2361183241434822606848 941993973894644136657553 Ns528p648 (Ns528p1912 (RS529to540.d4 qz223 qz240 qz302) RS529to540.d70) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns528p1914 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 42561218845274672305217 37778931862957161709568 Ns528p1663 Ns528p1664 

noncomputable def Ns528p1915 := @Enclosure.Real.IsNear.neg_val qz303 42561218845274672305217 37778931862957161709568 Ns528p1663 Ns528p1664 (Ns528p1914 (RS529to540.d58 qz223 qz240 qz302) RS529to540.d71) rfl 

noncomputable def Ns528p1916 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 913584 1000 928072 1000 

noncomputable def Ns528p1917 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 1197515211105123018765 2361183241434822606848 941993973894644136657553 

noncomputable def Ns528p1918 := @Ns528p1917 Ns528p648 93255129 2147483648 1213 10737418240 (Ns528p1912 (RS529to540.d4 qz223 qz240 qz302) RS529to540.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable def Ns528p1919 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 913584 1000 929330 1000 

noncomputable def Ns528p1920 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 42561218845274672305217 37778931862957161709568 Ns528p1663 

noncomputable def Ns528p1921 := @Ns528p1920 Ns528p1664 93255129 2147483648 1213 10737418240 (Ns528p1914 (RS529to540.d58 qz223 qz240 qz302) RS529to540.d71) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 93255129 2147483648 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS529to540.d60) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz563

noncomputable def Ns528p1922 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 928072 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns528p1913 rfl rfl) (Ns528p1915 rfl rfl)) (Ns528p1916 qz9 qz226 rfl rfl rfl rfl (Ns528p1918 rfl)) (Ns528p1919 qz9 qz243 rfl rfl rfl rfl (Ns528p1921 rfl)) 

noncomputable def Ns528p1923 := @List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns528p1911)) (@List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns528p1922)) (@List.nil RS529to540.d0)) 

noncomputable def Ns528p1924 := @List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns528p1889)) (@List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns528p1900)) Ns528p1923) 

noncomputable def Ns528p1925 := @List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns528p1867)) (@List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns528p1878)) Ns528p1924) 

noncomputable def Ns528p1926 := @List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns528p1845)) (@List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns528p1856)) Ns528p1925) 

noncomputable def Ns528p1927 := @List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns528p1823)) (@List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns528p1834)) Ns528p1926) 

noncomputable def Ns528p1928 := @List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns528p1801)) (@List.cons RS529to540.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns528p1812)) Ns528p1927) 

noncomputable abbrev qz565 := (RS529to540.d2 qz655 qz665 qz705)

noncomputable abbrev qz709 := (RS529to540.d2 qz758 qz763 (@Enclosure.dec_le_dec qz758 qz763 926814 1000 928072 1000 qz761 qz766 rfl rfl rfl))

noncomputable abbrev qz710 := (@List.cons RS529to540.d1 (RS529to540.d2 qz763 qz768 qz773) (@List.nil RS529to540.d1))

noncomputable abbrev qz566 := (@List.cons RS529to540.d1 (RS529to540.d2 qz665 qz675 qz706) (@List.cons RS529to540.d1 qz709 qz710))

noncomputable abbrev qz305 := (@List.cons RS529to540.d1 (RS529to540.d2 qz469 qz481 qz556) (@List.cons RS529to540.d1 qz565 qz566))

noncomputable def Ns528p1929 := @List.cons RS529to540.d1 (RS529to540.d2 qz116 qz134 qz278) (@List.cons RS529to540.d1 (RS529to540.d2 qz134 qz152 qz282) qz305) 

noncomputable abbrev qz306 := (RS529to540.d2 qz433 qz445 qz550)

noncomputable def Ns528p1930 := @List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 qz306 (RS529to540.d2 qz116 qz134 qz278) (@List.cons RS529to540.d1 (RS529to540.d2 qz134 qz152 qz282) qz305) 

noncomputable def Ns528p1931 := @List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 (RS529to540.d2 qz116 qz134 qz278) (RS529to540.d2 qz134 qz152 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 921779 1000 921779 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS529to540.d2 qz469 qz481 qz556)

noncomputable abbrev qz308 := qz565

noncomputable abbrev qz309 := qz566

noncomputable abbrev qz567 := (RS529to540.d2 qz665 qz675 qz706)

noncomputable abbrev qz310 := qz567

noncomputable abbrev qz568 := (@List.cons RS529to540.d1 qz709 qz710)

noncomputable abbrev qz311 := qz568

noncomputable abbrev qz569 := qz709

noncomputable abbrev qz312 := qz569

noncomputable abbrev qz570 := qz710

noncomputable abbrev qz313 := qz570

noncomputable abbrev qz711 := (RS529to540.d2 qz763 qz768 qz773)

noncomputable abbrev qz571 := qz711

noncomputable abbrev qz314 := qz571

noncomputable def Ns528p1932 := @List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 924297 1000 924297 1000 qz175 qz175 rfl rfl rfl) (@List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz189 qz189 925556 1000 925556 1000 qz192 qz192 rfl rfl rfl) (@List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz206 qz206 926814 1000 926814 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 qz312 qz314 (@List.nil RS529to540.d1) (@Enclosure.dec_le_dec qz223 qz223 928072 1000 928072 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS529to540.d1 RS529to540.d72 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS529to540.d1 qz565 qz566)

noncomputable def Ns528p1933 := @List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 (RS529to540.d2 qz134 qz152 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz152 qz152 923038 1000 923038 1000 qz155 qz155 rfl rfl rfl) Ns528p1932 

noncomputable def Ns528p1934 := @List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 (RS529to540.d2 qz4 qz35 qz258) (RS529to540.d2 qz35 qz62 qz262) (@List.cons RS529to540.d1 (RS529to540.d2 qz62 qz80 qz266) (@List.cons RS529to540.d1 (RS529to540.d2 qz80 qz98 qz270) (@List.cons RS529to540.d1 qz306 Ns528p1929))) (@Enclosure.dec_le_dec qz35 qz35 915477 1000 915477 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 (RS529to540.d2 qz35 qz62 qz262) (RS529to540.d2 qz62 qz80 qz266) (@List.cons RS529to540.d1 (RS529to540.d2 qz80 qz98 qz270) (@List.cons RS529to540.d1 qz306 Ns528p1929)) (@Enclosure.dec_le_dec qz62 qz62 916738 1000 916738 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 (RS529to540.d2 qz62 qz80 qz266) (RS529to540.d2 qz80 qz98 qz270) (@List.cons RS529to540.d1 qz306 Ns528p1929) (@Enclosure.dec_le_dec qz80 qz80 917999 1000 917999 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS529to540.d1 RS529to540.d72 (RS529to540.d2 qz80 qz98 qz270) qz306 Ns528p1929 (@Enclosure.dec_le_dec qz98 qz98 919259 1000 919259 1000 qz101 qz101 rfl rfl rfl) (Ns528p1930 (@Enclosure.dec_le_dec qz116 qz116 920519 1000 920519 1000 qz119 qz119 rfl rfl rfl) (Ns528p1931 Ns528p1933))))) 

noncomputable abbrev qz572 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz573 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns528p1928 Ns528p1934)

noncomputable abbrev qz574 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns528p1928 Ns528p1934))

theorem RS529to540.d73 : Zeta.Certificates.BatchSpec 12 913584 1000 929330 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz572 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz572 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz572 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz573 (@And.intro (@Eq Nat (@List.length qz572 qz574) 12) (And (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz572 qz574)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz572 qz574)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz572 qz574)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz572 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz572 qz574)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 913584 1000 929330 1000 := RS529to540.d73
#print axioms solution
#check solution
