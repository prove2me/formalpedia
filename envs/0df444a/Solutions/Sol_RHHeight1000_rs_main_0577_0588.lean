-- Prove2me | solution 1 for RHHeight1000.rs_main_0577_0588
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:23:24.438659+00:00
-- url     : https://prove2.me/submissions/fb272e65-d17d-4642-a7e7-4af4abf51f86

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

noncomputable def RS577to588.d0 := @PSigma Zeta.Certificates.ZIntervalRS fun (I : Zeta.Certificates.ZIntervalRS) => Zeta.Certificates.ZIntervalRS.Certified I 

noncomputable def RS577to588.d1 := @NonemptyInterval Real Real.instLE 

noncomputable def RS577to588.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h 

noncomputable def RS577to588.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => RS577to588.d2 a b h 

theorem RS577to588.d4 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS577to588.d3 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (RS577to588.d3 a b h)) 

noncomputable def Ns576p0 := nat_lit 26986075409044028275299783 

noncomputable def Ns576p1 := nat_lit 8589934592000000000000000 

noncomputable def Ns576p2 := nat_lit 26986075409044045455168967 

noncomputable def Ns576p3 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 Ns576p0 Ns576p1 Ns576p2 Ns576p1 614572177 536870912 1 163840000 614572177 536870912 1 163840000 307286088 268435456 3 268435456 BSN.pi_near_15 rfl rfl rfl 

noncomputable def Ns576p4 := nat_lit 53972150818088056550599566 

noncomputable def Ns576p5 := nat_lit 17179869184000000000000000 

noncomputable def Ns576p6 := nat_lit 18396140817044028275299783 

noncomputable def Ns576p7 := nat_lit 35576010001044028275299783 

noncomputable def Ns576p8 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625 

noncomputable def Ns576p9 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575 

noncomputable def Ns576p10 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375 

noncomputable def Ns576p11 := BSN.log_dyadic_bound Ns576p6 Ns576p7 16 15 Ns576p8 536870912 163840000 Ns576p9 Ns576p10 614572177 Ns576p4 Ns576p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns576p6) (BSN.artanhQ Ns576p7) 0 15 Ns576p9 Ns576p8 Ns576p10 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns576p12 := nat_lit 53972150818088090910337934 

noncomputable def Ns576p13 := nat_lit 18396140817044045455168967 

noncomputable def Ns576p14 := nat_lit 35576010001044045455168967 

noncomputable def Ns576p15 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625 

noncomputable def Ns576p16 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575 

noncomputable def Ns576p17 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375 

noncomputable def Ns576p18 := BSN.log_dyadic_bound Ns576p13 Ns576p14 16 15 Ns576p15 536870912 163840000 Ns576p16 Ns576p17 614572177 Ns576p12 Ns576p5 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP Ns576p13) (BSN.artanhQ Ns576p14) 0 15 Ns576p16 Ns576p15 Ns576p17 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable def Ns576p19 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 307286088 268435456 3 268435456 38410761 33554432 3 268435456 (Ns576p3 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac Ns576p0 Ns576p1 614572177 536870912 1 163840000 Bool.false (BSN.logfrac_isNear Ns576p4 Ns576p5 1 Ns576p0 Ns576p1 614572177 536870912 163840000 rfl rfl rfl (Ns576p11 rfl))) (BSN.isNear_log_sfrac Ns576p2 Ns576p1 614572177 536870912 1 163840000 Bool.false (BSN.logfrac_isNear Ns576p12 Ns576p5 1 Ns576p2 Ns576p1 614572177 536870912 163840000 rfl rfl rfl (Ns576p18 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl 

theorem RS577to588.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 3 268435456 := Ns576p19 

noncomputable def Ns576p20 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 33554432 10240000 385100712855 135135 23258159 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz585 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz316 := qz585

noncomputable abbrev qz0 := qz316

theorem RS577to588.d6 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 23258159 33554432 1 10240000 := BSN.isNear_log_sfrac 2 1 23258159 33554432 1 10240000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 23258159 33554432 10240000 rfl rfl rfl (Ns576p20 rfl)) 

theorem RS577to588.d7 : Enclosure.Real.IsNear (Real.log qz0) Bool.false 372130544 536870912 53 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz0) Bool.false 23258159 33554432 1 10240000 372130544 536870912 53 536870912 RS577to588.d6 rfl 

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz586 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz319 := qz586

noncomputable def Ns576p21 := @Enclosure.Real.IsNear.inv_image qz317 94906265 67108864 1 67108864 23726566 23726567 33554432 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz318 qz319)) Bool.false 94906265 67108864 1 67108864 94906265 67108864 1 67108864 (BSN.sqrt_enclosure 2 1 47453132 47453133 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

theorem RS577to588.d8 : Enclosure.Real.IsNear qz320 Bool.false 47453133 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 47453133 67108864 1 67108864 (Ns576p21 rfl rfl) rfl 

theorem RS577to588.d9 : Enclosure.Real.IsNear qz320 Bool.false 379625064 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz320 Bool.false 47453133 67108864 1 67108864 379625064 536870912 8 536870912 RS577to588.d8 rfl 

noncomputable def Ns576p22 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 33554432 10240000 13079757671720842725 316234143225 36863311 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS577to588.d10 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 10240000 := BSN.isNear_log_sfrac 3 1 36863311 33554432 1 10240000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 36863311 33554432 10240000 rfl rfl rfl (Ns576p22 rfl)) 

theorem RS577to588.d11 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 589812976 536870912 53 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 10240000 589812976 536870912 53 536870912 RS577to588.d10 rfl 

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def Ns576p23 := @Enclosure.Real.IsNear.inv_image qz321 116235963 67108864 1 67108864 19372660 19372661 33554432 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz322 qz319)) Bool.false 116235963 67108864 1 67108864 116235963 67108864 1 67108864 (BSN.sqrt_enclosure 3 1 58117981 58117982 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz323 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

theorem RS577to588.d12 : Enclosure.Real.IsNear qz323 Bool.false 38745321 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 38745321 67108864 1 67108864 (Ns576p23 rfl rfl) rfl 

theorem RS577to588.d13 : Enclosure.Real.IsNear qz323 Bool.false 309962568 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz323 Bool.false 38745321 67108864 1 67108864 309962568 536870912 8 536870912 RS577to588.d12 rfl 

noncomputable def Ns576p24 := nat_lit 1181671153346359170692730265957638242378174781758650 

noncomputable def Ns576p25 := nat_lit 5986310706507378352962293074805895248510699696029696 

noncomputable def Ns576p26 := nat_lit 2000000000000000000000000000000000000000000000000000 

noncomputable def Ns576p27 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625 

noncomputable def Ns576p28 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125 

noncomputable def Ns576p29 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875 

noncomputable def Ns576p30 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375 

noncomputable def Ns576p31 := nat_lit 2442358029135994033939875 

noncomputable def Ns576p32 := nat_lit 37260822860694382775919147000 

noncomputable def Ns576p33 := nat_lit 116336546489037573337554931640625 

noncomputable def Ns576p34 := nat_lit 57493278893883548332405996866302358825 

noncomputable def Ns576p35 := nat_lit 40230676762013536063022911548614501953125 

noncomputable def Ns576p36 := nat_lit 236310350532676991248348623960 

noncomputable def Ns576p37 := nat_lit 344268321641720831394195556640625 

noncomputable def Ns576p38 := nat_lit 81801971833623620377505564448994707675 

noncomputable def Ns576p39 := nat_lit 56886557708273976459167897701263427734375 

noncomputable def Ns576p40 := BSN.arctan_dyadic_bound_f 1 5 18 17 Ns576p25 Ns576p26 Ns576p27 Ns576p28 200200021673987500790625 Ns576p29 Ns576p30 Ns576p31 Ns576p24 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 Ns576p32 Ns576p33 151412625 Ns576p34 Ns576p35 1322214852783825 Ns576p27 Ns576p28 200200021673987500790625 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 Ns576p32 Ns576p33 151412625 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 Ns576p34 Ns576p35 1322214852783825 rfl rfl rfl rfl)) (@BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 Ns576p36 Ns576p37 1267389585 Ns576p38 Ns576p39 1927077560082675 Ns576p29 Ns576p30 Ns576p31 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 Ns576p36 Ns576p37 1267389585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 Ns576p38 Ns576p39 1927077560082675 rfl rfl rfl rfl)) rfl 

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 5)

theorem RS577to588.d14 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 qz324)) Bool.false Ns576p24 Ns576p25 1 Ns576p26 := Ns576p40 rfl rfl rfl 

noncomputable def Ns576p41 := nat_lit 25047178968060507272880539293402373975644382030403 

noncomputable def Ns576p42 := nat_lit 4733915408010924740926662591654183582145509 

noncomputable def Ns576p43 := nat_lit 77229300481955664312677298336960122659119574530232845 

noncomputable def Ns576p44 := nat_lit 24516194103503660983641551147684725335332607 

noncomputable def Ns576p45 := nat_lit 186647183216068817672719845704257068688983305564016735 

noncomputable def Ns576p46 := BSN.arctan_dyadic_bound_f 1 239 6 5 Ns576p25 Ns576p26 Ns576p42 Ns576p43 9945 Ns576p44 Ns576p45 65835 Ns576p41 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 Ns576p42 Ns576p43 9945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 Ns576p44 Ns576p45 65835 rfl rfl rfl rfl) rfl rfl rfl 

theorem RS577to588.d15 : Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz319 (@Nat.cast Real Real.instNatCast 239))) Bool.false Ns576p41 Ns576p25 1 Ns576p26 := Ns576p46 rfl 

noncomputable def Ns576p47 := nat_lit 18806549737669504701992162098148602382148218980016788 

noncomputable def Ns576p48 := nat_lit 100000000000000000000000000000000000000000000000000 

theorem RS577to588.d16 : Enclosure.Real.IsNear Real.pi Bool.false Ns576p47 Ns576p25 1 Ns576p48 := BSN.pi_combine Ns576p24 Ns576p41 Ns576p25 Ns576p26 Ns576p48 Ns576p47 rfl rfl rfl rfl RS577to588.d14 RS577to588.d15 

theorem RS577to588.d17 : Enclosure.Real.IsNear Real.pi Bool.false 28296951008113761 9007199254740992 1 9007199254740992 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false Ns576p47 Ns576p25 1 Ns576p48 28296951008113761 9007199254740992 1 9007199254740992 RS577to588.d16 rfl 

noncomputable def Ns576p49 := nat_lit 129013261453190219981479458510875701904296875 

noncomputable def Ns576p50 := nat_lit 20028702544022979302942508184499384445755625 

noncomputable def Ns576p51 := nat_lit 105610919306899072369715234453255625 

noncomputable def Ns576p52 := nat_lit 11743816085855617508865225 

noncomputable def Ns576p53 := nat_lit 24536140990734100341796875 

noncomputable def Ns576p54 := BSN.log_dyadic_bound 3 5 18 17 Ns576p49 33554432 10240000 Ns576p50 Ns576p51 46516319 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 3) (BSN.artanhQ 5) 0 17 8 816252149187356400 5258090972900390625 87256779635025 Ns576p52 Ns576p53 1210346287688420415225 Ns576p50 Ns576p49 Ns576p51 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 3) (BSN.artanhQ 5) 0 8 816252149187356400 5258090972900390625 87256779635025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 3) (BSN.artanhQ 5) 8 17 Ns576p52 Ns576p53 1210346287688420415225 rfl rfl rfl rfl)) rfl rfl 

theorem RS577to588.d18 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 10240000 := BSN.isNear_log_sfrac 4 1 46516319 33554432 1 10240000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 46516319 33554432 10240000 rfl rfl rfl (Ns576p54 rfl rfl)) 

theorem RS577to588.d19 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 744261104 536870912 53 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 10240000 744261104 536870912 53 536870912 RS577to588.d18 rfl 

noncomputable abbrev qz325 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def Ns576p55 := @Enclosure.Real.IsNear.inv_image qz325 134217729 67108864 1 67108864 16777215 16777216 33554432 (@Enclosure.Real.IsNear.of_eq qz325 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz326 qz319)) Bool.false 134217729 67108864 1 67108864 134217729 67108864 1 67108864 (BSN.sqrt_enclosure 4 1 67108864 67108865 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz327 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

theorem RS577to588.d20 : Enclosure.Real.IsNear qz327 Bool.false 33554431 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 33554431 67108864 1 67108864 (Ns576p55 rfl rfl) rfl 

theorem RS577to588.d21 : Enclosure.Real.IsNear qz327 Bool.false 268435448 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz327 Bool.false 33554431 67108864 1 67108864 268435448 536870912 8 536870912 RS577to588.d20 rfl 

noncomputable def Ns576p56 := nat_lit 61697213297292266380244507781205789317049021875 

noncomputable def Ns576p57 := nat_lit 12776162289178456695994184080609776001208236500 

noncomputable def Ns576p58 := nat_lit 57671893776295590731569354191667200000 

noncomputable def Ns576p59 := nat_lit 885951608314392539099884620 

noncomputable def Ns576p60 := nat_lit 1286943652057122751813246125 

noncomputable def Ns576p61 := BSN.log_dyadic_bound 2 3 22 21 Ns576p56 33554432 10240000 Ns576p57 Ns576p58 54003774 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 21 10 9927050056596826020 47940881637414340575 686533194547200 Ns576p59 Ns576p60 84004523356416638976000 Ns576p57 Ns576p56 Ns576p58 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP 2) (BSN.artanhQ 3) 0 10 9927050056596826020 47940881637414340575 686533194547200 rfl rfl rfl rfl) (@BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 10 21 Ns576p59 Ns576p60 84004523356416638976000 rfl rfl rfl rfl)) rfl rfl 

theorem RS577to588.d22 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 10240000 := BSN.isNear_log_sfrac 5 1 54003774 33554432 1 10240000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 10240000 rfl rfl rfl (Ns576p61 rfl rfl)) 

theorem RS577to588.d23 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 864060384 536870912 53 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 10240000 864060384 536870912 53 536870912 RS577to588.d22 rfl 

noncomputable abbrev qz328 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable def Ns576p62 := @Enclosure.Real.IsNear.inv_image qz328 150059981 67108864 1 67108864 15005998 15005999 33554432 (@Enclosure.Real.IsNear.of_eq qz328 (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 qz324 qz319)) Bool.false 150059981 67108864 1 67108864 150059981 67108864 1 67108864 (BSN.sqrt_enclosure 5 1 75029990 75029991 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz329 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

theorem RS577to588.d24 : Enclosure.Real.IsNear qz329 Bool.false 30011997 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 30011997 67108864 1 67108864 (Ns576p62 rfl rfl) rfl 

theorem RS577to588.d25 : Enclosure.Real.IsNear qz329 Bool.false 240095976 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz329 Bool.false 30011997 67108864 1 67108864 240095976 536870912 8 536870912 RS577to588.d24 rfl 

noncomputable def Ns576p63 := nat_lit 2166104270535356806332416 

noncomputable def Ns576p64 := nat_lit 1208925819614629174706176 

noncomputable def Ns576p65 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 33554432 10240000 1420244935680 967680 13605151 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 6) qz586)

theorem RS577to588.d26 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 24414063 250000000000000 := BSN.isNear_log_sfrac 6 1 4034683612241143 2251799813685248 24414063 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false Ns576p63 Ns576p64 1000000020480000 10240000000000000000000 4034683612241143 2251799813685248 24414063 250000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 13605151 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns576p65 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS577to588.d27 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 961943533 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 24414063 250000000000000 961943533 536870912 54 536870912 RS577to588.d26 rfl 

noncomputable abbrev qz331 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable def Ns576p66 := @Enclosure.Real.IsNear.inv_image qz331 164382475 67108864 1 67108864 13698539 13698540 33554432 (@Enclosure.Real.IsNear.of_eq qz331 (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 164382475 67108864 1 67108864 164382475 67108864 1 67108864 (BSN.sqrt_enclosure 6 1 82191237 82191238 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz332 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

theorem RS577to588.d28 : Enclosure.Real.IsNear qz332 Bool.false 27397079 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 27397079 67108864 1 67108864 (Ns576p66 rfl rfl) rfl 

theorem RS577to588.d29 : Enclosure.Real.IsNear qz332 Bool.false 219176632 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz332 Bool.false 27397079 67108864 1 67108864 219176632 536870912 8 536870912 RS577to588.d28 rfl 

noncomputable def Ns576p67 := nat_lit 2352460989330532755046400 

noncomputable def Ns576p68 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 33554432 10240000 11010900719820672 5524329195 18777589 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 7) qz586)

theorem RS577to588.d30 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 24414063 250000000000000 := BSN.isNear_log_sfrac 7 1 4381800050531575 2251799813685248 24414063 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false Ns576p67 Ns576p64 1000000020480000 10240000000000000000000 4381800050531575 2251799813685248 24414063 250000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 18777589 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns576p68 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS577to588.d31 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 1044702541 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 24414063 250000000000000 1044702541 536870912 54 536870912 RS577to588.d30 rfl 

noncomputable abbrev qz334 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable def Ns576p69 := @Enclosure.Real.IsNear.inv_image qz334 177553365 67108864 1 67108864 12682383 12682384 33554432 (@Enclosure.Real.IsNear.of_eq qz334 (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 177553365 67108864 1 67108864 177553365 67108864 1 67108864 (BSN.sqrt_enclosure 7 1 88776682 88776683 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz335 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

theorem RS577to588.d32 : Enclosure.Real.IsNear qz335 Bool.false 25364767 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 25364767 67108864 1 67108864 (Ns576p69 rfl rfl) rfl 

theorem RS577to588.d33 : Enclosure.Real.IsNear qz335 Bool.false 202918136 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz335 Bool.false 25364767 67108864 1 67108864 202918136 536870912 8 536870912 RS577to588.d32 rfl 

noncomputable def Ns576p70 := nat_lit 2513890570116003237199872 

noncomputable def Ns576p71 := BSN.log_dyadic_bound 0 16 1 0 1 33554432 10240000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8) qz586)

theorem RS577to588.d34 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 97656253 1000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 97656253 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false Ns576p70 Ns576p64 1000000030720000 10240000000000000000000 9364972152248037 4503599627370496 97656253 1000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns576p71 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS577to588.d35 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 1116391676 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 97656253 1000000000000000 1116391676 536870912 54 536870912 RS577to588.d34 rfl 

noncomputable abbrev qz337 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable def Ns576p72 := @Enclosure.Real.IsNear.inv_image qz337 189812531 67108864 1 67108864 11863283 11863284 33554432 (@Enclosure.Real.IsNear.of_eq qz337 (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 189812531 67108864 1 67108864 189812531 67108864 1 67108864 (BSN.sqrt_enclosure 8 1 94906265 94906266 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz338 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

theorem RS577to588.d36 : Enclosure.Real.IsNear qz338 Bool.false 23726567 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 23726567 67108864 1 67108864 (Ns576p72 rfl rfl) rfl 

theorem RS577to588.d37 : Enclosure.Real.IsNear qz338 Bool.false 189812536 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz338 Bool.false 23726567 67108864 1 67108864 189812536 536870912 8 536870912 RS577to588.d36 rfl 

noncomputable def Ns576p73 := nat_lit 2656281492024125531619328 

noncomputable def Ns576p74 := BSN.log_dyadic_bound 1 17 3 2 1252815 33554432 10240000 1448 3 3952142 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 9) qz586)

theorem RS577to588.d38 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 97656253 1000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 97656253 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false Ns576p73 Ns576p64 1000000030720000 10240000000000000000000 9895419672221413 4503599627370496 97656253 1000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 3952142 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns576p74 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS577to588.d39 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 1179625948 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 97656253 1000000000000000 1179625948 536870912 54 536870912 RS577to588.d38 rfl 

noncomputable abbrev qz340 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable def Ns576p75 := @Enclosure.Real.IsNear.inv_image qz340 201326593 67108864 1 67108864 11184810 11184811 33554432 (@Enclosure.Real.IsNear.of_eq qz340 (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 201326593 67108864 1 67108864 201326593 67108864 1 67108864 (BSN.sqrt_enclosure 9 1 100663296 100663297 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz341 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

theorem RS577to588.d40 : Enclosure.Real.IsNear qz341 Bool.false 22369621 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 22369621 67108864 1 67108864 (Ns576p75 rfl rfl) rfl 

theorem RS577to588.d41 : Enclosure.Real.IsNear qz341 Bool.false 178956968 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz341 Bool.false 22369621 67108864 1 67108864 178956968 536870912 8 536870912 RS577to588.d40 rfl 

noncomputable def Ns576p76 := nat_lit 2783654566499630094221312 

noncomputable def Ns576p77 := BSN.log_dyadic_bound 2 18 4 3 3571283520 33554432 10240000 14806464 960 7487455 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 10) qz586)

theorem RS577to588.d42 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 97656253 1000000000000000 := BSN.isNear_log_sfrac 10 1 10369921350850277 4503599627370496 97656253 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false Ns576p76 Ns576p64 1000000030720000 10240000000000000000000 10369921350850277 4503599627370496 97656253 1000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 7487455 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns576p77 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS577to588.d43 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 1236190956 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 97656253 1000000000000000 1236190956 536870912 54 536870912 RS577to588.d42 rfl 

noncomputable abbrev qz343 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10))

noncomputable def Ns576p78 := @Enclosure.Real.IsNear.inv_image qz343 212216861 67108864 1 67108864 10610843 10610844 33554432 (@Enclosure.Real.IsNear.of_eq qz343 (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 212216861 67108864 1 67108864 212216861 67108864 1 67108864 (BSN.sqrt_enclosure 10 1 106108430 106108431 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz344 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

theorem RS577to588.d44 : Enclosure.Real.IsNear qz344 Bool.false 21221687 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 21221687 67108864 1 67108864 (Ns576p78 rfl rfl) rfl 

theorem RS577to588.d45 : Enclosure.Real.IsNear qz344 Bool.false 169773496 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz344 Bool.false 21221687 67108864 1 67108864 169773496 536870912 8 536870912 RS577to588.d44 rfl 

noncomputable def Ns576p79 := nat_lit 2898877505641241362038784 

noncomputable def Ns576p80 := BSN.log_dyadic_bound 3 19 5 4 16049467073745 33554432 10240000 135406373544 688905 10685534 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 19) 0 4 135406373544 16049467073745 688905 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 11) qz586)

theorem RS577to588.d46 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 97656253 1000000000000000 := BSN.isNear_log_sfrac 11 1 10799160248194789 4503599627370496 97656253 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false Ns576p79 Ns576p64 1000000030720000 10240000000000000000000 10799160248194789 4503599627370496 97656253 1000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 10685534 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns576p80 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS577to588.d47 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 1287360220 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 97656253 1000000000000000 1287360220 536870912 54 536870912 RS577to588.d46 rfl 

noncomputable abbrev qz346 := (Real.sqrt (@Nat.cast Real Real.instNatCast 11))

noncomputable def Ns576p81 := @Enclosure.Real.IsNear.inv_image qz346 222574921 67108864 1 67108864 10117041 10117042 33554432 (@Enclosure.Real.IsNear.of_eq qz346 (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 222574921 67108864 1 67108864 222574921 67108864 1 67108864 (BSN.sqrt_enclosure 11 1 111287460 111287461 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz347 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

theorem RS577to588.d48 : Enclosure.Real.IsNear qz347 Bool.false 20234083 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 20234083 67108864 1 67108864 (Ns576p81 rfl rfl) rfl 

theorem RS577to588.d49 : Enclosure.Real.IsNear qz347 Bool.false 161872664 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz347 Bool.false 20234083 67108864 1 67108864 161872664 536870912 8 536870912 RS577to588.d48 rfl 

noncomputable def Ns576p82 := nat_lit 3004067793907357885399040 

noncomputable def Ns576p83 := BSN.log_dyadic_bound 4 20 6 5 106444800000000000 33554432 10240000 1454330814136320 990904320 13605151 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 20) 0 5 1454330814136320 106444800000000000 990904320 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz742 := (Enclosure.sfrac Bool.false 12 1)

noncomputable abbrev qz587 := qz742

noncomputable abbrev qz348 := qz587

noncomputable abbrev qz1 := qz348

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12) qz586)

theorem RS577to588.d50 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 11191024608564965 4503599627370496 97656253 1000000000000000 := BSN.isNear_log_sfrac 12 1 11191024608564965 4503599627370496 97656253 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false Ns576p82 Ns576p64 1000000030720000 10240000000000000000000 11191024608564965 4503599627370496 97656253 1000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 13605151 33554432 24973259072661432 36028797018963968 10240000 1000000000000000 rfl rfl rfl rfl (Ns576p83 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl) 

theorem RS577to588.d51 : Enclosure.Real.IsNear (Real.log qz1) Bool.false 1334074092 536870912 54 536870912 := @Enclosure.Real.IsNear.recentre' (Real.log qz1) Bool.false 11191024608564965 4503599627370496 97656253 1000000000000000 1334074092 536870912 54 536870912 RS577to588.d50 rfl 

noncomputable abbrev qz350 := (Real.sqrt (@Nat.cast Real Real.instNatCast 12))

noncomputable def Ns576p84 := @Enclosure.Real.IsNear.inv_image qz350 232471925 67108864 1 67108864 9686330 9686331 33554432 (@Enclosure.Real.IsNear.of_eq qz350 (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz349) Bool.false 232471925 67108864 1 67108864 232471925 67108864 1 67108864 (BSN.sqrt_enclosure 12 1 116235962 116235963 33554432 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl 

noncomputable abbrev qz351 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

theorem RS577to588.d52 : Enclosure.Real.IsNear qz351 Bool.false 19372661 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 19372661 67108864 1 67108864 (Ns576p84 rfl rfl) rfl 

theorem RS577to588.d53 : Enclosure.Real.IsNear qz351 Bool.false 154981288 536870912 8 536870912 := @Enclosure.Real.IsNear.recentre' qz351 Bool.false 19372661 67108864 1 67108864 154981288 536870912 8 536870912 RS577to588.d52 rfl 

theorem RS577to588.d54 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15 

noncomputable abbrev qz743 := (@instHMul Real Real.instMul)

noncomputable abbrev qz588 := (@HMul.hMul Real Real Real qz743 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable abbrev qz352 := qz588

noncomputable abbrev qz2 := qz352

theorem RS577to588.d55 : Enclosure.Real.IsNear qz2 Bool.false 884279719003555 140737488355328 1 500000000000000 := @Enclosure.Real.IsNear.mulLit_ff qz0 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) RS577to588.d54 rfl 

noncomputable abbrev qz353 := (@Inv.inv Real Real.instInv qz588)

noncomputable abbrev qz3 := qz353

theorem RS577to588.d56 : Enclosure.Real.IsNear qz3 Bool.false 10680707 67108864 1 67108864 := @Enclosure.Real.IsNear.recentre' qz3 Bool.false 10680707 67108864 1 67108864 10680707 67108864 1 67108864 (@Enclosure.Real.IsNear.inv_image qz2 884279719003555 140737488355328 1 500000000000000 5340353 5340354 33554432 RS577to588.d55 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable def Ns576p85 := nat_lit 9444732965739290427392000 

noncomputable def Ns576p86 := nat_lit 2439488822412954881595013070848 

noncomputable abbrev qz744 := (Enclosure.sfrac Bool.false 974151 1000)

noncomputable abbrev qz589 := qz744

noncomputable abbrev qz354 := qz589

noncomputable abbrev qz4 := qz354

noncomputable abbrev qz590 := qz743

noncomputable abbrev qz355 := qz590

noncomputable abbrev qz5 := qz355

noncomputable abbrev qz6 := (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12)

noncomputable abbrev qz7 := (@instHPow Real Real Real.instPow)

noncomputable abbrev qz745 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 974151 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz591 := qz745

noncomputable abbrev qz356 := qz591

noncomputable abbrev qz8 := qz356

noncomputable abbrev qz9 := (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real RSCompact.c0 (1 : Real) (4 : Real)))

noncomputable abbrev qz746 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 974151 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz592 := qz746

noncomputable abbrev qz357 := qz592

noncomputable abbrev qz10 := qz357

noncomputable abbrev qz593 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz8 qz9))

noncomputable def Ns576p87 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 qz593 (Zeta.RiemannSiegel.correction qz10)) 24930113 67108864 265995 268435456 8282404269088950312695 75557863725914323419136 24590249107132795589 Ns576p85 Ns576p86 

noncomputable def Ns576p88 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin BSN.quadSignPos 11 12 974151 1000 287 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 1334074092 54 154981288 8 

noncomputable def Ns576p89 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 974151 1000 174 233 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 

noncomputable def Ns576p90 := Ns576p89 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 56132090 214176 Bool.true 299421290 Bool.true 390434450 28296951008113761 1 Bool.false 455516894 Bool.true Bool.false 356917709 Bool.true Bool.true 195529740 

noncomputable def Ns576p91 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 974151 1000 35 109 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 

noncomputable def Ns576p92 := Ns576p91 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 129453770 174910 Bool.true 817597937 Bool.true 12027857 28296951008113761 1 Bool.false 536255090 Bool.false Bool.false 12026850 Bool.true Bool.false 56132090 

noncomputable def Ns576p93 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 974151 1000 142 46 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 

noncomputable def Ns576p94 := Ns576p93 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 89207157 129968 Bool.false 371485407 Bool.false 709941232 28296951008113761 1 Bool.false 413393919 Bool.true Bool.false 132005963 Bool.true Bool.true 129453770 

noncomputable def Ns576p95 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 974151 1000 393 255 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 

noncomputable def Ns576p96 := Ns576p95 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 181668016 76749 Bool.false 755012310 Bool.false 429874101 28296951008113761 1 Bool.false 529625429 Bool.true Bool.false 385390440 Bool.false Bool.false 89207157 

noncomputable def Ns576p97 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz4) qz4 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 974151 1000 823 572 536870912 268435456 9007199254740992 Bool.false 1057200449651 4533 

noncomputable def Ns576p98 := Ns576p97 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 446315512 4589 Bool.false 640981156 Bool.false 257451330 28296951008113761 1 Bool.false 499192720 Bool.false Bool.false 476315647 Bool.false Bool.false 181668016 

noncomputable def Ns576p99 := nat_lit 30315536476664749269011591474552404706171461325131246907537 

noncomputable def Ns576p100 := nat_lit 15394932646273224523269618380862106155994873367363584000 

noncomputable def Ns576p101 := nat_lit 421088063394808951730612109960480000 

noncomputable def Ns576p102 := nat_lit 2461220450848227527086226114998605314880 

noncomputable abbrev qz358 := (@Eq.refl Real qz589)

noncomputable abbrev qz11 := qz358

noncomputable def Ns576p103 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz4 974151 1000 3795881683204 16000000 1948302 4000 2000 Ns576p101 Ns576p102 qz11 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p104 := nat_lit 87308745052794477894753383446710925553773808616377991093706560 

noncomputable abbrev qz747 := (@instHSub Real Real.instSub)

noncomputable abbrev qz594 := qz747

noncomputable abbrev qz359 := qz594

noncomputable abbrev qz595 := (Enclosure.sfrac Bool.false 1 4)

noncomputable abbrev qz748 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz749 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz596 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1948302))))

noncomputable abbrev qz360 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 974151 4000) (Real.log (Enclosure.sfrac Bool.false 3795881683204 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz596))

noncomputable abbrev qz597 := (Enclosure.sfrac Bool.false 974151 2000)

noncomputable abbrev qz12 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz360 qz597) (@HMul.hMul Real Real Real qz355 qz597 (Real.log Real.pi)))

noncomputable def Ns576p105 := @Enclosure.Real.IsNear.addLit_ft_p qz12 (Enclosure.sfrac Bool.true Ns576p101 Ns576p102) 35473763680272052278737 18014398509481984000 138293805578271057 16384000000000000000000 Ns576p101 Ns576p102 0 1 Ns576p104 

noncomputable def Ns576p106 := nat_lit 2380603982387516639374651424768000 

noncomputable abbrev qz13 := (@HSub.hSub Real Real Real qz359 qz360 qz597)

noncomputable def Ns576p107 := @Enclosure.Real.IsNear.subLit_ff_p qz13 (@HMul.hMul Real Real Real qz5 qz597 (Real.log Real.pi)) 45518049693192971507153 18014398509481984000 47956658041143 16000000000000000000 37417881238911 67108864000 2922453 536870912000 Ns576p106 35473763680272052278737 18014398509481984000 

noncomputable def Ns576p108 := nat_lit 18207219877277188602861200 

noncomputable abbrev qz14 := qz360

noncomputable def Ns576p109 := @Enclosure.Real.IsNear.subLit_ff_p qz14 qz597 10858484370879632720989 3602879701896396800 47956658041143 16000000000000000000 974151 2000 0 1 Ns576p108 45518049693192971507153 18014398509481984000 47956658041143 16000000000000000000 

noncomputable def Ns576p110 := nat_lit 24451133083250934304808237937849270272 

noncomputable def Ns576p111 := nat_lit 119701437445148545237647360 

noncomputable def Ns576p112 := nat_lit 9671406556917033397649408 

noncomputable def Ns576p113 := nat_lit 123482107482084049846393145377089992305257063202781244305651104858603000197165969709743097132627779262451848220879713786744641849145165908399317246672386823316543041652705473853810278400 

noncomputable def Ns576p114 := nat_lit 3601558435803044545999049313256694756152121468316146496737051269533053132506250903079561708799916872797906170241400694940779937093291517388170152623292523922934304565921497931097047040 

noncomputable def Ns576p115 := nat_lit 225168536213962669064475128740893040266684271054324460259175279165235339490694668579192342906708927532530865985337807547862417892747292155586147433885739991063224659074414018560 

noncomputable def Ns576p116 := BSN.log_dyadic_bound 1698729683204 5893033683204 8 7 Ns576p113 268435456 81920000 Ns576p114 Ns576p115 159272547 7591763366408 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1698729683204) (BSN.artanhQ 5893033683204) 0 7 Ns576p114 Ns576p113 Ns576p115 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz361 := (Real.log (Enclosure.sfrac Bool.false 3795881683204 16000000))

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def Ns576p117 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 974151 4000) qz361 974151 4000 0 1 55740325453294695 4503599627370496 48828193 4000000000000000 10859898756130496085789 3602879701896396800 47566033039143 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 974151 4000) (BSN.isNear_log_sfrac 3795881683204 16000000 55740325453294695 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3795881683204) qz362)) Bool.false Ns576p111 Ns576p112 1000001392640000 81920000000000000000000 55740325453294695 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3795881683204 16000000 17 7591763366408 4194304000000 159272547 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p118 := BSN.arctan_dyadic_bound_f 1000 1948302 1 0 33554432 10240000 0 1 1 0 1 1 17222 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1948302) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1948302) 0 0 rfl) rfl rfl rfl 

noncomputable abbrev qz598 := qz748

noncomputable abbrev qz363 := qz598

noncomputable abbrev qz15 := qz363

noncomputable abbrev qz599 := qz749

noncomputable abbrev qz364 := qz599

noncomputable abbrev qz16 := qz364

noncomputable abbrev qz750 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz600 := qz750

noncomputable abbrev qz365 := qz600

noncomputable abbrev qz17 := (@Enclosure.Real.IsNear.mulLit_ff qz365 Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def Ns576p119 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1948302))) 884279719003555 562949953421312 1 2000000000000000 17222 33554432 1 10240000 29661808576186072170496 883990781789603 562949953421312 195312501 2000000000000000 qz17 (Ns576p118 rfl) rfl rfl 

noncomputable abbrev qz366 := (@HMul.hMul Real Real Real qz590 qz595 qz596)

noncomputable abbrev qz18 := qz366

noncomputable abbrev qz367 := qz595

noncomputable abbrev qz19 := qz367

noncomputable abbrev qz368 := qz596

noncomputable abbrev qz20 := qz368

noncomputable abbrev qz369 := (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def Ns576p120 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 974151 4000) qz361) qz18 10859898756130496085789 3602879701896396800 47566033039143 16000000000000000000 883990781789603 2251799813685248 195312501 8000000000000000 Ns576p110 10858484370879632720989 3602879701896396800 47956658041143 16000000000000000000 (Ns576p117 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz20 1 4 0 1 883990781789603 562949953421312 195312501 2000000000000000 883990781789603 2251799813685248 195312501 8000000000000000 qz369 Ns576p119 rfl) 

noncomputable def Ns576p121 := @Ns576p105 Ns576p99 Ns576p100 138293805578271057 16384000000000000000000 (@Ns576p107 138293805578271057 16384000000000000000000 (Ns576p109 (Ns576p120 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 974151 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz597 (Real.log Real.pi) 974151 2000 0 1 38410761 33554432 3 268435456 37417881238911 67108864000 2922453 536870912000 (Enclosure.Real.IsNear.const Bool.false 974151 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p101 Ns576p102) 

noncomputable abbrev qz370 := (@instHAdd Real Real.instAdd)

noncomputable def Ns576p122 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns576p99 Ns576p100 138293805578271057 16384000000000000000000 66075028103 33554432 567 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz370 qz12 (Enclosure.sfrac Bool.true Ns576p101 Ns576p102)) Bool.false Ns576p99 Ns576p100 138293805578271057 16384000000000000000000 Ns576p103 (Ns576p121 rfl rfl)) 

noncomputable def Ns576p123 := nat_lit 4746203248643125737947136 

noncomputable def Ns576p124 := nat_lit 4835703278458516698824704 

noncomputable def Ns576p125 := nat_lit 357388447002667415875384369020755343162584622036388197035524631066856032972818353056647840000 

noncomputable def Ns576p126 := nat_lit 46199975943266144436568348213124696692647303168343434164427665391357367878632476496239452487680 

noncomputable def Ns576p127 := nat_lit 109640805868997409281962729756650725622093641249352841507696824090189512662510992100000000 

noncomputable def Ns576p128 := nat_lit 935839847511769617201454931587134178536714429914232040016313953174191208098784954494487200000 

noncomputable def Ns576p129 := nat_lit 846999558959879314670419717240619439365200558086296293014507198841551744441595402431056628940800 

noncomputable abbrev qz371 := (BSN.sinEvenQ 137438953472)

noncomputable abbrev qz372 := (BSN.sinOddQ 137438953472)

noncomputable def Ns576p130 := BSN.sin_dyadic_bound_f 134895209630 137438953472 3 2 67108864 20500001 Ns576p125 Ns576p126 Ns576p127 Ns576p128 Ns576p129 Ns576p127 55789439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 134895209630) qz371 0 2 Ns576p125 Ns576p126 Ns576p127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 134895209630) qz372 0 2 Ns576p128 Ns576p129 Ns576p127 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz373 := (@Nat.cast Real Real.instNatCast 33554432)

noncomputable abbrev qz374 := (@Nat.cast Real Real.instNatCast Ns576p124)

noncomputable def Ns576p131 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz4) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66075028103) qz373) Bool.false 66075028103 33554432 567 67108864 Bool.true 55789439 67108864 1 10240000 (Ns576p122 rfl) (Enclosure.sfrac_false_div 66075028103 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66075028103) qz373) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p123) qz374) 226375608064910080 72057594037927936 Bool.false 55789439 67108864 313 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 66075028103 33554432 226375608064910080 72057594037927936 313 Ns576p123 Ns576p124 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 55789439 67108864 Ns576p123 Ns576p124 134895209630 137438953472 20500001 20480000 (Ns576p130 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p132 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz4) Bool.false Ns576p99 Ns576p100 138293805578271057 16384000000000000000000 1057200449651 536870912 4533 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz4) (@HAdd.hAdd Real Real Real qz370 qz12 (Enclosure.sfrac Bool.true Ns576p101 Ns576p102)) Bool.false Ns576p99 Ns576p100 138293805578271057 16384000000000000000000 Ns576p103 (Ns576p121 rfl rfl)) 

noncomputable def Ns576p133 := Ns576p98 76749 BSN.abs_quadSignPos (BSN.cos_quad_nat3 823 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 499192720 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 572 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 476315647 536870912) qz11 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) Bool.true 55789439 67108864 358471 41943040000 446315512 536870912 4589 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 55789439 67108864 358471 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz4) qz4) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz4)) Bool.true 55789439 67108864 5873188864 687194767360000 55789439 67108864 358471 41943040000 (Ns576p131 rfl rfl) rfl)) rfl) (Ns576p132 rfl) RS577to588.d7 

noncomputable def Ns576p134 := nat_lit 60496585275921246325950265005476376872126659191126025139678001095693039772022553496791793536520723606854472564736 

noncomputable def Ns576p135 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800 

noncomputable def Ns576p136 := nat_lit 4809978601081122175716081329133613860090881687657197232822374449029352763893813461858891372886946150875136 

noncomputable def Ns576p137 := nat_lit 302357348931724348873609782408811144246268341687094471437884943269105610055605823624856564567223198284342253060096 

noncomputable def Ns576p138 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000 

noncomputable abbrev qz375 := (BSN.sinEvenQ 536870912)

noncomputable abbrev qz376 := (BSN.sinOddQ 536870912)

noncomputable def Ns576p139 := BSN.sin_dyadic_bound_f 640981156 536870912 4 3 536870912 268435456 Ns576p134 Ns576p135 Ns576p136 Ns576p137 Ns576p138 Ns576p136 499192720 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 640981156) qz375 0 3 Ns576p134 Ns576p135 Ns576p136 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 640981156) qz376 0 3 Ns576p137 Ns576p138 Ns576p136 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p140 := nat_lit 613172978180649381971278734056045165210408890167436307123708413360800000 

noncomputable def Ns576p141 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720 

noncomputable def Ns576p142 := nat_lit 19300169270235693011173551719109659691916598550978051323984100000000 

noncomputable def Ns576p143 := nat_lit 1839480334203407674527813855064697276311842837305206965268477271882400000 

noncomputable def Ns576p144 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400 

noncomputable abbrev qz377 := (BSN.cosEvenQ 536870912)

noncomputable abbrev qz378 := (BSN.cosOddQ 536870912)

noncomputable def Ns576p145 := BSN.cos_dyadic_bound_f 257451330 536870912 3 2 536870912 268435456 Ns576p140 Ns576p141 Ns576p142 Ns576p143 Ns576p144 Ns576p142 476315647 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 257451330) qz377 0 2 Ns576p140 Ns576p141 Ns576p142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 257451330) qz378 0 2 Ns576p143 Ns576p144 Ns576p142 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p146 := nat_lit 116529452115110219876495522764768046254103668160120158028699392940105190680903385139349599031469761749424294400000 

noncomputable def Ns576p147 := nat_lit 34312186280501853937543392622450008240556960099401605016928684515980579005098462023582791156161000000000000 

noncomputable def Ns576p148 := nat_lit 582181842375176894822978820397090778277164703636679116427184886492603974172717912450520069805862779486417472000000 

noncomputable def Ns576p149 := BSN.sin_dyadic_bound_f 755012310 536870912 4 3 536870912 268435456 Ns576p146 Ns576p135 Ns576p147 Ns576p148 Ns576p138 Ns576p147 529625429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 755012310) qz375 0 3 Ns576p146 Ns576p135 Ns576p147 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 755012310) qz376 0 3 Ns576p148 Ns576p138 Ns576p147 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p150 := nat_lit 8579963380533485785825665760171845753240882008443960585682192625836327265 

noncomputable def Ns576p151 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480 

noncomputable def Ns576p152 := nat_lit 1166085096331994896635617365746025154360386825205151694345111437672801 

noncomputable def Ns576p153 := nat_lit 22469444716003163352091714562810292932047631300588612240710136220577005921 

noncomputable def Ns576p154 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800 

noncomputable def Ns576p155 := BSN.sin_dyadic_bound_f 429874101 536870912 3 2 536870912 268435456 Ns576p150 Ns576p151 Ns576p152 Ns576p153 Ns576p154 Ns576p152 385390440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 429874101) qz375 0 2 Ns576p150 Ns576p151 Ns576p152 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 429874101) qz376 0 2 Ns576p153 Ns576p154 Ns576p152 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p156 := Ns576p96 129968 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 393 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 529625429 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 255 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 385390440 536870912) qz11 rfl rfl (Ns576p133 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p139 rfl rfl) (Ns576p145 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p132 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p149 rfl rfl) (Ns576p155 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p157 := nat_lit 2658367796677080405066222273261508009260117451045801513626955288981018881 

noncomputable def Ns576p158 := nat_lit 362688733469696208082977651343477392542242091846338585275283603462401 

noncomputable def Ns576p159 := nat_lit 7974378012564301822782500864481837072995267868953711863710315299736131841 

noncomputable def Ns576p160 := BSN.cos_dyadic_bound_f 371485407 536870912 3 2 536870912 268435456 Ns576p157 Ns576p141 Ns576p158 Ns576p159 Ns576p144 Ns576p158 413393919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 371485407) qz377 0 2 Ns576p157 Ns576p141 Ns576p158 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 371485407) qz378 0 2 Ns576p159 Ns576p144 Ns576p158 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p161 := nat_lit 35056154161343388832785828606635486419617598084572187951658140052990747953993047476136898104296093462907905376256 

noncomputable def Ns576p162 := nat_lit 274647376664257459544000446540783031995164976078897331880025758552119769180746491160307949742358795015190845849600 

noncomputable def Ns576p163 := nat_lit 16393391044849080246660362535260215041928543967265566284900694960947099208121838829838622851235710999986176 

noncomputable def Ns576p164 := nat_lit 212416325879654475408781480602182177316003091724661277894573647593521824355594913180057787222426377806900363264000 

noncomputable def Ns576p165 := nat_lit 24992911276447428818504040635211255911560012823179657201082344028242898995447930695588023426554650346382366972313600 

noncomputable def Ns576p166 := BSN.cos_dyadic_bound_f 709941232 536870912 4 3 536870912 268435456 Ns576p161 Ns576p162 Ns576p163 Ns576p164 Ns576p165 Ns576p163 132005963 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 709941232) qz377 0 3 Ns576p161 Ns576p162 Ns576p163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 709941232) qz378 0 3 Ns576p164 Ns576p165 Ns576p163 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p167 := Ns576p94 174910 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 142 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 413393919 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 46 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 132005963 536870912) qz11 rfl rfl (Ns576p156 rfl rfl) (Ns576p132 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p160 rfl rfl) (Ns576p166 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p168 := nat_lit 160320566479625799752549457207639170186818773068084347955289862400526204323074621967690081554575145324576914319681 

noncomputable def Ns576p169 := nat_lit 89223127749936824767566533792623361226895417846770123402053141015777116805352226655494519496383461473167681 

noncomputable def Ns576p170 := nat_lit 800722640356099880555437596800730652196636798294316045395657882738189696295701754625684029801390375813188576389441 

noncomputable def Ns576p171 := BSN.sin_dyadic_bound_f 817597937 536870912 4 3 536870912 268435456 Ns576p168 Ns576p135 Ns576p169 Ns576p170 Ns576p138 Ns576p169 536255090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 817597937) qz375 0 3 Ns576p168 Ns576p135 Ns576p169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 817597937) qz376 0 3 Ns576p170 Ns576p138 Ns576p169 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p172 := BSN.sin_dyadic_bound_f 12027857 536870912 1 0 536870912 268435456 0 1 1 0 1 1 12026850 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 12027857) qz375 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 12027857) qz376 0 0 rfl) rfl rfl 

noncomputable def Ns576p173 := Ns576p92 214176 BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536255090 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 109 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12026850 536870912) qz11 rfl rfl (Ns576p167 rfl) (Ns576p132 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p171 rfl rfl) (Ns576p172 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p174 := nat_lit 1121875069521117190100322312190722523021040731041977386329193921328800000 

noncomputable def Ns576p175 := nat_lit 64604298759671857558553999193734251522371330169801678516416100000000 

noncomputable def Ns576p176 := nat_lit 3365495999965832226585849828573780100560077450465592555630548931786400000 

noncomputable def Ns576p177 := BSN.cos_dyadic_bound_f 299421290 536870912 3 2 536870912 268435456 Ns576p174 Ns576p141 Ns576p175 Ns576p176 Ns576p144 Ns576p175 455516894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 299421290) qz377 0 2 Ns576p174 Ns576p141 Ns576p175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 299421290) qz378 0 2 Ns576p176 Ns576p144 Ns576p175 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p178 := nat_lit 5838401746970269458975910542972295070156563512895759222187325628900000000 

noncomputable def Ns576p179 := nat_lit 539989164651204396683490940720194498712674238175288175039062500000000 

noncomputable def Ns576p180 := nat_lit 15290177926274603775913706722451987725983560108817561782016741974500000000 

noncomputable def Ns576p181 := BSN.sin_dyadic_bound_f 390434450 536870912 3 2 536870912 268435456 Ns576p178 Ns576p151 Ns576p179 Ns576p180 Ns576p154 Ns576p179 356917709 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 390434450) qz375 0 2 Ns576p178 Ns576p151 Ns576p179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 390434450) qz376 0 2 Ns576p180 Ns576p154 Ns576p179 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p182 := Ns576p90 249491 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 174 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 455516894 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 356917709 536870912) qz11 rfl rfl (Ns576p173 rfl) (Ns576p132 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p177 rfl rfl) (Ns576p181 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p183 := nat_lit 4117541144795525941278850897178079363684552209851157895158411705712640000 

noncomputable def Ns576p184 := nat_lit 268594222112618077567460964592188453492329608806817311234457600000000 

noncomputable def Ns576p185 := nat_lit 10783601464771528464557119317714201456915792015957821545006222488371200000 

noncomputable def Ns576p186 := BSN.sin_dyadic_bound_f 357797320 536870912 3 2 536870912 268435456 Ns576p183 Ns576p151 Ns576p184 Ns576p185 Ns576p154 Ns576p184 331893101 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 357797320) qz375 0 2 Ns576p183 Ns576p151 Ns576p184 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 357797320) qz376 0 2 Ns576p185 Ns576p154 Ns576p184 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz379 := (BSN.cos_quad_nat3 287 rfl)

noncomputable def Ns576p187 := Ns576p88 Bool.true 195529740 249491 Bool.true 357797320 28296951008113761 1 Bool.false 331893101 Bool.false Bool.true 99720452 265995 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 331893101 536870912) qz11 rfl (Ns576p182 rfl) (Ns576p132 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p186 rfl rfl) rfl 

noncomputable def Ns576p188 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) 99720452 536870912 265995 536870912 99720452 536870912 265995 536870912 107074020020584448 24930113 67108864 265995 268435456 (Ns576p187 rfl rfl rfl rfl) 

noncomputable def Ns576p189 := @Enclosure.Real.IsNear.mulLit_ff qz593 (Zeta.RiemannSiegel.correction qz10) 19018151 67108864 1 67108864 435499974160945 1125899906842624 1290125960207 140737488355328000 8282404269088950312695 75557863725914323419136 

noncomputable abbrev qz601 := (@HPow.hPow Real Real Real qz7 qz8 qz9)

noncomputable def Ns576p190 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz601 1 1 0 1 19018151 67108864 1 67108864 19018151 67108864 1 67108864 

noncomputable abbrev qz21 := (@Enclosure.Real.IsNear.of_eq qz356 (@HMul.hMul Real Real Real qz355 qz354 qz353) Bool.false 10404621404757 67108864000 974151 67108864000 (BSN.t_div_two_pi_mk qz354 974151 1000 qz358) (@Enclosure.Real.IsNear.mulLit_ff qz354 qz353 974151 1000 0 1 10680707 67108864 1 67108864 10404621404757 67108864000 974151 67108864000 (Enclosure.Real.IsNear.const Bool.false 974151 1000) RS577to588.d56 rfl))

noncomputable def Ns576p191 := @Enclosure.Real.IsNear.sqrt_image qz8 10404621404757 67108864000 974151 67108864000 417804457 417804497 33554432 qz21 

noncomputable abbrev qz751 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 974151 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz602 := qz751

noncomputable abbrev qz380 := qz602

noncomputable abbrev qz22 := qz380

noncomputable def Ns576p192 := @Enclosure.Real.IsNear.sqrt_image qz22 417804477 33554432 5 8388608 118402665 118402672 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 835608954 67108864 40 67108864 417804477 33554432 5 8388608 (Ns576p191 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz603 := (Real.sqrt qz751)

noncomputable abbrev qz381 := qz603

noncomputable abbrev qz23 := qz381

noncomputable def Ns576p193 := @Enclosure.Real.IsNear.inv_image qz23 236805337 67108864 7 67108864 9509075 9509076 33554432 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 236805337 67108864 7 67108864 236805337 67108864 7 67108864 (Ns576p192 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p194 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz23) Bool.false 19018151 67108864 1 67108864 19018151 67108864 1 67108864 (Ns576p193 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz382 := (@HMul.hMul Real Real Real qz590 qz588 qz592)

noncomputable abbrev qz24 := (Real.cos qz382)

noncomputable abbrev qz604 := (@HMul.hMul Real Real Real qz743 qz746 qz746)

noncomputable abbrev qz605 := (Enclosure.sfrac Bool.false 1 16)

noncomputable abbrev qz383 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz604 qz592) qz605)

noncomputable abbrev qz25 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz383))

noncomputable def Ns576p195 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz10) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz24) qz25) Bool.false 435499974160945 

noncomputable def Ns576p196 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz24) qz25 70344055 67108864 285 

noncomputable abbrev qz26 := (@Neg.neg Real Real.instNeg (Real.cos qz382))

noncomputable def Ns576p197 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz24) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz26)) Bool.true 70344055 67108864 285 67108864 (BSN.inv_eq_neg_inv_neg qz24) 

noncomputable def Ns576p198 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz26) Bool.false 70344055 67108864 285 67108864 70344055 67108864 

noncomputable def Ns576p199 := @Enclosure.Real.IsNear.recentre' qz24 Bool.true 64022462 67108864 661897216 171798691840000 32011231 33554432 40399 10485760000 

noncomputable abbrev qz27 := qz382

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 67108864)

noncomputable def Ns576p200 := @Enclosure.Real.IsNear.cos_image qz27 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 190396763) qz384) Bool.false 190396763 67108864 63 16777216 Bool.true 64022462 67108864 1 

noncomputable def Ns576p201 := nat_lit 134930377077757381239401699 

noncomputable def Ns576p202 := nat_lit 36028797018963968000000000000000 

noncomputable def Ns576p203 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz10 884279719003555 140737488355328 1 500000000000000 15151293 33554432 5 8388608 13397981116580529846615 4722366482869645213696 Ns576p201 

noncomputable def Ns576p204 := @Enclosure.Real.IsNear.subLit_ff_p qz22 qz1 417804477 33554432 5 8388608 12 1 0 1 15151293 15151293 33554432 5 

noncomputable abbrev qz385 := (Enclosure.Real.IsNear.const Bool.false 12 1)

noncomputable def Ns576p205 := @Ns576p204 8388608 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 835608954 67108864 40 67108864 417804477 33554432 5 8388608 (Ns576p191 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p206 := @Enclosure.Real.IsNear.recentre' qz27 Bool.false 13397981116580529846615 4722366482869645213696 Ns576p201 Ns576p202 190396763 67108864 63 16777216 (@Ns576p203 Ns576p202 RS577to588.d55 (Ns576p205 rfl rfl) rfl) 

noncomputable def Ns576p207 := nat_lit 12247255414233802752393216 

noncomputable def Ns576p208 := nat_lit 990891728295034352407101252904938110391549556656837416999682567005167109425317211333749390145 

noncomputable def Ns576p209 := nat_lit 841921880007965887768450634406154743028775352135827126587933886750017154302647634998868801 

noncomputable def Ns576p210 := nat_lit 2593829510109838978200306742295323181441535583531116181556121496815937639768864600179345472321 

noncomputable def Ns576p211 := BSN.sin_dyadic_bound_f 174043967351 137438953472 3 2 67108864 20500001 Ns576p208 Ns576p126 Ns576p209 Ns576p210 Ns576p129 Ns576p209 64022462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 174043967351) qz371 0 2 Ns576p208 Ns576p126 Ns576p209 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 174043967351) qz372 0 2 Ns576p210 Ns576p129 Ns576p209 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast Ns576p112)

noncomputable def Ns576p212 := @Ns576p200 10240000 (Ns576p206 rfl) (Enclosure.sfrac_false_div 190396763 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 190396763) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p207) qz386) 226375608064910080 72057594037927936 Bool.false 64022462 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 190396763 67108864 226375608064910080 72057594037927936 0 Ns576p207 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 64022462 67108864 Ns576p207 Ns576p112 174043967351 137438953472 20500001 20480000 (Ns576p211 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p213 := @Enclosure.Real.IsNear.inv_image qz26 32011231 33554432 40399 10485760000 35171885 35172170 33554432 (@Enclosure.Real.IsNear.neg qz24 Bool.true 32011231 33554432 40399 10485760000 (Ns576p199 (Ns576p212 rfl rfl) rfl)) 

noncomputable def Ns576p214 := Ns576p197 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz26) Bool.false 70344055 67108864 285 67108864 (@Ns576p198 285 67108864 (Ns576p213 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p215 := @Enclosure.Real.IsNear.recentre' qz25 Bool.true 12381998 33554432 

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz355 qz352 qz383)

noncomputable def Ns576p216 := @Enclosure.Real.IsNear.cos_image qz28 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 130777889)) qz384) Bool.true 130777889 67108864 

noncomputable def Ns576p217 := nat_lit 308790562135864464342872120005 

noncomputable def Ns576p218 := nat_lit 158456325028528675187087900672 

noncomputable def Ns576p219 := nat_lit 4308127107540428633014913330066549 

noncomputable def Ns576p220 := @Enclosure.Real.IsNear.recentre' qz28 Bool.true Ns576p217 Ns576p218 Ns576p219 

noncomputable def Ns576p221 := nat_lit 604462909807314587353088000000000000000 

noncomputable abbrev qz29 := qz383

noncomputable def Ns576p222 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz29 884279719003555 140737488355328 1 500000000000000 349200095286391 

noncomputable abbrev qz387 := (@HSub.hSub Real Real Real qz594 qz604 qz592)

noncomputable abbrev qz30 := qz387

noncomputable abbrev qz388 := qz605

noncomputable abbrev qz31 := qz388

noncomputable def Ns576p223 := @Enclosure.Real.IsNear.subLit_tf qz30 qz31 278831351108727 1125899906842624 159642595 140737488355328 1 16 

noncomputable abbrev qz389 := qz604

noncomputable abbrev qz32 := qz389

noncomputable def Ns576p224 := @Enclosure.Real.IsNear.subLit_ff_n qz32 qz10 229561679571849 1125899906842624 75756515 140737488355328 15151293 33554432 5 8388608 

noncomputable def Ns576p225 := @Enclosure.Real.IsNear.mulLit_ff qz10 qz10 15151293 33554432 5 8388608 15151293 33554432 5 8388608 229561679571849 1125899906842624 

noncomputable def Ns576p226 := nat_lit 2422249264189418915820736952501831582916366123261850202934467604804784877781302128189153827347421244801 

noncomputable def Ns576p227 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600 

noncomputable def Ns576p228 := nat_lit 25027177460753420627114020589622057190208678445469205298411049093939744762595103482944334119873921 

noncomputable def Ns576p229 := nat_lit 14611470614522529089525669903401330993009507343322369849769689830130433609816425493288555859345053363585 

noncomputable def Ns576p230 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600 

noncomputable abbrev qz606 := (BSN.cosEvenQ 67108864)

noncomputable def Ns576p231 := BSN.cos_dyadic_bound_t 130777889 67108864 4 3 33554432 10240000 Ns576p226 Ns576p227 Ns576p228 Ns576p229 Ns576p230 Ns576p228 12381998 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 130777889) qz606 0 3 Ns576p226 Ns576p227 Ns576p228 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 130777889) (BSN.cosOddQ 67108864) 0 3 Ns576p229 Ns576p230 Ns576p228 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz390 := (Enclosure.Real.IsNear.const Bool.false 1 16)

noncomputable def Ns576p232 := @Ns576p215 155697152 21474836480000 6190999 16777216 9503 1310720000 (@Ns576p216 15 2097152 Bool.true 12381998 33554432 1 10240000 (@Ns576p220 Ns576p221 130777889 67108864 15 2097152 (@Ns576p222 1125899906842624 159642595 140737488355328 Ns576p217 Ns576p218 Ns576p219 Ns576p221 RS577to588.d55 (@Ns576p223 0 1 5587201524582256 349200095286391 1125899906842624 159642595 140737488355328 (@Ns576p224 9356027610245904728064 278831351108727 1125899906842624 159642595 140737488355328 (@Ns576p225 75756515 140737488355328 (Ns576p205 rfl rfl) (Ns576p205 rfl rfl) rfl) (Ns576p205 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 130777889 67108864) (BSN.cos_neg_of_bound 130777889 67108864 Bool.true 12381998 33554432 1 10240000 (Ns576p231 rfl rfl)) rfl rfl) 

noncomputable abbrev qz33 := (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real RSCompact.c1 (@Neg.neg Real Real.instNeg (1 : Real)) 12) (Enclosure.sfrac Bool.false 1 1) Bool.false 1 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1))

noncomputable def Ns576p233 := @Ns576p189 24590249107132795589 Ns576p85 (Ns576p190 qz33 (@Enclosure.Real.IsNear.of_eq qz601 (@Inv.inv Real Real.instInv qz23) Bool.false 19018151 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz8 (BSN.t_div_two_pi_nonneg qz4 974151 1000 qz11)) Ns576p194) rfl) (@Ns576p195 1125899906842624 1290125960207 140737488355328000 (BSN.correction_mk qz10 (BSN.cos_two_pi_p_ne_zero_mk qz4 974151 1000 12 qz11 rfl rfl (@BSN.floor_sqrt_eq_dec qz4 974151 1000 12 qz11 rfl rfl rfl))) (@Ns576p196 67108864 6190999 16777216 9503 1310720000 435499974160945 1125899906842624 1290125960207 140737488355328000 Ns576p214 (Ns576p232 rfl) rfl)) 

noncomputable abbrev qz34 := qz359

noncomputable def Ns576p234 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (hardyZApproximantRS₀ qz4) Bool.true 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns576p85 (@Eq.refl Real (hardyZApproximantRS₀ qz4)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz4) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HMul.hMul Real Real Real qz5 qz593 (Zeta.RiemannSiegel.correction qz10))) Bool.true 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns576p85 (BSN.hardyZApproximantRS₀_eq qz4 12 (@BSN.floor_sqrt_eq_dec qz4 974151 1000 12 qz11 rfl rfl rfl)) (@Ns576p87 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns576p85 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz4) qz4 12)) Bool.true 24930113 67108864 265995 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz4) qz4 12) (Ns576p188 (Ns576p187 rfl rfl rfl rfl) rfl rfl)) (Ns576p233 rfl) rfl rfl)) 

theorem RS577to588.d57 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz4) Bool.true 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns576p85 := Ns576p234 

theorem RS577to588.d58 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS577to588.d3 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (RS577to588.d3 a b h)) 

noncomputable def Ns576p235 := nat_lit 4722366482869645213696000 

noncomputable def Ns576p236 := nat_lit 231822593363762111364894556160 

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 975630 1000)

noncomputable abbrev qz607 := qz752

noncomputable abbrev qz391 := qz607

noncomputable abbrev qz35 := qz391

noncomputable abbrev qz753 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 975630 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz608 := qz753

noncomputable abbrev qz392 := qz608

noncomputable abbrev qz36 := qz392

noncomputable abbrev qz754 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 975630 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz609 := qz754

noncomputable abbrev qz393 := qz609

noncomputable abbrev qz37 := qz393

noncomputable abbrev qz610 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz36 qz9))

noncomputable def Ns576p237 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HMul.hMul Real Real Real qz5 qz610 (Zeta.RiemannSiegel.correction qz37)) 6594159 4194304 66599 67108864 4124090717016130241563 37778931862957161709568 12164094895570651969 Ns576p235 Ns576p236 

noncomputable def Ns576p238 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin BSN.quadSignPos 11 12 975630 1000 287 536870912 268435456 9007199254740992 Bool.false 1059203176745 4539 1334074092 54 154981288 8 

noncomputable def Ns576p239 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 975630 1000 174 233 536870912 268435456 9007199254740992 Bool.false 1059203176745 4539 

noncomputable def Ns576p240 := Ns576p239 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 581964246 214499 Bool.true 125020620 Bool.true 291713121 28296951008113761 1 Bool.false 522379858 Bool.true Bool.false 277569401 Bool.true Bool.false 333082903 

noncomputable def Ns576p241 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 975630 1000 35 108 536870912 268435456 9007199254740992 Bool.false 1059203176745 4539 

noncomputable def Ns576p242 := Ns576p241 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 357957526 175174 Bool.true 466014132 Bool.true 597282396 28296951008113761 1 Bool.false 409659356 Bool.false Bool.false 237510790 Bool.false Bool.false 581964246 

noncomputable def Ns576p243 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 975630 1000 143 47 536870912 268435456 9007199254740992 Bool.false 1059203176745 4539 

noncomputable def Ns576p244 := Ns576p243 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 198854876 130165 Bool.false 108183160 Bool.false 324238412 28296951008113761 1 Bool.false 107452515 Bool.false Bool.false 304884059 Bool.false Bool.false 357957526 

noncomputable def Ns576p245 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 3 4 5 975630 1000 394 256 536870912 268435456 9007199254740992 Bool.false 1059203176745 4539 

noncomputable def Ns576p246 := Ns576p245 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 12831456 76866 Bool.false 813662375 Bool.false 311341030 28296951008113761 1 Bool.false 29637407 Bool.true Bool.false 449096631 Bool.false Bool.false 198854876 

noncomputable def Ns576p247 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz35) qz35 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 975630 1000 825 573 536870912 268435456 9007199254740992 Bool.false 1059203176745 4539 

noncomputable def Ns576p248 := Ns576p247 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 536870832 4597 Bool.false 406697462 Bool.false 544530176 28296951008113761 1 Bool.false 368900764 Bool.true Bool.false 455853499 Bool.true Bool.false 12831456 

noncomputable def Ns576p249 := nat_lit 3065069913886885787565136215809325773363791044361777 

noncomputable def Ns576p250 := nat_lit 1553570567139504270540519660018827759709690265600 

noncomputable def Ns576p251 := nat_lit 424294358134567166078642064000000000 

noncomputable def Ns576p252 := nat_lit 2483726132186265977506543290361920000000 

noncomputable abbrev qz611 := (@Eq.refl Real qz752)

noncomputable abbrev qz394 := qz611

noncomputable abbrev qz38 := qz394

noncomputable def Ns576p253 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz35 975630 1000 3807416587600 16000000 1951260 4000 2000 Ns576p251 Ns576p252 qz38 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p254 := nat_lit 8827401351994231068187592301530858227287718207761917760000000 

noncomputable abbrev qz612 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1951260))))

noncomputable abbrev qz395 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 975630 4000) (Real.log (Enclosure.sfrac Bool.false 3807416587600 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz612))

noncomputable abbrev qz613 := (Enclosure.sfrac Bool.false 975630 2000)

noncomputable abbrev qz39 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz395 qz613) (@HMul.hMul Real Real Real qz355 qz613 (Real.log Real.pi)))

noncomputable def Ns576p255 := @Enclosure.Real.IsNear.addLit_ft_p qz39 (Enclosure.sfrac Bool.true Ns576p251 Ns576p252) 3554096404568081865853 1801439850948198400 13850316217539741 1638400000000000000000 Ns576p251 Ns576p252 0 1 Ns576p254 

noncomputable def Ns576p256 := nat_lit 23851137225704838467639522099200 

noncomputable abbrev qz40 := (@HSub.hSub Real Real Real qz359 qz395 qz613)

noncomputable def Ns576p257 := @Enclosure.Real.IsNear.subLit_ff_p qz40 (@HMul.hMul Real Real Real qz5 qz613 (Real.log Real.pi)) 4560049974680521972861 1801439850948198400 4802887493859 1600000000000000000 3747469075443 6710886400 292689 53687091200 Ns576p256 3554096404568081865853 1801439850948198400 

noncomputable def Ns576p258 := nat_lit 9120099949361043945722000 

noncomputable abbrev qz41 := qz395

noncomputable def Ns576p259 := @Enclosure.Real.IsNear.subLit_ff_p qz41 qz613 5438819355570817375357 1801439850948198400 4802887493859 1600000000000000000 975630 2000 0 1 Ns576p258 4560049974680521972861 1801439850948198400 4802887493859 1600000000000000000 

noncomputable def Ns576p260 := nat_lit 12247132411542087159852234873069633536 

noncomputable def Ns576p261 := nat_lit 119730782323859739086159872 

noncomputable def Ns576p262 := nat_lit 126909317760034076410432923425000957316589966003954743112032520119896909777448099715558911533123775021867766188968431918955357846950663932755072792987172864000000000000000000000000000000 

noncomputable def Ns576p263 := nat_lit 3739250350164324401516164745324877555420057096229784746171505935938096133564031497188478472345244204889883504569237141832161646084140004582605853020284518400000000000000000000000000000 

noncomputable def Ns576p264 := nat_lit 247544962875001201423174761945604983231597107920032380699455126120902552348944332122352481392916418320730152488354211724612415623311401675587688857600000000000000000000000000000 

noncomputable def Ns576p265 := BSN.log_dyadic_bound 1710264587600 5904568587600 8 7 Ns576p262 268435456 81920000 Ns576p263 Ns576p264 160087031 7614833175200 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1710264587600) (BSN.artanhQ 5904568587600) 0 7 Ns576p263 Ns576p262 Ns576p264 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz396 := (Real.log (Enclosure.sfrac Bool.false 3807416587600 16000000))

noncomputable def Ns576p266 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 975630 4000) qz396 975630 4000 0 1 55753990227291239 4503599627370496 48828193 4000000000000000 5439526548545215150557 1801439850948198400 4763824993659 1600000000000000000 (Enclosure.Real.IsNear.const Bool.false 975630 4000) (BSN.isNear_log_sfrac 3807416587600 16000000 55753990227291239 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3807416587600) qz362)) Bool.false Ns576p261 Ns576p112 1000001392640000 81920000000000000000000 55753990227291239 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3807416587600 16000000 17 7614833175200 4194304000000 160087031 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p265 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p267 := BSN.arctan_dyadic_bound_f 1000 1951260 1 0 33554432 10240000 0 1 1 0 1 1 17196 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1951260) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1951260) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p268 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1951260))) 884279719003555 562949953421312 1 2000000000000000 17196 33554432 1 10240000 29661823212884861124608 883991217997219 562949953421312 195312501 2000000000000000 qz17 (Ns576p267 rfl) rfl rfl 

noncomputable abbrev qz397 := (@HMul.hMul Real Real Real qz590 qz595 qz612)

noncomputable abbrev qz42 := qz397

noncomputable abbrev qz398 := qz612

noncomputable abbrev qz43 := qz398

noncomputable def Ns576p269 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 975630 4000) qz396) qz42 5439526548545215150557 1801439850948198400 4763824993659 1600000000000000000 883991217997219 2251799813685248 195312501 8000000000000000 Ns576p260 5438819355570817375357 1801439850948198400 4802887493859 1600000000000000000 (Ns576p266 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz43 1 4 0 1 883991217997219 562949953421312 195312501 2000000000000000 883991217997219 2251799813685248 195312501 8000000000000000 qz369 Ns576p268 rfl) 

noncomputable def Ns576p270 := @Ns576p255 Ns576p249 Ns576p250 13850316217539741 1638400000000000000000 (@Ns576p257 13850316217539741 1638400000000000000000 (Ns576p259 (Ns576p269 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 975630 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz613 (Real.log Real.pi) 975630 2000 0 1 38410761 33554432 3 268435456 3747469075443 6710886400 292689 53687091200 (Enclosure.Real.IsNear.const Bool.false 975630 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p251 Ns576p252) 

noncomputable def Ns576p271 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns576p249 Ns576p250 13850316217539741 1638400000000000000000 132400397093 67108864 71 8388608 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz370 qz39 (Enclosure.sfrac Bool.true Ns576p251 Ns576p252)) Bool.false Ns576p249 Ns576p250 13850316217539741 1638400000000000000000 Ns576p253 (Ns576p270 rfl rfl)) 

noncomputable def Ns576p272 := nat_lit 15186710721277126294634496 

noncomputable def Ns576p273 := nat_lit 14361045858147224087852935964761525452776415572983020526617152058278857374743106192505720607296915777675620478627536305887580481484149688755121 

noncomputable def Ns576p274 := nat_lit 282877490902138091004622673603363019119652456796264491099280832830873987773707601701812303598028785564314492868916806270538811366318583631052800 

noncomputable def Ns576p275 := nat_lit 10209560327511106396466764098068137720033409397943594516722513706137317251385554399812782818695128925672406532427656636723989176217625521 

noncomputable def Ns576p276 := nat_lit 71716121983861330784563200063906431374672357026050726142041136712690038478744381480201545150254914775710441871930629863964333542617896347100081 

noncomputable def Ns576p277 := nat_lit 9900712181574833185161793576117705669187835987869257188474829149080589572079766059563430625931007494751007250412088219468858397821150427086848000 

noncomputable def Ns576p278 := BSN.sin_dyadic_bound_f 215816139661 137438953472 4 3 67108864 20500001 Ns576p273 Ns576p274 Ns576p275 Ns576p276 Ns576p277 Ns576p275 67108854 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215816139661) qz371 0 3 Ns576p273 Ns576p274 Ns576p275 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215816139661) qz372 0 3 Ns576p276 Ns576p277 Ns576p275 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p279 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz35) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 132400397093) qz384) Bool.false 132400397093 67108864 71 8388608 Bool.false 67108854 67108864 1 10240000 (Ns576p271 rfl) (Enclosure.sfrac_false_div 132400397093 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 132400397093) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p272) qz386) 226375608064910080 72057594037927936 Bool.false 67108854 67108864 313 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q3 132400397093 67108864 226375608064910080 72057594037927936 313 Ns576p272 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108854 67108864 Ns576p272 Ns576p112 215816139661 137438953472 20500001 20480000 (Ns576p278 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p280 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz35) Bool.false Ns576p249 Ns576p250 13850316217539741 1638400000000000000000 1059203176745 536870912 4539 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz35) (@HAdd.hAdd Real Real Real qz370 qz39 (Enclosure.sfrac Bool.true Ns576p251 Ns576p252)) Bool.false Ns576p249 Ns576p250 13850316217539741 1638400000000000000000 Ns576p253 (Ns576p270 rfl rfl)) 

noncomputable def Ns576p281 := Ns576p248 76866 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 825 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 368900764 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 573 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 455853499 536870912) qz38 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) Bool.false 33554427 33554432 44887 5242880000 536870832 536870912 4597 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 33554427 33554432 44887 5242880000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz35) qz35) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz35)) Bool.false 67108854 67108864 735428608 85899345920000 33554427 33554432 44887 5242880000 (Ns576p279 rfl rfl) rfl)) rfl) (Ns576p280 rfl) RS577to588.d7 

noncomputable def Ns576p282 := nat_lit 6873760947316030498080268361995614395361222385880957885036344194270880000 

noncomputable def Ns576p283 := nat_lit 748465346465085237900558230992928212564004788480158453374093312778496 

noncomputable def Ns576p284 := nat_lit 18001495441933422118872673377614525342173335955268778966170676738679234816 

noncomputable def Ns576p285 := BSN.sin_dyadic_bound_f 406697462 536870912 3 2 536870912 268435456 Ns576p282 Ns576p151 Ns576p283 Ns576p284 Ns576p154 Ns576p283 368900764 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 406697462) qz375 0 2 Ns576p282 Ns576p151 Ns576p283 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 406697462) qz376 0 2 Ns576p284 Ns576p154 Ns576p283 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p286 := nat_lit 22095358543464825915251781347488867516241837614900698169208270977698365440 

noncomputable def Ns576p287 := nat_lit 7729930959298367532503407101872577278357829234213511228561782552395776 

noncomputable def Ns576p288 := nat_lit 57856281058949965754416326584305906941230328696455959044032562055553744896 

noncomputable def Ns576p289 := BSN.sin_dyadic_bound_f 544530176 536870912 3 2 536870912 268435456 Ns576p286 Ns576p151 Ns576p287 Ns576p288 Ns576p154 Ns576p287 455853499 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 544530176) qz375 0 2 Ns576p286 Ns576p151 Ns576p287 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 544530176) qz376 0 2 Ns576p288 Ns576p154 Ns576p287 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p290 := nat_lit 60565316012483896665223545473144670994328254687221986811678391722977118768281967090059569445003656090582275390625 

noncomputable def Ns576p291 := nat_lit 84203628824327265014817162018184223316474242940331051079960015661973045149210206014686264097690582275390625 

noncomputable def Ns576p292 := nat_lit 366662310246044513375620079523166630164808626009179969671051314461849903240306463806893772222617418650582275390625 

noncomputable def Ns576p293 := BSN.cos_dyadic_bound_f 813662375 536870912 4 3 536870912 268435456 Ns576p290 Ns576p162 Ns576p291 Ns576p292 Ns576p165 Ns576p291 29637407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 813662375) qz377 0 3 Ns576p290 Ns576p162 Ns576p291 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 813662375) qz378 0 3 Ns576p292 Ns576p165 Ns576p291 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p294 := nat_lit 1311485359178888716979439714908371173223521897516473545105140231728800000 

noncomputable def Ns576p295 := nat_lit 88285801226468579158014361027414211793221646224323140794016100000000 

noncomputable def Ns576p296 := nat_lit 3934279505934213213780003116003058691246979249256971989033832662986400000 

noncomputable def Ns576p297 := BSN.cos_dyadic_bound_f 311341030 536870912 3 2 536870912 268435456 Ns576p294 Ns576p141 Ns576p295 Ns576p296 Ns576p144 Ns576p295 449096631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 311341030) qz377 0 2 Ns576p294 Ns576p141 Ns576p295 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 311341030) qz378 0 2 Ns576p296 Ns576p144 Ns576p295 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p298 := Ns576p246 130165 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 394 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 29637407 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 256 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 449096631 536870912) qz38 rfl rfl (Ns576p281 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p285 rfl rfl) (Ns576p289 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p280 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p293 rfl rfl) (Ns576p297 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p299 := nat_lit 136974161849492807209861327360000 

noncomputable def Ns576p300 := nat_lit 9969209968386869046778552952102584320 

noncomputable def Ns576p301 := nat_lit 69784469778708083327449870664718090240 

noncomputable def Ns576p302 := BSN.sin_dyadic_bound_f 108183160 536870912 2 1 536870912 268435456 Ns576p299 Ns576p300 Ns576p299 Ns576p299 Ns576p301 Ns576p299 107452515 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 108183160) qz375 0 1 Ns576p299 Ns576p300 Ns576p299 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 108183160) qz376 0 1 Ns576p299 Ns576p301 Ns576p299 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p303 := nat_lit 2776759362182673537848386700064384747808692173871912154677378848982630400 

noncomputable def Ns576p304 := nat_lit 122156254974781517988882304197362270776390792037617530227699755319296 

noncomputable def Ns576p305 := nat_lit 7272267219398947714764268881199926229155793917905994738629909281064943616 

noncomputable def Ns576p306 := BSN.sin_dyadic_bound_f 324238412 536870912 3 2 536870912 268435456 Ns576p303 Ns576p151 Ns576p304 Ns576p305 Ns576p154 Ns576p304 304884059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 324238412) qz375 0 2 Ns576p303 Ns576p151 Ns576p304 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 324238412) qz376 0 2 Ns576p305 Ns576p154 Ns576p304 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p307 := Ns576p244 175174 BSN.abs_quadSignPos (BSN.cos_quad_nat3 143 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 107452515 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 304884059 536870912) qz38 rfl rfl (Ns576p298 rfl rfl) (Ns576p280 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p302 rfl rfl) (Ns576p306 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p308 := nat_lit 11850567667951321535315186666119030838252278706764321782371384917810544640 

noncomputable def Ns576p309 := nat_lit 2224296589074344896092578210105527064128363552000388772970035559858176 

noncomputable def Ns576p310 := nat_lit 31033599793014007462660386617971576580175950691012842133911675679549751296 

noncomputable def Ns576p311 := BSN.sin_dyadic_bound_f 466014132 536870912 3 2 536870912 268435456 Ns576p308 Ns576p151 Ns576p309 Ns576p310 Ns576p154 Ns576p309 409659356 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 466014132) qz375 0 2 Ns576p308 Ns576p151 Ns576p309 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 466014132) qz376 0 2 Ns576p310 Ns576p154 Ns576p309 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p312 := nat_lit 17546862121873953454635868416850104126246757993460793253119403195199887113736963949866098833682978545619116752896 

noncomputable def Ns576p313 := nat_lit 2061372970484660651180288398589526052236258105162394489586254711504165100221589851428071642596224339542016 

noncomputable def Ns576p314 := nat_lit 106386299522179866188901028645561849465178878161559054594674698207508482589773936762434178354856767571876516986880 

noncomputable def Ns576p315 := BSN.cos_dyadic_bound_f 597282396 536870912 4 3 536870912 268435456 Ns576p312 Ns576p162 Ns576p313 Ns576p314 Ns576p165 Ns576p313 237510790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 597282396) qz377 0 3 Ns576p312 Ns576p162 Ns576p313 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 597282396) qz378 0 3 Ns576p314 Ns576p165 Ns576p313 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p316 := Ns576p242 214499 BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 409659356 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 237510790 536870912) qz38 rfl rfl (Ns576p307 rfl) (Ns576p280 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p311 rfl rfl) (Ns576p315 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p317 := nat_lit 244301758615421331945774003360000 

noncomputable def Ns576p318 := nat_lit 1993841993677373809355710590420516864 

noncomputable def Ns576p319 := nat_lit 29907629905160607140335658856307752960 

noncomputable def Ns576p320 := BSN.cos_dyadic_bound_f 125020620 536870912 2 1 536870912 268435456 Ns576p317 Ns576p318 Ns576p317 Ns576p317 Ns576p319 Ns576p317 522379858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 125020620) qz377 0 1 Ns576p317 Ns576p318 Ns576p317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 125020620) qz378 0 1 Ns576p317 Ns576p319 Ns576p317 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p321 := nat_lit 1819272090302667259328563405062523482672685441806474477504023813966361345 

noncomputable def Ns576p322 := nat_lit 52438192071350821957632536786361526090329997649553958986299090236161 

noncomputable def Ns576p323 := nat_lit 4764675336576965396910687036770859774052887051401714829910275028527706881 

noncomputable def Ns576p324 := BSN.sin_dyadic_bound_f 291713121 536870912 3 2 536870912 268435456 Ns576p321 Ns576p151 Ns576p322 Ns576p323 Ns576p154 Ns576p322 277569401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 291713121) qz375 0 2 Ns576p321 Ns576p151 Ns576p322 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 291713121) qz376 0 2 Ns576p323 Ns576p154 Ns576p322 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p325 := Ns576p240 249867 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 174 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 522379858 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 277569401 536870912) qz38 rfl rfl (Ns576p316 rfl) (Ns576p280 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p320 rfl rfl) (Ns576p324 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p326 := nat_lit 2913765857905717449297370529408087163494070153705380657141117100815810560 

noncomputable def Ns576p327 := nat_lit 134507541609404360370067339292169229650873206333392862883749891670016 

noncomputable def Ns576p328 := nat_lit 7631073758495225712528704610852802868493606131656219085020161573740609536 

noncomputable def Ns576p329 := BSN.sin_dyadic_bound_f 328165808 536870912 3 2 536870912 268435456 Ns576p326 Ns576p151 Ns576p327 Ns576p328 Ns576p154 Ns576p327 308108527 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 328165808) qz375 0 2 Ns576p326 Ns576p151 Ns576p327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 328165808) qz376 0 2 Ns576p328 Ns576p154 Ns576p327 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p330 := Ns576p238 Bool.false 333082903 249867 Bool.true 328165808 28296951008113761 1 Bool.false 308108527 Bool.false Bool.false 422026176 266396 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 308108527 536870912) qz38 rfl (Ns576p325 rfl) (Ns576p280 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p329 rfl rfl) rfl 

noncomputable def Ns576p331 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) 422026176 536870912 266396 536870912 422026176 536870912 266396 536870912 453147155993985024 6594159 4194304 66599 67108864 (Ns576p330 rfl rfl rfl rfl) 

noncomputable def Ns576p332 := @Enclosure.Real.IsNear.mulLit_ff qz610 (Zeta.RiemannSiegel.correction qz37) 19010939 67108864 1 67108864 216932510120417 562949953421312 3192103686563 351843720888320000 4124090717016130241563 37778931862957161709568 

noncomputable abbrev qz614 := (@HPow.hPow Real Real Real qz7 qz36 qz9)

noncomputable def Ns576p333 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz614 1 1 0 1 19010939 67108864 1 67108864 19010939 67108864 1 67108864 

noncomputable def Ns576p334 := @Enclosure.Real.IsNear.sqrt_image qz36 1042041817041 6710886400 97563 6710886400 418121501 418121541 33554432 (@Enclosure.Real.IsNear.of_eq qz36 (@HMul.hMul Real Real Real qz5 qz35 qz3) Bool.false 1042041817041 6710886400 97563 6710886400 (BSN.t_div_two_pi_mk qz35 975630 1000 qz38) (@Enclosure.Real.IsNear.mulLit_ff qz35 qz3 975630 1000 0 1 10680707 67108864 1 67108864 1042041817041 6710886400 97563 6710886400 (Enclosure.Real.IsNear.const Bool.false 975630 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz755 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 975630 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz615 := qz755

noncomputable abbrev qz399 := qz615

noncomputable abbrev qz44 := qz399

noncomputable def Ns576p335 := @Enclosure.Real.IsNear.sqrt_image qz44 418121521 33554432 5 8388608 118447581 118447587 33554432 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 836243042 67108864 40 67108864 418121521 33554432 5 8388608 (Ns576p334 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p336 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz44) 3701487 1048576 3 33554432 9505469 9505470 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz44) Bool.false 236895168 67108864 6 67108864 3701487 1048576 3 33554432 (Ns576p335 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p337 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 19010939 67108864 1 67108864 19010939 67108864 1 67108864 (Ns576p336 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz400 := (@HMul.hMul Real Real Real qz590 qz588 qz609)

noncomputable abbrev qz45 := (Real.cos qz400)

noncomputable abbrev qz616 := (@HMul.hMul Real Real Real qz743 qz754 qz754)

noncomputable abbrev qz401 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz616 qz609) qz605)

noncomputable abbrev qz46 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz401))

noncomputable def Ns576p338 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz37) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz45) qz46) Bool.false 216932510120417 

noncomputable def Ns576p339 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz45) qz46 34588099 33554432 69 

noncomputable abbrev qz47 := (@Neg.neg Real Real.instNeg (Real.cos qz400))

noncomputable def Ns576p340 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz45) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz47)) Bool.true 34588099 33554432 69 16777216 (BSN.inv_eq_neg_inv_neg qz45) 

noncomputable def Ns576p341 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz47) Bool.false 69176198 67108864 276 67108864 34588099 33554432 

noncomputable def Ns576p342 := @Enclosure.Real.IsNear.recentre' qz45 Bool.true 65103312 67108864 661897216 171798691840000 4068957 4194304 40399 10485760000 

noncomputable abbrev qz48 := qz400

noncomputable def Ns576p343 := @Enclosure.Real.IsNear.cos_image qz48 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 194380855) qz384) Bool.false 194380855 67108864 63 16777216 Bool.true 65103312 67108864 1 

noncomputable def Ns576p344 := nat_lit 134930377078438228045098211 

noncomputable def Ns576p345 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz37 884279719003555 140737488355328 1 500000000000000 15468337 33554432 5 8388608 13678336695812292938035 4722366482869645213696 Ns576p344 

noncomputable def Ns576p346 := @Enclosure.Real.IsNear.subLit_ff_p qz44 qz1 418121521 33554432 5 8388608 12 1 0 1 15468337 15468337 33554432 5 

noncomputable def Ns576p347 := @Ns576p346 8388608 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 836243042 67108864 40 67108864 418121521 33554432 5 8388608 (Ns576p334 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p348 := @Enclosure.Real.IsNear.recentre' qz48 Bool.false 13678336695812292938035 4722366482869645213696 Ns576p344 Ns576p202 194380855 67108864 63 16777216 (@Ns576p345 Ns576p202 RS577to588.d55 (Ns576p347 rfl rfl) rfl) 

noncomputable def Ns576p349 := nat_lit 12821423582125315525181440 

noncomputable def Ns576p350 := nat_lit 1190392842260759523746755056837420516308113686442881545006942676734463854264730168652579552065 

noncomputable def Ns576p351 := nat_lit 1214651194311902553863936974644246158141677635177048797182503992302125272502921552499653441 

noncomputable def Ns576p352 := nat_lit 3115728961130246148535245441377153525122354081655355491251316289745582844061669521100327959361 

noncomputable def Ns576p353 := BSN.sin_dyadic_bound_f 182203387767 137438953472 3 2 67108864 20500001 Ns576p350 Ns576p126 Ns576p351 Ns576p352 Ns576p129 Ns576p351 65103312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 182203387767) qz371 0 2 Ns576p350 Ns576p126 Ns576p351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 182203387767) qz372 0 2 Ns576p352 Ns576p129 Ns576p351 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p354 := @Ns576p343 10240000 (Ns576p348 rfl) (Enclosure.sfrac_false_div 194380855 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 194380855) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p349) qz386) 226375608064910080 72057594037927936 Bool.false 65103312 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 194380855 67108864 226375608064910080 72057594037927936 0 Ns576p349 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 65103312 67108864 Ns576p349 Ns576p112 182203387767 137438953472 20500001 20480000 (Ns576p353 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p355 := @Enclosure.Real.IsNear.inv_image qz47 4068957 4194304 40399 10485760000 34587961 34588237 33554432 (@Enclosure.Real.IsNear.neg qz45 Bool.true 4068957 4194304 40399 10485760000 (Ns576p342 (Ns576p354 rfl rfl) rfl)) 

noncomputable def Ns576p356 := Ns576p340 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz47) Bool.false 34588099 33554432 69 16777216 (@Ns576p341 69 16777216 (Ns576p355 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p357 := @Enclosure.Real.IsNear.recentre' qz46 Bool.true 12543766 33554432 

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz355 qz352 qz401)

noncomputable def Ns576p358 := @Enclosure.Real.IsNear.cos_image qz49 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65563177)) qz373) Bool.true 65563177 33554432 

noncomputable def Ns576p359 := nat_lit 309613350250505001127097718845 

noncomputable def Ns576p360 := nat_lit 4350905974001352510034882147339601 

noncomputable def Ns576p361 := @Enclosure.Real.IsNear.recentre' qz49 Bool.true Ns576p359 Ns576p218 Ns576p360 

noncomputable abbrev qz50 := qz401

noncomputable def Ns576p362 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz50 884279719003555 140737488355328 1 500000000000000 350130556651679 

noncomputable abbrev qz402 := (@HSub.hSub Real Real Real qz594 qz616 qz609)

noncomputable abbrev qz51 := qz402

noncomputable def Ns576p363 := @Enclosure.Real.IsNear.subLit_tf qz51 qz31 279761812474015 1125899906842624 161227815 140737488355328 1 16 

noncomputable abbrev qz403 := qz616

noncomputable abbrev qz52 := qz403

noncomputable def Ns576p364 := @Enclosure.Real.IsNear.subLit_ff_n qz52 qz37 239269449545569 1125899906842624 77341735 140737488355328 15468337 33554432 5 8388608 

noncomputable def Ns576p365 := @Enclosure.Real.IsNear.mulLit_ff qz37 qz37 15468337 33554432 5 8388608 15468337 33554432 5 8388608 239269449545569 1125899906842624 

noncomputable def Ns576p366 := nat_lit 597752203570583352939805590045542220169572703414120569172049368257947731159449714622199042829295201 

noncomputable def Ns576p367 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600 

noncomputable def Ns576p368 := nat_lit 6308409551111786440301549213081108565064580439325915038810186661475814540275767254315403943521 

noncomputable def Ns576p369 := nat_lit 3605536603139692290890996783411723314666214864474975014580455686345776122158711347379369724058377825 

noncomputable def Ns576p370 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600 

noncomputable def Ns576p371 := BSN.cos_dyadic_bound_t 65563177 33554432 4 3 33554432 10240000 Ns576p366 Ns576p367 Ns576p368 Ns576p369 Ns576p370 Ns576p368 12543766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65563177) (BSN.cosEvenQ 33554432) 0 3 Ns576p366 Ns576p367 Ns576p368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65563177) (BSN.cosOddQ 33554432) 0 3 Ns576p369 Ns576p370 Ns576p368 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p372 := @Ns576p357 1255817216 171798691840000 6271883 16777216 76649 10485760000 (@Ns576p358 121 16777216 Bool.true 12543766 33554432 1 10240000 (@Ns576p361 Ns576p221 65563177 33554432 121 16777216 (@Ns576p362 1125899906842624 161227815 140737488355328 Ns576p359 Ns576p218 Ns576p360 Ns576p221 RS577to588.d55 (@Ns576p363 0 1 5602088906426864 350130556651679 1125899906842624 161227815 140737488355328 (@Ns576p364 9387248712856088084480 279761812474015 1125899906842624 161227815 140737488355328 (@Ns576p365 77341735 140737488355328 (Ns576p347 rfl rfl) (Ns576p347 rfl rfl) rfl) (Ns576p347 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65563177 33554432) (BSN.cos_neg_of_bound 65563177 33554432 Bool.true 12543766 33554432 1 10240000 (Ns576p371 rfl rfl)) rfl rfl) 

noncomputable def Ns576p373 := @Ns576p332 12164094895570651969 Ns576p235 (Ns576p333 qz33 (@Enclosure.Real.IsNear.of_eq qz614 (@Inv.inv Real Real.instInv (Real.sqrt qz44)) Bool.false 19010939 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz36 (BSN.t_div_two_pi_nonneg qz35 975630 1000 qz38)) Ns576p337) rfl) (@Ns576p338 562949953421312 3192103686563 351843720888320000 (BSN.correction_mk qz37 (BSN.cos_two_pi_p_ne_zero_mk qz35 975630 1000 12 qz38 rfl rfl (@BSN.floor_sqrt_eq_dec qz35 975630 1000 12 qz38 rfl rfl rfl))) (@Ns576p339 16777216 6271883 16777216 76649 10485760000 216932510120417 562949953421312 3192103686563 351843720888320000 Ns576p356 (Ns576p372 rfl) rfl)) 

noncomputable def Ns576p374 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (hardyZApproximantRS₀ qz35) Bool.false 55270813313427474824165 37778931862957161709568 4698652088383815387969 Ns576p235 (@Eq.refl Real (hardyZApproximantRS₀ qz35)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz35) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HMul.hMul Real Real Real qz5 qz610 (Zeta.RiemannSiegel.correction qz37))) Bool.false 55270813313427474824165 37778931862957161709568 4698652088383815387969 Ns576p235 (BSN.hardyZApproximantRS₀_eq qz35 12 (@BSN.floor_sqrt_eq_dec qz35 975630 1000 12 qz38 rfl rfl rfl)) (@Ns576p237 55270813313427474824165 37778931862957161709568 4698652088383815387969 Ns576p235 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz35) qz35 12)) Bool.false 6594159 4194304 66599 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz35) qz35 12) (Ns576p331 (Ns576p330 rfl rfl rfl rfl) rfl rfl)) (Ns576p373 rfl) rfl rfl)) 

theorem RS577to588.d59 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz35) Bool.false 55270813313427474824165 37778931862957161709568 4698652088383815387969 Ns576p235 := Ns576p374 

noncomputable abbrev qz617 := (@HMul.hMul Real Real Real qz743 (Real.sqrt qz751) qz745)

noncomputable abbrev qz404 := qz617

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv qz404)

noncomputable abbrev qz405 := (@HMul.hMul Real Real Real qz590 (@HMul.hMul Real Real Real qz590 qz617 qz617) qz617)

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz355 (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv qz405))

noncomputable abbrev qz406 := (@HMul.hMul Real Real Real qz590 qz603 qz603)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real qz355 qz406 qz381))

noncomputable abbrev qz618 := (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 25 4) qz53)

noncomputable def Ns576p375 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (@HAdd.hAdd Real Real Real qz370 (@HAdd.hAdd Real Real Real qz370 qz618 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55)) Bool.false 

noncomputable def Ns576p376 := @Enclosure.Real.IsNear.addLit_ff (@HAdd.hAdd Real Real Real qz370 qz618 qz54) (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 13 10) qz55) 24533001 2147483648 

noncomputable def Ns576p377 := @Enclosure.Real.IsNear.addLit_ff qz618 qz54 3066625 268435456 25 268435456 

noncomputable def Ns576p378 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) qz53 25 4 0 1 122665 67108864 1 67108864 3066625 

noncomputable def Ns576p379 := @Enclosure.Real.IsNear.recentre' qz53 Bool.false 122665 67108864 1 67108864 122665 67108864 1 67108864 

noncomputable def Ns576p380 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz8 236805337 67108864 7 67108864 10404621404757 67108864000 974151 67108864000 2463869878110894788109 4503599627370496000 303516512496243 

noncomputable def Ns576p381 := @Enclosure.Real.IsNear.sqrt_image qz8 10404621404757 67108864000 974151 67108864000 417804457 417804497 33554432 qz21 

noncomputable def Ns576p382 := @Enclosure.Real.IsNear.sqrt_image qz22 417804477 33554432 5 8388608 118402665 118402672 33554432 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 835608954 67108864 40 67108864 417804477 33554432 5 8388608 (Ns576p381 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable abbrev qz407 := (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 236805337 67108864 7 67108864 236805337 67108864 7 67108864 (Ns576p382 rfl rfl rfl rfl rfl) rfl)

noncomputable def Ns576p383 := @Ns576p380 4503599627370496000 qz407 

noncomputable def Ns576p384 := Ns576p383 qz21 

noncomputable abbrev qz56 := qz404

noncomputable def Ns576p385 := @Enclosure.Real.IsNear.inv_image qz56 2463869878110894788109 4503599627370496000 303516512496243 4503599627370496000 61332 61333 33554432 (Ns576p384 rfl) rfl rfl 

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv qz405)

noncomputable def Ns576p386 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) qz57 1 32 0 1 1 

noncomputable def Ns576p387 := @Enclosure.Real.IsNear.recentre' qz57 Bool.false 1 67108864 1 67108864 

noncomputable def Ns576p388 := nat_lit 14957303443642456996519979626338387992945134913266438231617979029 

noncomputable def Ns576p389 := nat_lit 91343852333181432387730302044767688728495783936000000000 

noncomputable def Ns576p390 := nat_lit 5527632579711197027179804969134228408515739697917511843179 

noncomputable abbrev qz58 := qz405

noncomputable def Ns576p391 := @Enclosure.Real.IsNear.inv_image qz58 Ns576p388 Ns576p389 Ns576p390 Ns576p389 0 1 

noncomputable def Ns576p392 := nat_lit 6070654776262195540110213015433740007795881 

noncomputable def Ns576p393 := nat_lit 20282409603651670423947251286016000000 

noncomputable def Ns576p394 := nat_lit 1495650477419797588300448211376264023 

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real qz590 qz617 qz617)

noncomputable abbrev qz59 := qz408

noncomputable def Ns576p395 := @Enclosure.Real.IsNear.mulLit_ff qz59 qz56 Ns576p392 Ns576p393 Ns576p394 Ns576p393 2463869878110894788109 4503599627370496000 303516512496243 

noncomputable def Ns576p396 := @Enclosure.Real.IsNear.mulLit_ff qz56 qz56 2463869878110894788109 4503599627370496000 303516512496243 4503599627370496000 2463869878110894788109 4503599627370496000 303516512496243 4503599627370496000 Ns576p392 

noncomputable def Ns576p397 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) qz55 13 10 0 1 1527373 67108864 1 

noncomputable def Ns576p398 := @Enclosure.Real.IsNear.recentre' qz55 Bool.false 1527373 67108864 1 67108864 1527373 67108864 

noncomputable def Ns576p399 := nat_lit 13279277856891519434407753 

noncomputable abbrev qz60 := qz406

noncomputable def Ns576p400 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz23 56076767631683569 4503599627370496 3315274767 4503599627370496 236805337 67108864 7 67108864 Ns576p399 

noncomputable def Ns576p401 := @Enclosure.Real.IsNear.mulLit_ff qz23 qz23 236805337 67108864 7 67108864 236805337 67108864 7 67108864 56076767631683569 4503599627370496 3315274767 

noncomputable def Ns576p402 := @Ns576p401 4503599627370496 qz407 

noncomputable def Ns576p403 := Ns576p402 qz407 

noncomputable def Ns576p404 := @Ns576p400 302231454903657293676544 1177612155075739831 302231454903657293676544 (Ns576p403 rfl) qz407 

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz355 qz406 qz381)

noncomputable def Ns576p405 := @Enclosure.Real.IsNear.inv_image qz61 Ns576p399 302231454903657293676544 1177612155075739831 302231454903657293676544 763686 763687 33554432 (Ns576p404 rfl) 

noncomputable def Ns576p406 := @Ns576p376 201 2147483648 19855849 671088640 13 671088640 59103929320865792 440358589 10737418240 1213 10737418240 (@Ns576p377 1 2147483648 1 2147483648 6585527310483456 24533001 2147483648 201 2147483648 (@Ns576p378 268435456 25 268435456 (Enclosure.Real.IsNear.const Bool.false 25 4) (Ns576p379 (Ns576p385 rfl rfl rfl rfl) rfl) rfl) (@Ns576p386 67108864 1 67108864 1 2147483648 1 2147483648 (Enclosure.Real.IsNear.const Bool.false 1 32) (@Ns576p387 1 67108864 1 67108864 (@Ns576p391 33554432 (@Ns576p395 4503599627370496000 Ns576p388 Ns576p389 Ns576p390 Ns576p389 (@Ns576p396 Ns576p393 Ns576p394 Ns576p393 (Ns576p384 rfl) (Ns576p384 rfl) rfl) (Ns576p384 rfl) rfl) rfl rfl rfl rfl rfl rfl) rfl) rfl) rfl rfl) (@Ns576p397 67108864 19855849 671088640 13 671088640 (Enclosure.Real.IsNear.const Bool.false 13 10) (@Ns576p398 1 67108864 (Ns576p405 rfl rfl rfl rfl rfl rfl) rfl) rfl) 

theorem RS577to588.d60 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 := @Ns576p375 440358589 10737418240 1213 10737418240 (BSN.hardyZErrorBoundRS₀_mk qz4 974151 1000 qz11 rfl rfl) (Ns576p406 rfl rfl) 

noncomputable def Ns576p407 := nat_lit 18889465931478580854784000 

noncomputable def Ns576p408 := nat_lit 217421749770466821868856803328 

noncomputable abbrev qz756 := (Enclosure.sfrac Bool.false 976875 1000)

noncomputable abbrev qz619 := qz756

noncomputable abbrev qz409 := qz619

noncomputable abbrev qz62 := qz409

noncomputable abbrev qz757 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 976875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz620 := qz757

noncomputable abbrev qz410 := qz620

noncomputable abbrev qz63 := qz410

noncomputable abbrev qz758 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 976875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz621 := qz758

noncomputable abbrev qz411 := qz621

noncomputable abbrev qz64 := qz411

noncomputable abbrev qz622 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz63 qz9))

noncomputable def Ns576p409 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HMul.hMul Real Real Real qz5 qz622 (Zeta.RiemannSiegel.correction qz64)) 525657 8388608 33343 33554432 16449297645726314885353 151115727451828646838272 48438723478237756507 Ns576p407 Ns576p408 

noncomputable def Ns576p410 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin BSN.quadSignPos 11 12 976875 1000 287 536870912 268435456 9007199254740992 Bool.false 1060889508532 4546 1334074092 54 154981288 8 

noncomputable def Ns576p411 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 976875 1000 173 233 536870912 268435456 9007199254740992 Bool.false 1060889508532 4546 

noncomputable def Ns576p412 := Ns576p411 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 131165237 214779 Bool.true 821061430 Bool.true 208144808 28296951008113761 1 Bool.false 536409773 Bool.true Bool.false 202969440 Bool.true Bool.true 99660021 

noncomputable def Ns576p413 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 7 8 9 976875 1000 35 108 536870912 268435456 9007199254740992 Bool.false 1060889508532 4546 

noncomputable def Ns576p414 := Ns576p413 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 63861442 175403 Bool.true 169589981 Bool.true 379584914 28296951008113761 1 Bool.false 166783626 Bool.false Bool.false 408179290 Bool.false Bool.false 131165237 

noncomputable def Ns576p415 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 976875 1000 143 47 536870912 268435456 9007199254740992 Bool.false 1060889508532 4546 

noncomputable def Ns576p416 := Ns576p415 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 457039366 130335 Bool.false 596895248 Bool.false 709915535 28296951008113761 1 Bool.false 481304457 Bool.false Bool.false 520382768 Bool.false Bool.true 63861442 

noncomputable def Ns576p417 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 976875 1000 395 257 536870912 268435456 9007199254740992 Bool.false 1060889508532 4546 

noncomputable def Ns576p418 := Ns576p417 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 684498757 76967 Bool.false 730074231 Bool.false 78602783 28296951008113761 1 Bool.false 524972365 Bool.false Bool.false 78322267 Bool.true Bool.true 457039366 

noncomputable def Ns576p419 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz62) qz62 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 976875 1000 826 574 536870912 268435456 9007199254740992 Bool.false 1060889508532 4546 

noncomputable def Ns576p420 := Ns576p419 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 536870592 4605 Bool.false 786411866 Bool.false 653229952 28296951008113761 1 Bool.false 56796509 Bool.true Bool.false 186138247 Bool.true Bool.true 684498757 

noncomputable def Ns576p421 := nat_lit 64876030395337277662122100219386471105036625 

noncomputable def Ns576p422 := nat_lit 32830990715939712003366018676002035597312 

noncomputable def Ns576p423 := nat_lit 427008482573496661977539062500000000 

noncomputable def Ns576p424 := nat_lit 2502803774466088758319932861328125000000 

noncomputable abbrev qz623 := (@Eq.refl Real qz756)

noncomputable abbrev qz412 := qz623

noncomputable abbrev qz65 := qz412

noncomputable def Ns576p425 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz62 976875 1000 3817140062500 16000000 1953750 4000 2000 Ns576p423 Ns576p424 qz65 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p426 := nat_lit 712749357370648802440306276824314257745763702392578125000000 

noncomputable abbrev qz624 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1953750))))

noncomputable abbrev qz413 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 976875 4000) (Real.log (Enclosure.sfrac Bool.false 3817140062500 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz624))

noncomputable abbrev qz625 := (Enclosure.sfrac Bool.false 976875 2000)

noncomputable abbrev qz66 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz413 qz625) (@HMul.hMul Real Real Real qz355 qz625 (Real.log Real.pi)))

noncomputable def Ns576p427 := @Enclosure.Real.IsNear.addLit_ft_p qz66 (Enclosure.sfrac Bool.true Ns576p423 Ns576p424) 284780383576456778641 144115188075855872 1109435163331089 131072000000000000000 Ns576p423 Ns576p424 0 1 Ns576p426 

noncomputable def Ns576p428 := nat_lit 152890304250402172477575790592 

noncomputable abbrev qz67 := (@HSub.hSub Real Real Real qz359 qz413 qz625)

noncomputable def Ns576p429 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (@HMul.hMul Real Real Real qz5 qz625 (Real.log Real.pi)) 365359364854489633681 144115188075855872 384717328311 128000000000000000 300180097215 536870912 23445 4294967296 Ns576p428 284780383576456778641 144115188075855872 

noncomputable abbrev qz68 := qz413

noncomputable def Ns576p430 := @Enclosure.Real.IsNear.subLit_ff_p qz68 qz625 435750627030290486161 144115188075855872 384717328311 128000000000000000 976875 2000 0 1 730718729708979267362000 365359364854489633681 144115188075855872 384717328311 128000000000000000 

noncomputable def Ns576p431 := nat_lit 981223180760038107744271382953852928 

noncomputable def Ns576p432 := nat_lit 119755449908113134013382656 

noncomputable def Ns576p433 := nat_lit 129866712493261534977777547418809060051662287152301760471041607033521573290522943289513925725596783183772637116112333779960330559788417303934693336486816406250000000000000000000000000000 

noncomputable def Ns576p434 := nat_lit 3858992470285263723681198398485356320481323255132224281521647585199076712282765614981964646302753332532634517661638481889063712060305988416075706481933593750000000000000000000000000000 

noncomputable def Ns576p435 := nat_lit 267993279930311389941245206354133526369669986466157039020702367821690853657363442205824796262660194500557119465233846256069227820262312889099121093750000000000000000000000000000 

noncomputable def Ns576p436 := BSN.log_dyadic_bound 1719988062500 5914292062500 8 7 Ns576p433 268435456 81920000 Ns576p434 Ns576p435 160771694 7634280125000 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1719988062500) (BSN.artanhQ 5914292062500) 0 7 Ns576p434 Ns576p433 Ns576p435 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz414 := (Real.log (Enclosure.sfrac Bool.false 3817140062500 16000000))

noncomputable def Ns576p437 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 976875 4000) qz414 976875 4000 0 1 55765476966329447 4503599627370496 48828193 4000000000000000 435807202491864628305 144115188075855872 76318465659 25600000000000000 (Enclosure.Real.IsNear.const Bool.false 976875 4000) (BSN.isNear_log_sfrac 3817140062500 16000000 55765476966329447 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3817140062500) qz362)) Bool.false Ns576p432 Ns576p112 1000001392640000 81920000000000000000000 55765476966329447 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3817140062500 16000000 17 7634280125000 4194304000000 160771694 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p436 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p438 := BSN.arctan_dyadic_bound_f 1000 1953750 1 0 33554432 10240000 0 1 1 0 1 1 17174 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1953750) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1953750) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p439 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1953750))) 884279719003555 562949953421312 1 2000000000000000 17174 33554432 1 10240000 29661835597783836393472 883991587095971 562949953421312 195312501 2000000000000000 qz17 (Ns576p438 rfl) rfl rfl 

noncomputable abbrev qz415 := (@HMul.hMul Real Real Real qz590 qz595 qz624)

noncomputable abbrev qz69 := qz415

noncomputable abbrev qz416 := qz624

noncomputable abbrev qz70 := qz416

noncomputable def Ns576p440 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 976875 4000) qz414) qz69 435807202491864628305 144115188075855872 76318465659 25600000000000000 883991587095971 2251799813685248 195312501 8000000000000000 Ns576p431 435750627030290486161 144115188075855872 384717328311 128000000000000000 (Ns576p437 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz70 1 4 0 1 883991587095971 562949953421312 195312501 2000000000000000 883991587095971 2251799813685248 195312501 8000000000000000 qz369 Ns576p439 rfl) 

noncomputable def Ns576p441 := @Ns576p427 Ns576p421 Ns576p422 1109435163331089 131072000000000000000 (@Ns576p429 1109435163331089 131072000000000000000 (Ns576p430 (Ns576p440 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 976875 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz625 (Real.log Real.pi) 976875 2000 0 1 38410761 33554432 3 268435456 300180097215 536870912 23445 4294967296 (Enclosure.Real.IsNear.const Bool.false 976875 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p423 Ns576p424) 

noncomputable def Ns576p442 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns576p421 Ns576p422 1109435163331089 131072000000000000000 66305594283 33554432 569 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz370 qz66 (Enclosure.sfrac Bool.true Ns576p423 Ns576p424)) Bool.false Ns576p421 Ns576p422 1109435163331089 131072000000000000000 Ns576p425 (Ns576p441 rfl rfl)) 

noncomputable def Ns576p443 := nat_lit 7590671854184056913657856 

noncomputable def Ns576p444 := nat_lit 14340715048287434532114682066952323555372448463521434881651337890892760597528941996405565157485005692890454166443157752122979782107816776864241 

noncomputable def Ns576p445 := nat_lit 10166347445443162750575433726717451118842349727691720069930558848139841950300191822491584150584670008851875955309835717679316607947936241 

noncomputable def Ns576p446 := nat_lit 71614719606262731545691752179480080937060121789148603369111268782569390173857887267831658141290759229612174071681105278772256168174351914799601 

noncomputable def Ns576p447 := BSN.sin_dyadic_bound_f 215739869821 137438953472 4 3 67108864 20500001 Ns576p444 Ns576p274 Ns576p445 Ns576p446 Ns576p277 Ns576p445 67108824 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215739869821) qz371 0 3 Ns576p444 Ns576p274 Ns576p445 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215739869821) qz372 0 3 Ns576p446 Ns576p277 Ns576p445 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p448 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz62) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66305594283) qz373) Bool.false 66305594283 33554432 569 67108864 Bool.true 67108824 67108864 1 10240000 (Ns576p442 rfl) (Enclosure.sfrac_false_div 66305594283 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66305594283) qz373) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p443) qz374) 226375608064910080 72057594037927936 Bool.false 67108824 67108864 314 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 66305594283 33554432 226375608064910080 72057594037927936 314 Ns576p443 Ns576p124 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108824 67108864 Ns576p443 Ns576p124 215739869821 137438953472 20500001 20480000 (Ns576p447 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p449 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz62) Bool.false Ns576p421 Ns576p422 1109435163331089 131072000000000000000 1060889508532 536870912 4546 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz62) (@HAdd.hAdd Real Real Real qz370 qz66 (Enclosure.sfrac Bool.true Ns576p423 Ns576p424)) Bool.false Ns576p421 Ns576p422 1109435163331089 131072000000000000000 Ns576p425 (Ns576p441 rfl rfl)) 

noncomputable def Ns576p450 := Ns576p420 76967 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 826 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 56796509 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 574 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 186138247 536870912) qz65 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) Bool.true 8388603 8388608 359721 41943040000 536870592 536870912 4605 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 8388603 8388608 359721 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz62) qz62) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz62)) Bool.true 67108824 67108864 5893668864 687194767360000 8388603 8388608 359721 41943040000 (Ns576p448 rfl rfl) rfl)) rfl) (Ns576p449 rfl) RS577to588.d7 

noncomputable def Ns576p451 := nat_lit 52829185354320298126502259340697334950760675888110594475533319626590047321685410752458766430730289220737100353536 

noncomputable def Ns576p452 := nat_lit 55950077727286816312684639235246063936968959238297433963022326043588206273279319661883860232272379775225856 

noncomputable def Ns576p453 := nat_lit 319912851748899031369684415327296183181526159720816544408243609930689486566152768911427054495358768094815223746560 

noncomputable def Ns576p454 := BSN.cos_dyadic_bound_f 786411866 536870912 4 3 536870912 268435456 Ns576p451 Ns576p162 Ns576p452 Ns576p453 Ns576p165 Ns576p452 56796509 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 786411866) qz377 0 3 Ns576p451 Ns576p162 Ns576p452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 786411866) qz378 0 3 Ns576p453 Ns576p165 Ns576p452 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p455 := nat_lit 25113971046422791825445371754313220824344328784421046255625917023167247066156231539185254300222801152068630347776 

noncomputable def Ns576p456 := nat_lit 6036609436810739390209051171027141397409419988919175090584720813128726156905708717453748463614979836215296 

noncomputable def Ns576p457 := nat_lit 152225722745227123163573564177367939000251459428479297655021566392590482577212721957492271052681010915607566090240 

noncomputable def Ns576p458 := BSN.cos_dyadic_bound_f 653229952 536870912 4 3 536870912 268435456 Ns576p455 Ns576p162 Ns576p456 Ns576p457 Ns576p165 Ns576p456 186138247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 653229952) qz377 0 3 Ns576p455 Ns576p162 Ns576p456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 653229952) qz378 0 3 Ns576p457 Ns576p165 Ns576p456 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p459 := nat_lit 101863146529021492619632256560835478474322825957215170875797225004078758980132615600831736471829152098334887809761 

noncomputable def Ns576p460 := nat_lit 22930009575935540824968898902036939289049334847146667923549006065997016465387477324648821149994941134312161 

noncomputable def Ns576p461 := nat_lit 508959993908539064276733142444454068015137832765490685595340070967149941117631913234843347290815188577415533073121 

noncomputable def Ns576p462 := BSN.sin_dyadic_bound_f 730074231 536870912 4 3 536870912 268435456 Ns576p459 Ns576p135 Ns576p460 Ns576p461 Ns576p138 Ns576p460 524972365 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 730074231) qz375 0 3 Ns576p459 Ns576p135 Ns576p460 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 730074231) qz376 0 3 Ns576p461 Ns576p138 Ns576p460 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p463 := nat_lit 38172595610486469051423196417921 

noncomputable def Ns576p464 := BSN.sin_dyadic_bound_f 78602783 536870912 2 1 536870912 268435456 Ns576p463 Ns576p300 Ns576p463 Ns576p463 Ns576p301 Ns576p463 78322267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 78602783) qz375 0 1 Ns576p463 Ns576p300 Ns576p463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 78602783) qz376 0 1 Ns576p463 Ns576p301 Ns576p463 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p465 := Ns576p418 130335 BSN.abs_quadSignPos (BSN.cos_quad_nat3 395 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 524972365 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 257 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 78322267 536870912) qz65 rfl rfl (Ns576p450 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p454 rfl rfl) (Ns576p458 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p449 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p462 rfl rfl) (Ns576p464 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p466 := nat_lit 31906058261573573064732656384611501785827235042784927217936871408617390080 

noncomputable def Ns576p467 := nat_lit 16113317745318043308684196478223052897217489905224984194675763111264256 

noncomputable def Ns576p468 := nat_lit 83537397694438366908942897070160619734380596795066349882090902453722546176 

noncomputable def Ns576p469 := BSN.sin_dyadic_bound_f 596895248 536870912 3 2 536870912 268435456 Ns576p466 Ns576p151 Ns576p467 Ns576p468 Ns576p154 Ns576p467 481304457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 596895248) qz375 0 2 Ns576p466 Ns576p151 Ns576p467 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 596895248) qz376 0 2 Ns576p468 Ns576p154 Ns576p467 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p470 := nat_lit 91059178185806614081157910993133202320909298928871180216321816712567162146598868236397950688438977674171168290625 

noncomputable def Ns576p471 := nat_lit 16386271969120633218480860823790557696608091437238331723574291916893894497816413502422187134899121337890625 

noncomputable def Ns576p472 := nat_lit 455011551834875994641255863615268102241733067906882486601884094328218947270097725815993298883340708043746489890625 

noncomputable def Ns576p473 := BSN.sin_dyadic_bound_f 709915535 536870912 4 3 536870912 268435456 Ns576p470 Ns576p135 Ns576p471 Ns576p472 Ns576p138 Ns576p471 520382768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 709915535) qz375 0 3 Ns576p470 Ns576p135 Ns576p471 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 709915535) qz376 0 3 Ns576p472 Ns576p138 Ns576p471 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p474 := Ns576p416 175403 BSN.abs_quadSignPos (BSN.cos_quad_nat3 143 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 481304457 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 47 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 520382768 536870912) qz65 rfl rfl (Ns576p465 rfl rfl) (Ns576p449 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p469 rfl rfl) (Ns576p473 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p475 := nat_lit 827181411009101587815051728890321 

noncomputable def Ns576p476 := BSN.sin_dyadic_bound_f 169589981 536870912 2 1 536870912 268435456 Ns576p475 Ns576p300 Ns576p475 Ns576p475 Ns576p301 Ns576p475 166783626 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 169589981) qz375 0 1 Ns576p475 Ns576p300 Ns576p475 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 169589981) qz376 0 1 Ns576p475 Ns576p301 Ns576p475 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p477 := nat_lit 2897938394128020635178926213559049868447465200674121333915430237061857536 

noncomputable def Ns576p478 := nat_lit 430994323294887588513093818740125011459010290763923004812332261785856 

noncomputable def Ns576p479 := nat_lit 8692953193737472130359752453039669355319477581440836155736666046662000896 

noncomputable def Ns576p480 := BSN.cos_dyadic_bound_f 379584914 536870912 3 2 536870912 268435456 Ns576p477 Ns576p141 Ns576p478 Ns576p479 Ns576p144 Ns576p478 408179290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 379584914) qz377 0 2 Ns576p477 Ns576p141 Ns576p478 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 379584914) qz378 0 2 Ns576p479 Ns576p144 Ns576p478 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p481 := Ns576p414 214779 BSN.abs_quadSignPos (BSN.cos_quad_nat3 35 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 166783626 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 408179290 536870912) qz65 rfl rfl (Ns576p474 rfl) (Ns576p449 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p476 rfl rfl) (Ns576p480 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p482 := nat_lit 163059405081089387396693591976538133142376961872822075665058859630209378877106717363976800381931610923550886400000 

noncomputable def Ns576p483 := nat_lit 93865892838094029683950045839975732238944961893200513670932621662461406221054863483566290268801000000000000 

noncomputable def Ns576p484 := nat_lit 814386551810397563567036543652521984647040957535529305446534039081072817322682473426655120969828567862010432000000 

noncomputable def Ns576p485 := BSN.sin_dyadic_bound_f 821061430 536870912 4 3 536870912 268435456 Ns576p482 Ns576p135 Ns576p483 Ns576p484 Ns576p138 Ns576p483 536409773 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 821061430) qz375 0 3 Ns576p482 Ns576p135 Ns576p483 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 821061430) qz376 0 3 Ns576p484 Ns576p138 Ns576p483 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p486 := nat_lit 1876991599631949381633366967914496 

noncomputable def Ns576p487 := BSN.sin_dyadic_bound_f 208144808 536870912 2 1 536870912 268435456 Ns576p486 Ns576p300 Ns576p486 Ns576p486 Ns576p301 Ns576p486 202969440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 208144808) qz375 0 1 Ns576p486 Ns576p300 Ns576p486 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 208144808) qz376 0 1 Ns576p486 Ns576p301 Ns576p486 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p488 := Ns576p412 250193 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536409773 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 202969440 536870912) qz65 rfl rfl (Ns576p481 rfl) (Ns576p449 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p485 rfl rfl) (Ns576p487 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p489 := nat_lit 2110806210697148295606711917602518657238213867340435258051749857784130625 

noncomputable def Ns576p490 := nat_lit 70590313532214923259693957811697999210249004307082178461299437890625 

noncomputable def Ns576p491 := nat_lit 5528187691318240997665634565408234686482314963694166590418026571297090625 

noncomputable def Ns576p492 := BSN.sin_dyadic_bound_f 302756265 536870912 3 2 536870912 268435456 Ns576p489 Ns576p151 Ns576p490 Ns576p491 Ns576p154 Ns576p490 286962697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 302756265) qz375 0 2 Ns576p489 Ns576p151 Ns576p490 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 302756265) qz376 0 2 Ns576p491 Ns576p154 Ns576p490 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p493 := Ns576p410 Bool.true 99660021 250193 Bool.true 302756265 28296951008113761 1 Bool.false 286962697 Bool.false Bool.true 16821024 266744 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 286962697 536870912) qz65 rfl (Ns576p488 rfl) (Ns576p449 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p492 rfl rfl) rfl 

noncomputable def Ns576p494 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) 16821024 536870912 266744 536870912 16821024 536870912 266744 536870912 18061436991307776 525657 8388608 33343 33554432 (Ns576p493 rfl rfl rfl rfl) 

noncomputable def Ns576p495 := @Enclosure.Real.IsNear.mulLit_ff qz622 (Zeta.RiemannSiegel.correction qz64) 19004879 67108864 1 67108864 865530248612807 2251799813685248 12715295281307 1407374883553280000 16449297645726314885353 151115727451828646838272 

noncomputable abbrev qz626 := (@HPow.hPow Real Real Real qz7 qz63 qz9)

noncomputable def Ns576p496 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz626 1 1 0 1 19004879 67108864 1 67108864 19004879 67108864 1 67108864 

noncomputable def Ns576p497 := @Enclosure.Real.IsNear.sqrt_image qz63 83469725205 536870912 7815 536870912 418388198 418388238 33554432 (@Enclosure.Real.IsNear.of_eq qz63 (@HMul.hMul Real Real Real qz5 qz62 qz3) Bool.false 83469725205 536870912 7815 536870912 (BSN.t_div_two_pi_mk qz62 976875 1000 qz65) (@Enclosure.Real.IsNear.mulLit_ff qz62 qz3 976875 1000 0 1 10680707 67108864 1 67108864 83469725205 536870912 7815 536870912 (Enclosure.Real.IsNear.const Bool.false 976875 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz759 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 976875 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz627 := qz759

noncomputable abbrev qz417 := qz627

noncomputable abbrev qz71 := qz417

noncomputable def Ns576p498 := @Enclosure.Real.IsNear.sqrt_image qz71 209194109 16777216 5 8388608 118485350 118485357 33554432 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 836776436 67108864 40 67108864 209194109 16777216 5 8388608 (Ns576p497 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p499 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz71) 236970707 67108864 7 67108864 9502439 9502440 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz71) Bool.false 236970707 67108864 7 67108864 236970707 67108864 7 67108864 (Ns576p498 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p500 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 19004879 67108864 1 67108864 19004879 67108864 1 67108864 (Ns576p499 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz418 := (@HMul.hMul Real Real Real qz590 qz588 qz621)

noncomputable abbrev qz72 := (Real.cos qz418)

noncomputable abbrev qz628 := (@HMul.hMul Real Real Real qz743 qz758 qz758)

noncomputable abbrev qz419 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz628 qz621) qz605)

noncomputable abbrev qz73 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz419))

noncomputable def Ns576p501 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz64) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz72) qz73) Bool.false 865530248612807 

noncomputable def Ns576p502 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz72) qz73 68407363 67108864 271 

noncomputable abbrev qz74 := (@Neg.neg Real Real.instNeg (Real.cos qz418))

noncomputable def Ns576p503 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz72) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz74)) Bool.true 68407363 67108864 271 67108864 (BSN.inv_eq_neg_inv_neg qz72) 

noncomputable def Ns576p504 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz74) Bool.false 68407363 67108864 271 67108864 68407363 67108864 

noncomputable def Ns576p505 := @Enclosure.Real.IsNear.recentre' qz72 Bool.true 65835013 67108864 2657828864 687194767360000 65835013 67108864 162221 41943040000 

noncomputable abbrev qz75 := qz418

noncomputable abbrev qz629 := (@Nat.cast Real Real.instNatCast 16777216)

noncomputable def Ns576p506 := @Enclosure.Real.IsNear.cos_image qz75 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49433067) qz629) Bool.false 49433067 16777216 253 67108864 Bool.true 65835013 67108864 1 

noncomputable def Ns576p507 := nat_lit 134930377079010955491568867 

noncomputable def Ns576p508 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz64 884279719003555 140737488355328 1 500000000000000 7867517 16777216 5 8388608 6957085722015692022935 2361183241434822606848 Ns576p507 

noncomputable def Ns576p509 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz1 209194109 16777216 5 8388608 12 1 0 1 7867517 7867517 16777216 5 

noncomputable def Ns576p510 := @Ns576p509 8388608 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 836776436 67108864 40 67108864 209194109 16777216 5 8388608 (Ns576p497 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p511 := @Enclosure.Real.IsNear.recentre' qz75 Bool.false 6957085722015692022935 2361183241434822606848 Ns576p507 Ns576p202 49433067 16777216 253 67108864 (@Ns576p508 Ns576p202 RS577to588.d55 (Ns576p510 rfl rfl) rfl) 

noncomputable def Ns576p512 := nat_lit 3326103274235045970182144 

noncomputable def Ns576p513 := nat_lit 2417851639229258349412352 

noncomputable def Ns576p514 := nat_lit 1380380562484915120054913974538179762713723647832680368325841886155449320132818422668477725505 

noncomputable def Ns576p515 := nat_lit 1632778843481740938816753705471909493179772443995659113309554627724867447577205114491763521 

noncomputable def Ns576p516 := nat_lit 3612638878856759638623833284457802001261270874652455611812798994343193672099399441565407378241 

noncomputable def Ns576p517 := BSN.sin_dyadic_bound_f 189067081591 137438953472 3 2 67108864 20500001 Ns576p514 Ns576p126 Ns576p515 Ns576p516 Ns576p129 Ns576p515 65835013 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 189067081591) qz371 0 2 Ns576p514 Ns576p126 Ns576p515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 189067081591) qz372 0 2 Ns576p516 Ns576p129 Ns576p515 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p518 := @Ns576p506 10240000 (Ns576p511 rfl) (Enclosure.sfrac_false_div 49433067 16777216) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 49433067) qz629) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p512) (@Nat.cast Real Real.instNatCast Ns576p513)) 226375608064910080 72057594037927936 Bool.false 65835013 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 49433067 16777216 226375608064910080 72057594037927936 0 Ns576p512 Ns576p513 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 65835013 67108864 Ns576p512 Ns576p513 189067081591 137438953472 20500001 20480000 (Ns576p517 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p519 := @Enclosure.Real.IsNear.inv_image qz74 65835013 67108864 162221 41943040000 34203546 34203817 33554432 (@Enclosure.Real.IsNear.neg qz72 Bool.true 65835013 67108864 162221 41943040000 (Ns576p505 (Ns576p518 rfl rfl) rfl)) 

noncomputable def Ns576p520 := Ns576p503 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz74) Bool.false 68407363 67108864 271 67108864 (@Ns576p504 271 67108864 (Ns576p519 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p521 := @Enclosure.Real.IsNear.recentre' qz73 Bool.true 12652589 33554432 

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz355 qz352 qz419)

noncomputable def Ns576p522 := @Enclosure.Real.IsNear.cos_image qz76 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65680589)) qz373) Bool.true 65680589 33554432 

noncomputable def Ns576p523 := nat_lit 77541953032371931421543845445 

noncomputable def Ns576p524 := nat_lit 39614081257132168796771975168 

noncomputable def Ns576p525 := nat_lit 1096722875192213716892545377695651 

noncomputable def Ns576p526 := @Enclosure.Real.IsNear.recentre' qz76 Bool.true Ns576p523 Ns576p524 Ns576p525 

noncomputable def Ns576p527 := nat_lit 151115727451828646838272000000000000000 

noncomputable abbrev qz77 := qz419

noncomputable def Ns576p528 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz77 884279719003555 140737488355328 1 500000000000000 87689394391799 

noncomputable abbrev qz420 := (@HSub.hSub Real Real Real qz594 qz628 qz621)

noncomputable abbrev qz78 := qz420

noncomputable def Ns576p529 := @Enclosure.Real.IsNear.subLit_tf qz78 qz31 70097208347383 281474976710656 40640325 35184372088832 1 16 

noncomputable abbrev qz421 := qz628

noncomputable abbrev qz79 := qz421

noncomputable def Ns576p530 := @Enclosure.Real.IsNear.subLit_ff_n qz79 qz64 61897823745289 281474976710656 19668805 35184372088832 7867517 16777216 5 8388608 

noncomputable def Ns576p531 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz64 7867517 16777216 5 8388608 7867517 16777216 5 8388608 61897823745289 281474976710656 

noncomputable def Ns576p532 := nat_lit 602082877811608324079558399511042985604181226528971807467963020163328199199457247770189310444609201 

noncomputable def Ns576p533 := nat_lit 6445319709891802077950690026694273790047992641548823106935481981516354213708535904439689977521 

noncomputable def Ns576p534 := nat_lit 3631508874133768704192358270317001144125327540364291264334811375377562688644823862070585944765275825 

noncomputable def Ns576p535 := BSN.cos_dyadic_bound_t 65680589 33554432 4 3 33554432 10240000 Ns576p532 Ns576p367 Ns576p533 Ns576p534 Ns576p370 Ns576p533 12652589 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65680589) (BSN.cosEvenQ 33554432) 0 3 Ns576p532 Ns576p367 Ns576p533 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65680589) (BSN.cosOddQ 33554432) 0 3 Ns576p534 Ns576p370 Ns576p533 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p536 := @Ns576p521 633028608 85899345920000 12652589 33554432 38637 5242880000 (@Ns576p522 61 8388608 Bool.true 12652589 33554432 1 10240000 (@Ns576p526 Ns576p527 65680589 33554432 61 8388608 (@Ns576p528 281474976710656 40640325 35184372088832 Ns576p523 Ns576p524 Ns576p525 Ns576p527 RS577to588.d55 (@Ns576p529 0 1 1403030310268784 87689394391799 281474976710656 40640325 35184372088832 (@Ns576p530 1176036005441047625728 70097208347383 281474976710656 40640325 35184372088832 (@Ns576p531 19668805 35184372088832 (Ns576p510 rfl rfl) (Ns576p510 rfl rfl) rfl) (Ns576p510 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65680589 33554432) (BSN.cos_neg_of_bound 65680589 33554432 Bool.true 12652589 33554432 1 10240000 (Ns576p535 rfl rfl)) rfl rfl) 

noncomputable def Ns576p537 := @Ns576p495 48438723478237756507 Ns576p407 (Ns576p496 qz33 (@Enclosure.Real.IsNear.of_eq qz626 (@Inv.inv Real Real.instInv (Real.sqrt qz71)) Bool.false 19004879 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz63 (BSN.t_div_two_pi_nonneg qz62 976875 1000 qz65)) Ns576p500) rfl) (@Ns576p501 2251799813685248 12715295281307 1407374883553280000 (BSN.correction_mk qz64 (BSN.cos_two_pi_p_ne_zero_mk qz62 976875 1000 12 qz65 rfl rfl (@BSN.floor_sqrt_eq_dec qz62 976875 1000 12 qz65 rfl rfl rfl))) (@Ns576p502 67108864 12652589 33554432 38637 5242880000 865530248612807 2251799813685248 12715295281307 1407374883553280000 Ns576p520 (Ns576p536 rfl) rfl)) 

noncomputable def Ns576p538 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (hardyZApproximantRS₀ qz62) Bool.true 25918692323025086148841 151115727451828646838272 18818879020405043772507 Ns576p407 (@Eq.refl Real (hardyZApproximantRS₀ qz62)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz62) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HMul.hMul Real Real Real qz5 qz622 (Zeta.RiemannSiegel.correction qz64))) Bool.true 25918692323025086148841 151115727451828646838272 18818879020405043772507 Ns576p407 (BSN.hardyZApproximantRS₀_eq qz62 12 (@BSN.floor_sqrt_eq_dec qz62 976875 1000 12 qz65 rfl rfl rfl)) (@Ns576p409 25918692323025086148841 151115727451828646838272 18818879020405043772507 Ns576p407 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz62) qz62 12)) Bool.true 525657 8388608 33343 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz62) qz62 12) (Ns576p494 (Ns576p493 rfl rfl rfl rfl) rfl rfl)) (Ns576p537 rfl) rfl rfl)) 

theorem RS577to588.d61 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz62) Bool.true 25918692323025086148841 151115727451828646838272 18818879020405043772507 Ns576p407 := Ns576p538 

noncomputable def Ns576p539 := nat_lit 1888946593147858085478400 

noncomputable def Ns576p540 := nat_lit 6493734320402392418871031103488 

noncomputable abbrev qz760 := (Enclosure.sfrac Bool.false 978120 1000)

noncomputable abbrev qz630 := qz760

noncomputable abbrev qz422 := qz630

noncomputable abbrev qz80 := qz422

noncomputable abbrev qz761 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 978120 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz631 := qz761

noncomputable abbrev qz423 := qz631

noncomputable abbrev qz81 := qz423

noncomputable abbrev qz762 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 978120 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz632 := qz762

noncomputable abbrev qz424 := qz632

noncomputable abbrev qz82 := qz424

noncomputable abbrev qz633 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz81 qz9))

noncomputable def Ns576p541 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HMul.hMul Real Real Real qz5 qz633 (Zeta.RiemannSiegel.correction qz82)) 351063737 67108864 267075 268435456 2051475337694050542505 18889465931478580854784 4961108611711132261 Ns576p539 Ns576p540 

noncomputable def Ns576p542 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin BSN.quadSignPos 11 12 978120 1000 287 536870912 268435456 9007199254740992 Bool.false 1062576266265 4551 1334074092 54 154981288 8 

noncomputable def Ns576p543 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 978120 1000 173 233 536870912 268435456 9007199254740992 Bool.false 1062576266265 4551 

noncomputable def Ns576p544 := Ns576p543 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 1526250376 215044 Bool.true 673361437 Bool.true 124150549 28296951008113761 1 Bool.false 510194334 Bool.true Bool.false 123046994 Bool.true Bool.false 1327812691 

noncomputable def Ns576p545 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 7 8 9 978120 1000 34 108 536870912 268435456 9007199254740992 Bool.false 1062576266265 4551 

noncomputable def Ns576p546 := Ns576p545 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 1399898807 175618 Bool.true 716054742 Bool.true 161461487 28296951008113761 1 Bool.false 126071706 Bool.true Bool.false 512773958 Bool.false Bool.false 1526250376 

noncomputable def Ns576p547 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 978120 1000 144 48 536870912 268435456 9007199254740992 Bool.false 1062576266265 4551 

noncomputable def Ns576p548 := Ns576p547 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 1021891079 130494 Bool.false 242718426 Bool.false 252703748 28296951008113761 1 Bool.false 482932797 Bool.false Bool.false 478487394 Bool.false Bool.false 1399898807 

noncomputable def Ns576p549 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignPos BSN.quadSignNeg 3 4 5 978120 1000 396 257 536870912 268435456 9007199254740992 Bool.false 1062576266265 4551 

noncomputable def Ns576p550 := Ns576p549 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 1156187978 77059 Bool.false 646912033 Bool.false 689605338 28296951008113761 1 Bool.false 192051257 Bool.false Bool.false 515016809 Bool.true Bool.false 1021891079 

noncomputable def Ns576p551 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz80) qz80 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 978120 1000 828 575 536870912 268435456 9007199254740992 Bool.false 1062576266265 4551 

noncomputable def Ns576p552 := Ns576p551 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 536870720 4605 Bool.false 323237358 Bool.false 762355673 28296951008113761 1 Bool.false 442468259 Bool.false Bool.false 530778220 Bool.false Bool.false 1156187978 

noncomputable def Ns576p553 := nat_lit 2439232561279945150749380689808910495925212531267 

noncomputable def Ns576p554 := nat_lit 1232432015780874304538539554775074048856555520 

noncomputable def Ns576p555 := nat_lit 429736478638110421060647936000000000 

noncomputable def Ns576p556 := nat_lit 2522003374458078892723018723921920000000 

noncomputable abbrev qz634 := (@Eq.refl Real qz760)

noncomputable abbrev qz425 := qz634

noncomputable abbrev qz83 := qz425

noncomputable def Ns576p557 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz80 978120 1000 3826875937600 16000000 1956240 4000 2000 Ns576p555 Ns576p556 qz83 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p558 := nat_lit 449599345695119490186125848745578382608935173763133440000000 

noncomputable abbrev qz635 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1956240))))

noncomputable abbrev qz426 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 978120 4000) (Real.log (Enclosure.sfrac Bool.false 3826875937600 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz635))

noncomputable abbrev qz636 := (Enclosure.sfrac Bool.false 978120 2000)

noncomputable abbrev qz84 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz426 qz636) (@HMul.hMul Real Real Real qz355 qz636 (Real.log Real.pi)))

noncomputable def Ns576p559 := @Enclosure.Real.IsNear.addLit_ft_p qz84 (Enclosure.sfrac Bool.true Ns576p555 Ns576p556) 178270730703898865007 90071992547409920 3471390716434371 409600000000000000000 Ns576p555 Ns576p556 0 1 Ns576p558 

noncomputable def Ns576p560 := nat_lit 1495443277748571650188640256000 

noncomputable abbrev qz85 := (@HSub.hSub Real Real Real qz359 qz426 qz636)

noncomputable def Ns576p561 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (@HMul.hMul Real Real Real qz5 qz636 (Real.log Real.pi)) 1143483893979089642283 450359962737049600 1203761428479 400000000000000000 939258338733 1677721600 73359 13421772800 Ns576p560 178270730703898865007 90071992547409920 

noncomputable def Ns576p562 := nat_lit 2286967787958179284566000 

noncomputable abbrev qz86 := qz426

noncomputable def Ns576p563 := @Enclosure.Real.IsNear.subLit_ff_p qz86 qz636 1363736937355271119659 450359962737049600 1203761428479 400000000000000000 978120 2000 0 1 Ns576p562 1143483893979089642283 450359962737049600 1203761428479 400000000000000000 

noncomputable def Ns576p564 := nat_lit 3070862581452290230661261647971090432 

noncomputable def Ns576p565 := nat_lit 119780086075255528404025344 

noncomputable def Ns576p566 := nat_lit 132891889597821814445696224316407131530787947130469271955516973197446830595274057364966124126349842609442426412132835698922391463814488275432849318938148864000000000000000000000000000000 

noncomputable def Ns576p567 := nat_lit 3982347051383675709793672147729218005970909762539800860197735616572826890653554161818730289405367226714774844965721809085104591248410120753722839362070118400000000000000000000000000000 

noncomputable def Ns576p568 := nat_lit 290030041697955711566502849098981693794509367990752196671099668167329800412960517461271481207826977246803658712656410997828308006497657933883087257600000000000000000000000000000 

noncomputable def Ns576p569 := BSN.log_dyadic_bound 1729723937600 5924027937600 8 7 Ns576p566 268435456 81920000 Ns576p567 Ns576p568 161455485 7653751875200 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1729723937600) (BSN.artanhQ 5924027937600) 0 7 Ns576p567 Ns576p566 Ns576p568 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz427 := (Real.log (Enclosure.sfrac Bool.false 3826875937600 16000000))

noncomputable def Ns576p570 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 978120 4000) qz427 978120 4000 0 1 55776949075635303 4503599627370496 48828193 4000000000000000 1363913735746510064259 450359962737049600 1193995803429 400000000000000000 (Enclosure.Real.IsNear.const Bool.false 978120 4000) (BSN.isNear_log_sfrac 3826875937600 16000000 55776949075635303 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3826875937600) qz362)) Bool.false Ns576p565 Ns576p112 1000001392640000 81920000000000000000000 55776949075635303 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3826875937600 16000000 17 7653751875200 4194304000000 161455485 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p569 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p571 := BSN.arctan_dyadic_bound_f 1000 1956240 1 0 33554432 10240000 0 1 1 0 1 1 17152 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1956240) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1956240) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p572 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1956240))) 884279719003555 562949953421312 1 2000000000000000 17152 33554432 1 10240000 29661847982682811662336 883991956194723 562949953421312 195312501 2000000000000000 qz17 (Ns576p571 rfl) rfl rfl 

noncomputable abbrev qz428 := (@HMul.hMul Real Real Real qz590 qz595 qz635)

noncomputable abbrev qz87 := qz428

noncomputable abbrev qz429 := qz635

noncomputable abbrev qz88 := qz429

noncomputable def Ns576p573 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 978120 4000) qz427) qz87 1363913735746510064259 450359962737049600 1193995803429 400000000000000000 883991956194723 2251799813685248 195312501 8000000000000000 Ns576p564 1363736937355271119659 450359962737049600 1203761428479 400000000000000000 (Ns576p570 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz88 1 4 0 1 883991956194723 562949953421312 195312501 2000000000000000 883991956194723 2251799813685248 195312501 8000000000000000 qz369 Ns576p572 rfl) 

noncomputable def Ns576p574 := @Ns576p559 Ns576p553 Ns576p554 3471390716434371 409600000000000000000 (@Ns576p561 3471390716434371 409600000000000000000 (Ns576p563 (Ns576p573 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 978120 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz636 (Real.log Real.pi) 978120 2000 0 1 38410761 33554432 3 268435456 939258338733 1677721600 73359 13421772800 (Enclosure.Real.IsNear.const Bool.false 978120 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p555 Ns576p556) 

noncomputable def Ns576p575 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns576p553 Ns576p554 3471390716434371 409600000000000000000 132822033283 67108864 569 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz370 qz84 (Enclosure.sfrac Bool.true Ns576p555 Ns576p556)) Bool.false Ns576p553 Ns576p554 3471390716434371 409600000000000000000 Ns576p557 (Ns576p574 rfl rfl)) 

noncomputable def Ns576p576 := nat_lit 15183649964533012230045696 

noncomputable def Ns576p577 := nat_lit 14349448733771377520351520499612704978534713825946186137022502443655760153083735022896611945140291804607556476254917404678075090528915041550336 

noncomputable def Ns576p578 := nat_lit 10184895843961445832142210105992180277939134317843495102940660912517335161569202294093160617647180055641078404899858265449545325069991936 

noncomputable def Ns576p579 := nat_lit 71658279964299697934710515028499995295891506087596784085278388307698230199972537290843433688122456462133775568872164422843354363044343731716096 

noncomputable def Ns576p580 := BSN.sin_dyadic_bound_f 215772643692 137438953472 4 3 67108864 20500001 Ns576p577 Ns576p274 Ns576p578 Ns576p579 Ns576p277 Ns576p578 67108840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215772643692) qz371 0 3 Ns576p577 Ns576p274 Ns576p578 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215772643692) qz372 0 3 Ns576p579 Ns576p277 Ns576p578 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p581 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz80) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 132822033283) qz384) Bool.false 132822033283 67108864 569 67108864 Bool.false 67108840 67108864 1 10240000 (Ns576p575 rfl) (Enclosure.sfrac_false_div 132822033283 67108864) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 132822033283) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p576) qz386) 226375608064910080 72057594037927936 Bool.false 67108840 67108864 314 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q3 132822033283 67108864 226375608064910080 72057594037927936 314 Ns576p576 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108840 67108864 Ns576p576 Ns576p112 215772643692 137438953472 20500001 20480000 (Ns576p580 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p582 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz80) Bool.false Ns576p553 Ns576p554 3471390716434371 409600000000000000000 1062576266265 536870912 4551 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz80) (@HAdd.hAdd Real Real Real qz370 qz84 (Enclosure.sfrac Bool.true Ns576p555 Ns576p556)) Bool.false Ns576p553 Ns576p554 3471390716434371 409600000000000000000 Ns576p557 (Ns576p574 rfl rfl)) 

noncomputable def Ns576p583 := Ns576p552 77059 BSN.abs_quadSignPos (BSN.cos_quad_nat0 828 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 442468259 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 575 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 530778220 536870912) qz83 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) Bool.false 8388605 8388608 359721 41943040000 536870720 536870912 4605 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 8388605 8388608 359721 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz80) qz80) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz80)) Bool.false 67108840 67108864 5893668864 687194767360000 8388605 8388608 359721 41943040000 (Ns576p581 rfl rfl) rfl)) rfl) (Ns576p582 rfl) RS577to588.d7 

noncomputable def Ns576p584 := nat_lit 1523733233425295671089221787788647413811697579108681472717539901326704896 

noncomputable def Ns576p585 := nat_lit 119171494843555473305837464982335002132949745812732562904523275714816 

noncomputable def Ns576p586 := nat_lit 4570961357286199902321053688435977571430826837834418953026810657428685056 

noncomputable def Ns576p587 := BSN.cos_dyadic_bound_f 323237358 536870912 3 2 536870912 268435456 Ns576p584 Ns576p141 Ns576p585 Ns576p586 Ns576p144 Ns576p585 442468259 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 323237358) qz377 0 2 Ns576p584 Ns576p141 Ns576p585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 323237358) qz378 0 2 Ns576p586 Ns576p144 Ns576p585 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p588 := nat_lit 121135734309469761677851580906284868737582638231745619327229134576209588139249129333094849344785693322335906050721 

noncomputable def Ns576p589 := nat_lit 38538218693837669224414582462392145313744287622006474630334589140912441069834059822710886672033622367285921 

noncomputable def Ns576p590 := nat_lit 605175776627116050753613508652051143568236864717307413420413658995978831091704563414816338961538995539035774661281 

noncomputable def Ns576p591 := BSN.sin_dyadic_bound_f 762355673 536870912 4 3 536870912 268435456 Ns576p588 Ns576p135 Ns576p589 Ns576p590 Ns576p138 Ns576p589 530778220 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 762355673) qz375 0 3 Ns576p588 Ns576p135 Ns576p589 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 762355673) qz376 0 3 Ns576p590 Ns576p138 Ns576p589 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p592 := nat_lit 24155184762026944660087994369027283671457006057378809481771026839194368795955705672941408591894442390387861498241 

noncomputable def Ns576p593 := nat_lit 5372083477777975727060048336878045945642917536364346741513753644153811307581211872641751747982600318232961 

noncomputable def Ns576p594 := nat_lit 146418988885972968272393887649707512905096846025518382240236270305776178830520866383776160687471777388438927452545 

noncomputable def Ns576p595 := BSN.cos_dyadic_bound_f 646912033 536870912 4 3 536870912 268435456 Ns576p592 Ns576p162 Ns576p593 Ns576p594 Ns576p165 Ns576p593 192051257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 646912033) qz377 0 3 Ns576p592 Ns576p162 Ns576p593 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 646912033) qz378 0 3 Ns576p594 Ns576p165 Ns576p593 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p596 := nat_lit 81068355361593406233970015500623066413313218771525012625824753209607561699175633875812460474324465773388551622656 

noncomputable def Ns576p597 := nat_lit 11566644150751165630378460300432395226268327536723597419979870973863728446192071121522686639316498699718656 

noncomputable def Ns576p598 := nat_lit 405116364784064620009535626691494753717999880121832468719121339877082150800595991936175865628694781974655336124416 

noncomputable def Ns576p599 := BSN.sin_dyadic_bound_f 689605338 536870912 4 3 536870912 268435456 Ns576p596 Ns576p135 Ns576p597 Ns576p598 Ns576p138 Ns576p597 515016809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 689605338) qz375 0 3 Ns576p596 Ns576p135 Ns576p597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 689605338) qz376 0 3 Ns576p598 Ns576p138 Ns576p597 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p600 := Ns576p550 130494 BSN.abs_quadSignPos (BSN.cos_quad_nat0 396 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 192051257 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 257 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 515016809 536870912) qz83 rfl rfl (Ns576p583 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p587 rfl rfl) (Ns576p591 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p582 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p595 rfl rfl) (Ns576p599 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p601 := nat_lit 484407174271801023083968691322562298596414626039337299608891219883008256 

noncomputable def Ns576p602 := nat_lit 12045420811060309613670766322362342752487853434961659822330742251776 

noncomputable def Ns576p603 := nat_lit 1453197431973780948632678732435042171103738902411141975507028998164521216 

noncomputable def Ns576p604 := BSN.cos_dyadic_bound_f 242718426 536870912 3 2 536870912 268435456 Ns576p601 Ns576p141 Ns576p602 Ns576p603 Ns576p144 Ns576p602 482932797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 242718426) qz377 0 2 Ns576p601 Ns576p141 Ns576p602 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 242718426) qz378 0 2 Ns576p603 Ns576p144 Ns576p602 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p605 := nat_lit 569178125427428469631203257273694617431533735365061085300026509780647936 

noncomputable def Ns576p606 := nat_lit 16630046592447221252833156708034794380718615637789936662421931360256 

noncomputable def Ns576p607 := nat_lit 1707501116189100514451104105507667782705839768863907676026754685479223296 

noncomputable def Ns576p608 := BSN.cos_dyadic_bound_f 252703748 536870912 3 2 536870912 268435456 Ns576p605 Ns576p141 Ns576p606 Ns576p607 Ns576p144 Ns576p606 478487394 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 252703748) qz377 0 2 Ns576p605 Ns576p141 Ns576p606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 252703748) qz378 0 2 Ns576p607 Ns576p144 Ns576p606 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p609 := Ns576p548 175618 BSN.abs_quadSignPos (BSN.cos_quad_nat0 144 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 482932797 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 478487394 536870912) qz83 rfl rfl (Ns576p600 rfl rfl) (Ns576p582 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p604 rfl rfl) (Ns576p608 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p610 := nat_lit 36281657240627920903208987428055629655411622171925935111366143910776307008071884557208619120422782116934277206016 

noncomputable def Ns576p611 := nat_lit 18169990568548050085200804082117116149667723748401313934920581548473542706824102321308101431047811292532736 

noncomputable def Ns576p612 := nat_lit 219832745739459137536339858482579999336143056399361153555218372230608366141895661653232739074921702637789237022720 

noncomputable def Ns576p613 := BSN.cos_dyadic_bound_f 716054742 536870912 4 3 536870912 268435456 Ns576p610 Ns576p162 Ns576p611 Ns576p612 Ns576p165 Ns576p611 126071706 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 716054742) qz377 0 3 Ns576p610 Ns576p162 Ns576p611 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 716054742) qz378 0 3 Ns576p612 Ns576p165 Ns576p611 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p614 := nat_lit 94856410207962455813373488208527388856943863394617937689953072274896001 

noncomputable def Ns576p615 := nat_lit 461903850756029414084839178372214852379084015324742022909321966721 

noncomputable def Ns576p616 := nat_lit 284568306816185855381292294947225422141126832015823163585813398180754561 

noncomputable def Ns576p617 := BSN.cos_dyadic_bound_f 161461487 536870912 3 2 536870912 268435456 Ns576p614 Ns576p141 Ns576p615 Ns576p616 Ns576p144 Ns576p615 512773958 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 161461487) qz377 0 2 Ns576p614 Ns576p141 Ns576p615 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 161461487) qz378 0 2 Ns576p616 Ns576p144 Ns576p615 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p618 := Ns576p546 215044 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 126071706 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 108 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 512773958 536870912) qz83 rfl rfl (Ns576p609 rfl) (Ns576p582 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p613 rfl rfl) (Ns576p617 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p619 := nat_lit 73689622722368329112061510388971151745298695406650987949400578366705405090315796950741378115179785552813591245681 

noncomputable def Ns576p620 := nat_lit 8689181958590654636196889558910140535692391556582629564677481137948047264265314560801303105550759725773681 

noncomputable def Ns576p621 := nat_lit 368261840580167395384439402789645280885317553521187131730955391341239723980971200465713050403945751161230570435441 

noncomputable def Ns576p622 := BSN.sin_dyadic_bound_f 673361437 536870912 4 3 536870912 268435456 Ns576p619 Ns576p135 Ns576p620 Ns576p621 Ns576p138 Ns576p620 510194334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 673361437) qz375 0 3 Ns576p619 Ns576p135 Ns576p620 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 673361437) qz376 0 3 Ns576p621 Ns576p138 Ns576p620 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p623 := nat_lit 237571630021634827720405235962801 

noncomputable def Ns576p624 := BSN.sin_dyadic_bound_f 124150549 536870912 2 1 536870912 268435456 Ns576p623 Ns576p300 Ns576p623 Ns576p623 Ns576p301 Ns576p623 123046994 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 124150549) qz375 0 1 Ns576p623 Ns576p300 Ns576p623 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 124150549) qz376 0 1 Ns576p623 Ns576p301 Ns576p623 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p625 := Ns576p544 250503 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 510194334 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 123046994 536870912) qz83 rfl rfl (Ns576p618 rfl) (Ns576p582 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p622 rfl rfl) (Ns576p624 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p626 := nat_lit 1477384763134291913269637087305772339384114257715043711315606995502429505 

noncomputable def Ns576p627 := nat_lit 34581540200361572640691660166150112956515074858240129702879621084481 

noncomputable def Ns576p628 := nat_lit 3869285057143773473160012204065325217251702983894391617045166040262702401 

noncomputable def Ns576p629 := BSN.sin_dyadic_bound_f 276920777 536870912 3 2 536870912 268435456 Ns576p626 Ns576p151 Ns576p627 Ns576p628 Ns576p154 Ns576p627 264803738 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 276920777) qz375 0 2 Ns576p626 Ns576p151 Ns576p627 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 276920777) qz376 0 2 Ns576p628 Ns576p154 Ns576p627 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p630 := Ns576p542 Bool.false 1327812691 250503 Bool.true 276920777 28296951008113761 1 Bool.false 264803738 Bool.false Bool.false 1404254948 267075 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 264803738 536870912) qz83 rfl (Ns576p625 rfl) (Ns576p582 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p629 rfl rfl) rfl 

noncomputable def Ns576p631 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) 1404254948 536870912 267075 536870912 1404254948 536870912 267075 536870912 1507807269226545152 351063737 67108864 267075 268435456 (Ns576p630 rfl rfl rfl rfl) 

noncomputable def Ns576p632 := @Enclosure.Real.IsNear.mulLit_ff qz633 (Zeta.RiemannSiegel.correction qz82) 4749707 16777216 1 33554432 431916187186715 1125899906842624 2599903679517 281474976710656000 2051475337694050542505 18889465931478580854784 

noncomputable abbrev qz637 := (@HPow.hPow Real Real Real qz7 qz81 qz9)

noncomputable def Ns576p633 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz637 1 1 0 1 4749707 16777216 1 33554432 4749707 16777216 1 33554432 

noncomputable def Ns576p634 := @Enclosure.Real.IsNear.sqrt_image qz81 261175328271 1677721600 24453 1677721600 418654725 418654766 33554432 (@Enclosure.Real.IsNear.of_eq qz81 (@HMul.hMul Real Real Real qz5 qz80 qz3) Bool.false 261175328271 1677721600 24453 1677721600 (BSN.t_div_two_pi_mk qz80 978120 1000 qz83) (@Enclosure.Real.IsNear.mulLit_ff qz80 qz3 978120 1000 0 1 10680707 67108864 1 67108864 261175328271 1677721600 24453 1677721600 (Enclosure.Real.IsNear.const Bool.false 978120 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz763 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 978120 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz638 := qz763

noncomputable abbrev qz430 := qz638

noncomputable abbrev qz89 := qz430

noncomputable def Ns576p635 := @Enclosure.Real.IsNear.sqrt_image qz89 837309491 67108864 41 67108864 118523084 118523091 33554432 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 837309491 67108864 41 67108864 837309491 67108864 41 67108864 (Ns576p634 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p636 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz89) 237046175 67108864 7 67108864 9499413 9499415 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz89) Bool.false 237046175 67108864 7 67108864 237046175 67108864 7 67108864 (Ns576p635 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p637 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 18998828 67108864 2 67108864 4749707 16777216 1 33554432 (Ns576p636 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz431 := (@HMul.hMul Real Real Real qz590 qz588 qz632)

noncomputable abbrev qz90 := (Real.cos qz431)

noncomputable abbrev qz639 := (@HMul.hMul Real Real Real qz743 qz762 qz762)

noncomputable abbrev qz432 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz639 qz632) qz605)

noncomputable abbrev qz91 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz432))

noncomputable def Ns576p638 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz82) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz90) qz91) Bool.false 431916187186715 

noncomputable def Ns576p639 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz90) qz91 67822999 67108864 271 

noncomputable abbrev qz92 := (@Neg.neg Real Real.instNeg (Real.cos qz431))

noncomputable def Ns576p640 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz90) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz92)) Bool.true 67822999 67108864 271 67108864 (BSN.inv_eq_neg_inv_neg qz90) 

noncomputable def Ns576p641 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz92) Bool.false 67822999 67108864 271 67108864 67822999 67108864 

noncomputable def Ns576p642 := @Enclosure.Real.IsNear.recentre' qz90 Bool.true 66402248 67108864 1354514432 343597383680000 8300281 8388608 82673 20971520000 

noncomputable abbrev qz93 := qz431

noncomputable abbrev qz640 := (@Nat.cast Real Real.instNatCast 4194304)

noncomputable def Ns576p643 := @Enclosure.Real.IsNear.cos_image qz93 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12567597) qz640) Bool.false 12567597 4194304 129 33554432 Bool.true 66402248 67108864 1 

noncomputable def Ns576p644 := nat_lit 1106429092045710596971658463 

noncomputable def Ns576p645 := nat_lit 288230376151711744000000000000000 

noncomputable def Ns576p646 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz82 884279719003555 140737488355328 1 500000000000000 32003123 67108864 41 67108864 28299712613676208102265 9444732965739290427392 Ns576p644 

noncomputable def Ns576p647 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz1 837309491 67108864 41 67108864 12 1 0 1 32003123 32003123 67108864 41 

noncomputable def Ns576p648 := @Ns576p647 67108864 (@Enclosure.Real.IsNear.recentre' qz89 Bool.false 837309491 67108864 41 67108864 837309491 67108864 41 67108864 (Ns576p634 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p649 := @Enclosure.Real.IsNear.recentre' qz93 Bool.false 28299712613676208102265 9444732965739290427392 Ns576p644 Ns576p645 12567597 4194304 129 33554432 (@Ns576p646 Ns576p645 RS577to588.d55 (Ns576p648 rfl rfl) rfl) 

noncomputable def Ns576p650 := nat_lit 9748607935233185858759032989301710467706585050884853575839588809486473515095460525488218000093287401946549640924083701763438316986390238506721 

noncomputable def Ns576p651 := nat_lit 3199748981952908402888236469595506343845786745267286266730573485671603651729756095592792200843071864044570156112893519701331738213265121 

noncomputable def Ns576p652 := nat_lit 48701932082638607640855145967713201814690372274374366752662573257600247604692228957563284764820510761722002492869774624343871845279883506003681 

noncomputable def Ns576p653 := BSN.sin_dyadic_bound_f 195926415223 137438953472 4 3 67108864 20500001 Ns576p650 Ns576p274 Ns576p651 Ns576p652 Ns576p277 Ns576p651 66402248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 195926415223) qz371 0 3 Ns576p650 Ns576p274 Ns576p651 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 195926415223) qz372 0 3 Ns576p652 Ns576p277 Ns576p651 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p654 := @Ns576p643 10240000 (Ns576p649 rfl) (Enclosure.sfrac_false_div 12567597 4194304) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 12567597) qz640) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 861693486907477421195264) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 66402248 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 12567597 4194304 226375608064910080 72057594037927936 0 861693486907477421195264 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 66402248 67108864 861693486907477421195264 604462909807314587353088 195926415223 137438953472 20500001 20480000 (Ns576p653 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p655 := @Enclosure.Real.IsNear.inv_image qz92 8300281 8388608 82673 20971520000 33911364 33911635 33554432 (@Enclosure.Real.IsNear.neg qz90 Bool.true 8300281 8388608 82673 20971520000 (Ns576p642 (Ns576p654 rfl rfl) rfl)) 

noncomputable def Ns576p656 := Ns576p640 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz92) Bool.false 67822999 67108864 271 67108864 (@Ns576p641 271 67108864 (Ns576p655 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p657 := @Enclosure.Real.IsNear.recentre' qz91 Bool.true 12736570 33554432 

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz355 qz352 qz432)

noncomputable def Ns576p658 := @Enclosure.Real.IsNear.cos_image qz94 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 131542627)) qz384) Bool.true 131542627 67108864 

noncomputable def Ns576p659 := nat_lit 1242384994702381095028086985445 

noncomputable def Ns576p660 := nat_lit 633825300114114700748351602688 

noncomputable def Ns576p661 := nat_lit 29013923490078130842438759508621341 

noncomputable def Ns576p662 := @Enclosure.Real.IsNear.recentre' qz94 Bool.true Ns576p659 Ns576p660 Ns576p661 

noncomputable def Ns576p663 := nat_lit 3868562622766813359059763200000000000000 

noncomputable abbrev qz95 := qz432

noncomputable def Ns576p664 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz95 884279719003555 140737488355328 1 500000000000000 1404968323939799 

noncomputable abbrev qz433 := (@HSub.hSub Real Real Real qz594 qz639 qz632)

noncomputable abbrev qz96 := qz433

noncomputable def Ns576p665 := @Enclosure.Real.IsNear.subLit_tf qz96 qz31 1123493347229143 4503599627370496 5375721191 4503599627370496 1 16 

noncomputable abbrev qz434 := qz639

noncomputable abbrev qz97 := qz434

noncomputable def Ns576p666 := @Enclosure.Real.IsNear.subLit_ff_n qz97 qz82 1024199881753129 4503599627370496 2624257767 4503599627370496 32003123 67108864 41 67108864 

noncomputable def Ns576p667 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz82 32003123 67108864 41 67108864 32003123 67108864 41 67108864 1024199881753129 4503599627370496 

noncomputable def Ns576p668 := nat_lit 2479904812404395196722462814961828854125505013626572824715371745279060579408335443995875490030514783601 

noncomputable def Ns576p669 := nat_lit 26840965223001564982924393049645383106743413338928031312893105793006115831762984215723700084196721 

noncomputable def Ns576p670 := nat_lit 14957256986162387992998868585231065661540255266698857117144914595117797925325252365556103186344967587185 

noncomputable def Ns576p671 := BSN.cos_dyadic_bound_t 131542627 67108864 4 3 33554432 10240000 Ns576p668 Ns576p227 Ns576p669 Ns576p670 Ns576p230 Ns576p669 12736570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 131542627) qz606 0 3 Ns576p668 Ns576p227 Ns576p669 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 131542627) (BSN.cosOddQ 67108864) 0 3 Ns576p670 Ns576p230 Ns576p669 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p672 := @Ns576p657 5238308864 687194767360000 6368285 16777216 319721 41943040000 (@Ns576p658 505 67108864 Bool.true 12736570 33554432 1 10240000 (@Ns576p662 Ns576p663 131542627 67108864 505 67108864 (@Ns576p664 4503599627370496 5375721191 4503599627370496 Ns576p659 Ns576p660 Ns576p661 Ns576p663 RS577to588.d55 (@Ns576p665 0 1 22479493183036784 1404968323939799 4503599627370496 5375721191 4503599627370496 (@Ns576p666 75396362244105334423552 1123493347229143 4503599627370496 5375721191 4503599627370496 (@Ns576p667 2624257767 4503599627370496 (Ns576p648 rfl rfl) (Ns576p648 rfl rfl) rfl) (Ns576p648 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 131542627 67108864) (BSN.cos_neg_of_bound 131542627 67108864 Bool.true 12736570 33554432 1 10240000 (Ns576p671 rfl rfl)) rfl rfl) 

noncomputable def Ns576p673 := @Ns576p632 4961108611711132261 Ns576p539 (Ns576p633 qz33 (@Enclosure.Real.IsNear.of_eq qz637 (@Inv.inv Real Real.instInv (Real.sqrt qz89)) Bool.false 4749707 16777216 1 33554432 (BSN.rpow_neg_quarter_mk qz81 (BSN.t_div_two_pi_nonneg qz80 978120 1000 qz83)) Ns576p637) rfl) (@Ns576p638 1125899906842624 2599903679517 281474976710656000 (BSN.correction_mk qz82 (BSN.cos_two_pi_p_ne_zero_mk qz80 978120 1000 12 qz83 rfl rfl (@BSN.floor_sqrt_eq_dec qz80 978120 1000 12 qz83 rfl rfl rfl))) (@Ns576p639 67108864 6368285 16777216 319721 41943040000 431916187186715 1125899906842624 2599903679517 281474976710656000 Ns576p656 (Ns576p672 rfl) rfl)) 

noncomputable def Ns576p674 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (hardyZApproximantRS₀ qz80) Bool.false 96764181858336812538967 18889465931478580854784 1884334343736672412261 Ns576p539 (@Eq.refl Real (hardyZApproximantRS₀ qz80)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz80) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HMul.hMul Real Real Real qz5 qz633 (Zeta.RiemannSiegel.correction qz82))) Bool.false 96764181858336812538967 18889465931478580854784 1884334343736672412261 Ns576p539 (BSN.hardyZApproximantRS₀_eq qz80 12 (@BSN.floor_sqrt_eq_dec qz80 978120 1000 12 qz83 rfl rfl rfl)) (@Ns576p541 96764181858336812538967 18889465931478580854784 1884334343736672412261 Ns576p539 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz80) qz80 12)) Bool.false 351063737 67108864 267075 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz80) qz80 12) (Ns576p631 (Ns576p630 rfl rfl rfl rfl) rfl rfl)) (Ns576p673 rfl) rfl rfl)) 

theorem RS577to588.d62 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz80) Bool.false 96764181858336812538967 18889465931478580854784 1884334343736672412261 Ns576p539 := Ns576p674 

noncomputable def Ns576p675 := nat_lit 2361183241434822606848000 

noncomputable def Ns576p676 := nat_lit 23801674766211095413927039729664 

noncomputable abbrev qz764 := (Enclosure.sfrac Bool.false 979365 1000)

noncomputable abbrev qz641 := qz764

noncomputable abbrev qz435 := qz641

noncomputable abbrev qz98 := qz435

noncomputable abbrev qz765 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 979365 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz642 := qz765

noncomputable abbrev qz436 := qz642

noncomputable abbrev qz99 := qz436

noncomputable abbrev qz766 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 979365 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz643 := qz766

noncomputable abbrev qz437 := qz643

noncomputable abbrev qz100 := qz437

noncomputable abbrev qz644 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz99 qz9))

noncomputable def Ns576p677 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HMul.hMul Real Real Real qz5 qz644 (Zeta.RiemannSiegel.correction qz100)) 1230946649 268435456 267425 268435456 2047978253878178803083 18889465931478580854784 6048992895782584347 Ns576p675 Ns576p676 

noncomputable def Ns576p678 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin BSN.quadSignPos 11 12 979365 1000 287 536870912 268435456 9007199254740992 Bool.false 1064263449783 4557 1334074092 54 154981288 8 

noncomputable def Ns576p679 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 9 10 11 979365 1000 173 233 536870912 268435456 9007199254740992 Bool.false 1064263449783 4557 

noncomputable def Ns576p680 := Ns576p679 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 1147899078 215328 Bool.true 525235659 Bool.true 39730505 28296951008113761 1 Bool.false 445369143 Bool.true Bool.false 39694250 Bool.true Bool.true 1300705440 

noncomputable def Ns576p681 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 979365 1000 34 107 536870912 268435456 9007199254740992 Bool.false 1064263449783 4557 

noncomputable def Ns576p682 := Ns576p681 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 1190909828 175852 Bool.true 418778860 Bool.true 786227131 28296951008113761 1 Bool.false 381655051 Bool.true Bool.false 533838582 Bool.false Bool.true 1147899078 

noncomputable def Ns576p683 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 5 6 7 979365 1000 144 48 536870912 268435456 9007199254740992 Bool.false 1064263449783 4557 

noncomputable def Ns576p684 := Ns576p683 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 1311207774 130670 Bool.false 732282245 Bool.false 639232602 28296951008113761 1 Bool.false 110242784 Bool.false Bool.false 199202630 Bool.false Bool.true 1190909828 

noncomputable def Ns576p685 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 979365 1000 397 258 536870912 268435456 9007199254740992 Bool.false 1064263449783 4557 

noncomputable def Ns576p686 := Ns576p685 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 920250379 77167 Bool.false 564175620 Bool.false 457718821 28296951008113761 1 Bool.false 465923587 Bool.true Bool.false 353288911 Bool.true Bool.true 1311207774 

noncomputable def Ns576p687 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz98) qz98 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 1 2 3 979365 1000 829 577 536870912 268435456 9007199254740992 Bool.false 1064263449783 4557 

noncomputable def Ns576p688 := Ns576p687 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 536870896 4621 Bool.false 703803492 Bool.false 28592323 28296951008113761 1 Bool.false 518845963 Bool.true Bool.false 28578808 Bool.true Bool.true 920250379 

noncomputable def Ns576p689 := nat_lit 403345136378679325972869657929451338931189248379035159 

noncomputable def Ns576p690 := nat_lit 203468672406694919278303524340600992815020978995200 

noncomputable def Ns576p691 := nat_lit 432478399432998135112161889500000000 

noncomputable def Ns576p692 := nat_lit 2541325555078042077595717628071005000000 

noncomputable abbrev qz645 := (@Eq.refl Real qz764)

noncomputable abbrev qz438 := qz645

noncomputable abbrev qz101 := qz438

noncomputable def Ns576p693 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz98 979365 1000 3836624212900 16000000 1958730 4000 2000 Ns576p691 Ns576p692 qz101 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p694 := nat_lit 18150531137040569668779134606825310251903516177056582155000000 

noncomputable abbrev qz646 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1958730))))

noncomputable abbrev qz439 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 979365 4000) (Real.log (Enclosure.sfrac Bool.false 3836624212900 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz646))

noncomputable abbrev qz647 := (Enclosure.sfrac Bool.false 979365 2000)

noncomputable abbrev qz102 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz439 qz647) (@HMul.hMul Real Real Real qz355 qz647 (Real.log Real.pi)))

noncomputable def Ns576p695 := @Enclosure.Real.IsNear.addLit_ft_p qz102 (Enclosure.sfrac Bool.true Ns576p691 Ns576p692) 7142151724299969956231 3602879701896396800 27806372379672711 3276800000000000000000 Ns576p691 Ns576p692 0 1 Ns576p694 

noncomputable def Ns576p696 := nat_lit 95860337746682435799358426316800 

noncomputable abbrev qz103 := (@HSub.hSub Real Real Real qz359 qz439 qz647)

noncomputable def Ns576p697 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (@HMul.hMul Real Real Real qz5 qz647 (Real.log Real.pi)) 9161761039702673656199 3602879701896396800 9642249647889 3200000000000000000 7523630989353 13421772800 587619 107374182400 Ns576p696 7142151724299969956231 3602879701896396800 

noncomputable def Ns576p698 := nat_lit 3664704415881069462479600 

noncomputable abbrev qz104 := qz439

noncomputable def Ns576p699 := @Enclosure.Real.IsNear.subLit_ff_p qz104 qz647 2185205635865311196443 720575940379279360 9642249647889 3200000000000000000 979365 2000 0 1 Ns576p698 9161761039702673656199 3602879701896396800 9642249647889 3200000000000000000 

noncomputable def Ns576p700 := nat_lit 4920645643705461636902586431899172864 

noncomputable def Ns576p701 := nat_lit 119804690933373313314979840 

noncomputable def Ns576p702 := nat_lit 135986373042072594720075364628148700945906871372662157834659565729804761857379316984655278194225350126984208383632271363874002215692242783966492171121064390250000000000000000000000000000 

noncomputable def Ns576p703 := nat_lit 4109417448375782923114732634336518593999586305385472030368476998625394782938707394688752216965394770169450532439248227960628878331877313547162908356655184150000000000000000000000000000 

noncomputable def Ns576p704 := nat_lit 313770986643500934321487443177207709808151291162203322752265886347242300986800172090417989929945294204754457960101920850551456204374469233638086959350000000000000000000000000000 

noncomputable def Ns576p705 := BSN.log_dyadic_bound 1739472212900 5933776212900 8 7 Ns576p702 268435456 81920000 Ns576p703 Ns576p704 162138407 7673248425800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1739472212900) (BSN.artanhQ 5933776212900) 0 7 Ns576p703 Ns576p702 Ns576p704 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz440 := (Real.log (Enclosure.sfrac Bool.false 3836624212900 16000000))

noncomputable def Ns576p706 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 979365 4000) qz440 979365 4000 0 1 55788406605540455 4503599627370496 48828193 4000000000000000 2185488513409405108443 720575940379279360 9564124647489 3200000000000000000 (Enclosure.Real.IsNear.const Bool.false 979365 4000) (BSN.isNear_log_sfrac 3836624212900 16000000 55788406605540455 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3836624212900) qz362)) Bool.false Ns576p701 Ns576p112 1000001392640000 81920000000000000000000 55788406605540455 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3836624212900 16000000 17 7673248425800 4194304000000 162138407 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p705 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p707 := BSN.arctan_dyadic_bound_f 1000 1958730 1 0 33554432 10240000 0 1 1 0 1 1 17130 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1958730) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1958730) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p708 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1958730))) 884279719003555 562949953421312 1 2000000000000000 17130 33554432 1 10240000 29661860367581786931200 883992325293475 562949953421312 195312501 2000000000000000 qz17 (Ns576p707 rfl) rfl rfl 

noncomputable abbrev qz441 := (@HMul.hMul Real Real Real qz590 qz595 qz646)

noncomputable abbrev qz105 := qz441

noncomputable abbrev qz442 := qz646

noncomputable abbrev qz106 := qz442

noncomputable def Ns576p709 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 979365 4000) qz440) qz105 2185488513409405108443 720575940379279360 9564124647489 3200000000000000000 883992325293475 2251799813685248 195312501 8000000000000000 Ns576p700 2185205635865311196443 720575940379279360 9642249647889 3200000000000000000 (Ns576p706 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz106 1 4 0 1 883992325293475 562949953421312 195312501 2000000000000000 883992325293475 2251799813685248 195312501 8000000000000000 qz369 Ns576p708 rfl) 

noncomputable def Ns576p710 := @Ns576p695 Ns576p689 Ns576p690 27806372379672711 3276800000000000000000 (@Ns576p697 27806372379672711 3276800000000000000000 (Ns576p699 (Ns576p709 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 979365 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz647 (Real.log Real.pi) 979365 2000 0 1 38410761 33554432 3 268435456 7523630989353 13421772800 587619 107374182400 (Enclosure.Real.IsNear.const Bool.false 979365 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p691 Ns576p692) 

noncomputable def Ns576p711 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns576p689 Ns576p690 27806372379672711 3276800000000000000000 66516465611 33554432 571 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz370 qz102 (Enclosure.sfrac Bool.true Ns576p691 Ns576p692)) Bool.false Ns576p689 Ns576p690 27806372379672711 3276800000000000000000 Ns576p693 (Ns576p710 rfl rfl)) 

noncomputable abbrev qz443 := (BSN.cosEvenQ 137438953472)

noncomputable abbrev qz444 := (BSN.cosOddQ 137438953472)

noncomputable def Ns576p712 := BSN.cos_dyadic_bound_f 25812947 137438953472 1 0 67108864 20500001 0 1 1 0 1 1 67108862 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 25812947) qz443 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 25812947) qz444 0 0 rfl) rfl rfl 

noncomputable def Ns576p713 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz98) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66516465611) qz373) Bool.false 66516465611 33554432 571 67108864 Bool.true 67108862 67108864 1 10240000 (Ns576p711 rfl) (Enclosure.sfrac_false_div 66516465611 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66516465611) qz373) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 908212346165051523072) qz374) 226375608064910080 72057594037927936 Bool.false 67108862 67108864 315 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 66516465611 33554432 226375608064910080 72057594037927936 315 908212346165051523072 Ns576p124 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108862 67108864 908212346165051523072 Ns576p124 25812947 137438953472 20500001 20480000 (Ns576p712 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p714 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz98) Bool.false Ns576p689 Ns576p690 27806372379672711 3276800000000000000000 1064263449783 536870912 4557 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz98) (@HAdd.hAdd Real Real Real qz370 qz102 (Enclosure.sfrac Bool.true Ns576p691 Ns576p692)) Bool.false Ns576p689 Ns576p690 27806372379672711 3276800000000000000000 Ns576p693 (Ns576p710 rfl rfl)) 

noncomputable def Ns576p715 := Ns576p688 77167 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 829 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 518845963 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 577 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 28578808 536870912) qz101 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) Bool.true 33554431 33554432 360971 41943040000 536870896 536870912 4621 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 33554431 33554432 360971 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz98) qz98) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz98)) Bool.true 67108862 67108864 5914148864 687194767360000 33554431 33554432 360971 41943040000 (Ns576p713 rfl rfl) rfl)) rfl) (Ns576p714 rfl) RS577to588.d7 

noncomputable def Ns576p716 := nat_lit 87960514008750946481347486131567651564290680993830978356505892538648468721721036696253269056558973904951061774336 

noncomputable def Ns576p717 := nat_lit 14771241807415888565066159386080043409835214670765922380125031670605658194277514031492787750317380375412736 

noncomputable def Ns576p718 := nat_lit 439537237163529311691720738464066228405123265181585457380263436044673778678842493835068875278285645884779130781696 

noncomputable def Ns576p719 := BSN.sin_dyadic_bound_f 703803492 536870912 4 3 536870912 268435456 Ns576p716 Ns576p135 Ns576p717 Ns576p718 Ns576p138 Ns576p717 518845963 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 703803492) qz375 0 3 Ns576p716 Ns576p135 Ns576p717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 703803492) qz376 0 3 Ns576p718 Ns576p138 Ns576p717 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p720 := nat_lit 668340478405152726310220796241 

noncomputable def Ns576p721 := BSN.sin_dyadic_bound_f 28592323 536870912 2 1 536870912 268435456 Ns576p720 Ns576p300 Ns576p720 Ns576p720 Ns576p301 Ns576p720 28578808 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 28592323) qz375 0 1 Ns576p720 Ns576p300 Ns576p720 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 28592323) qz376 0 1 Ns576p720 Ns576p301 Ns576p720 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p722 := nat_lit 25462066371692144716234011730951434251051409297979848023991061940183040000 

noncomputable def Ns576p723 := nat_lit 10263949787290422795891048825742440748875223994654560682430489600000000 

noncomputable def Ns576p724 := nat_lit 66669746483347623096086207121059697182017416846336827916966941431603200000 

noncomputable def Ns576p725 := BSN.sin_dyadic_bound_f 564175620 536870912 3 2 536870912 268435456 Ns576p722 Ns576p151 Ns576p723 Ns576p724 Ns576p154 Ns576p723 465923587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 564175620) qz375 0 2 Ns576p722 Ns576p151 Ns576p723 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 564175620) qz376 0 2 Ns576p724 Ns576p154 Ns576p723 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p726 := nat_lit 6128023481994788969027343204138294615173776258172697239709320320167932641 

noncomputable def Ns576p727 := nat_lit 1926593828857532461883375663628039476236886316853903639246964431745761 

noncomputable def Ns576p728 := nat_lit 18380217258326651842158262861087627766568855001884383911849467031640306401 

noncomputable def Ns576p729 := BSN.cos_dyadic_bound_f 457718821 536870912 3 2 536870912 268435456 Ns576p726 Ns576p141 Ns576p727 Ns576p728 Ns576p144 Ns576p727 353288911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 457718821) qz377 0 2 Ns576p726 Ns576p141 Ns576p727 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 457718821) qz378 0 2 Ns576p728 Ns576p144 Ns576p727 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p730 := Ns576p686 130670 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 397 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 465923587 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 258 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 353288911 536870912) qz101 rfl rfl (Ns576p715 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p719 rfl rfl) (Ns576p721 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p714 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p725 rfl rfl) (Ns576p729 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p731 := nat_lit 39691072982748405601516884366783356108586860961810390895594349804955684474348814793565317124353178304888348140625 

noncomputable def Ns576p732 := nat_lit 23776178453930188983681637613380952350848025435266339375933011713607659564840360604344021646615625244140625 

noncomputable def Ns576p733 := nat_lit 240462336599747037907325390029870153414502215618102016565370600920450051806663386841807734537738808792405941740625 

noncomputable def Ns576p734 := BSN.cos_dyadic_bound_f 732282245 536870912 4 3 536870912 268435456 Ns576p731 Ns576p162 Ns576p732 Ns576p733 Ns576p165 Ns576p732 110242784 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 732282245) qz377 0 3 Ns576p731 Ns576p162 Ns576p732 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 732282245) qz378 0 3 Ns576p733 Ns576p165 Ns576p732 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p735 := nat_lit 23027124811506958043981196448100724950498073948814918733138852969069645270126784449918012760505182309373388722176 

noncomputable def Ns576p736 := nat_lit 4654864033391553242299319759096351359423785080591773604815160230047099645149998381795866728720674552221696 

noncomputable def Ns576p737 := nat_lit 139586584625165758779655423068910673526348321903134832116819901494915558154352469221757088426808519715503484375040 

noncomputable def Ns576p738 := BSN.cos_dyadic_bound_f 639232602 536870912 4 3 536870912 268435456 Ns576p735 Ns576p162 Ns576p736 Ns576p737 Ns576p165 Ns576p736 199202630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 639232602) qz377 0 3 Ns576p735 Ns576p162 Ns576p736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 639232602) qz378 0 3 Ns576p737 Ns576p165 Ns576p736 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p739 := Ns576p684 175852 BSN.abs_quadSignPos (BSN.cos_quad_nat0 144 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 110242784 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 48 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 199202630 536870912) qz101 rfl rfl (Ns576p730 rfl rfl) (Ns576p714 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p734 rfl rfl) (Ns576p738 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p740 := nat_lit 4293618707286510047729731156445634263235689397721562200972490780876800000 

noncomputable def Ns576p741 := nat_lit 945971391873990812441727949011818263445329593743775316377625600000000 

noncomputable def Ns576p742 := nat_lit 12878964179075782161564310013438879153180177533977199052284717091430400000 

noncomputable def Ns576p743 := BSN.cos_dyadic_bound_f 418778860 536870912 3 2 536870912 268435456 Ns576p740 Ns576p141 Ns576p741 Ns576p742 Ns576p144 Ns576p741 381655051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 418778860) qz377 0 2 Ns576p740 Ns576p141 Ns576p741 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 418778860) qz378 0 2 Ns576p742 Ns576p144 Ns576p741 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p744 := nat_lit 137059899458353145242315510125153253338343990929979445918985084850084195371062345790331100139581942852815919284561 

noncomputable def Ns576p745 := nat_lit 55792563409464241140946994970320449496011660890852097507946914164353323310716947610891729051725806305050961 

noncomputable def Ns576p746 := nat_lit 684655894615566299851543118243449509802176591793926481862386506751237308387621326826170494599667798154383547203921 

noncomputable def Ns576p747 := BSN.sin_dyadic_bound_f 786227131 536870912 4 3 536870912 268435456 Ns576p744 Ns576p135 Ns576p745 Ns576p746 Ns576p138 Ns576p745 533838582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 786227131) qz375 0 3 Ns576p744 Ns576p135 Ns576p745 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 786227131) qz376 0 3 Ns576p746 Ns576p138 Ns576p745 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p748 := Ns576p682 215328 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 381655051 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 533838582 536870912) qz101 rfl rfl (Ns576p739 rfl) (Ns576p714 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p743 rfl rfl) (Ns576p747 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p749 := nat_lit 19125361023002337941837182486949546802341655646498326918394382040999273825 

noncomputable def Ns576p750 := nat_lit 5792067658768185509779741434632827744927903438895455593973615465735521 

noncomputable def Ns576p751 := nat_lit 50080853617368117547319644074926074189783976754308835001023614729958335841 

noncomputable def Ns576p752 := BSN.sin_dyadic_bound_f 525235659 536870912 3 2 536870912 268435456 Ns576p749 Ns576p151 Ns576p750 Ns576p751 Ns576p154 Ns576p750 445369143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 525235659) qz375 0 2 Ns576p749 Ns576p151 Ns576p750 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 525235659) qz376 0 2 Ns576p751 Ns576p154 Ns576p750 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p753 := nat_lit 2491703378160931114929402750625 

noncomputable def Ns576p754 := BSN.sin_dyadic_bound_f 39730505 536870912 2 1 536870912 268435456 Ns576p753 Ns576p300 Ns576p753 Ns576p753 Ns576p301 Ns576p753 39694250 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 39730505) qz375 0 1 Ns576p753 Ns576p300 Ns576p753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 39730505) qz376 0 1 Ns576p753 Ns576p301 Ns576p753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p755 := Ns576p680 250832 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 445369143 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 233 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 39694250 536870912) qz101 rfl rfl (Ns576p748 rfl) (Ns576p714 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p752 rfl rfl) (Ns576p754 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p756 := nat_lit 991755927961968158742454873033176086962806806579299193188026133583996545 

noncomputable def Ns576p757 := nat_lit 15583801001916925089830562390980637098310859203377249578819921618561 

noncomputable def Ns576p758 := nat_lit 2597430770889246835970569703700161497204430085364216228516940831894513281 

noncomputable def Ns576p759 := BSN.sin_dyadic_bound_f 250659503 536870912 3 2 536870912 268435456 Ns576p756 Ns576p151 Ns576p757 Ns576p758 Ns576p154 Ns576p757 241651535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 250659503) qz375 0 2 Ns576p756 Ns576p151 Ns576p757 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 250659503) qz376 0 2 Ns576p758 Ns576p154 Ns576p757 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p760 := Ns576p678 Bool.true 1300705440 250832 Bool.true 250659503 28296951008113761 1 Bool.false 241651535 Bool.false Bool.true 1230946649 267425 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 241651535 536870912) qz101 rfl (Ns576p755 rfl) (Ns576p714 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p759 rfl rfl) rfl 

noncomputable def Ns576p761 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) 1230946649 536870912 267425 536870912 1230946649 536870912 267425 536870912 1321718900143947776 1230946649 268435456 267425 268435456 (Ns576p760 rfl rfl rfl rfl) 

noncomputable def Ns576p762 := @Enclosure.Real.IsNear.mulLit_ff qz644 (Zeta.RiemannSiegel.correction qz100) 4748197 16777216 1 33554432 431317035472239 1125899906842624 6341391213261 703687441776640000 2047978253878178803083 18889465931478580854784 

noncomputable abbrev qz648 := (@HPow.hPow Real Real Real qz7 qz99 qz9)

noncomputable def Ns576p763 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz648 1 1 0 1 4748197 16777216 1 33554432 4748197 16777216 1 33554432 

noncomputable def Ns576p764 := @Enclosure.Real.IsNear.sqrt_image qz99 2092062122211 13421772800 195873 13421772800 418921083 418921123 33554432 (@Enclosure.Real.IsNear.of_eq qz99 (@HMul.hMul Real Real Real qz5 qz98 qz3) Bool.false 2092062122211 13421772800 195873 13421772800 (BSN.t_div_two_pi_mk qz98 979365 1000 qz101) (@Enclosure.Real.IsNear.mulLit_ff qz98 qz3 979365 1000 0 1 10680707 67108864 1 67108864 2092062122211 13421772800 195873 13421772800 (Enclosure.Real.IsNear.const Bool.false 979365 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz767 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 979365 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz649 := qz767

noncomputable abbrev qz445 := qz649

noncomputable abbrev qz107 := qz445

noncomputable def Ns576p765 := @Enclosure.Real.IsNear.sqrt_image qz107 418921103 33554432 5 8388608 118560781 118560788 33554432 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 837842206 67108864 40 67108864 418921103 33554432 5 8388608 (Ns576p764 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p766 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz107) 237121569 67108864 7 67108864 9496393 9496395 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz107) Bool.false 237121569 67108864 7 67108864 237121569 67108864 7 67108864 (Ns576p765 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p767 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 18992788 67108864 2 67108864 4748197 16777216 1 33554432 (Ns576p766 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz446 := (@HMul.hMul Real Real Real qz590 qz588 qz643)

noncomputable abbrev qz108 := (Real.cos qz446)

noncomputable abbrev qz650 := (@HMul.hMul Real Real Real qz743 qz766 qz766)

noncomputable abbrev qz447 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz650 qz643) qz605)

noncomputable abbrev qz109 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz447))

noncomputable def Ns576p768 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz100) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz108) qz109) Bool.false 431317035472239 

noncomputable def Ns576p769 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz108) qz109 33707601 33554432 131 

noncomputable abbrev qz110 := (@Neg.neg Real Real.instNeg (Real.cos qz446))

noncomputable def Ns576p770 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz108) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz110)) Bool.true 33707601 33554432 131 33554432 (BSN.inv_eq_neg_inv_neg qz108) 

noncomputable def Ns576p771 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz110) Bool.false 67415202 67108864 262 67108864 33707601 33554432 

noncomputable def Ns576p772 := @Enclosure.Real.IsNear.recentre' qz108 Bool.true 66803918 67108864 661897216 171798691840000 33401959 33554432 40399 10485760000 

noncomputable abbrev qz111 := qz446

noncomputable def Ns576p773 := @Enclosure.Real.IsNear.cos_image qz111 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 204428699) qz384) Bool.false 204428699 67108864 63 16777216 Bool.true 66803918 67108864 1 

noncomputable def Ns576p774 := nat_lit 134930377080155317315333347 

noncomputable def Ns576p775 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz100 884279719003555 140737488355328 1 500000000000000 16267919 33554432 5 8388608 14385390842092593452045 4722366482869645213696 Ns576p774 

noncomputable def Ns576p776 := @Enclosure.Real.IsNear.subLit_ff_p qz107 qz1 418921103 33554432 5 8388608 12 1 0 1 16267919 16267919 33554432 5 

noncomputable def Ns576p777 := @Ns576p776 8388608 (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 837842206 67108864 40 67108864 418921103 33554432 5 8388608 (Ns576p764 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p778 := @Enclosure.Real.IsNear.recentre' qz111 Bool.false 14385390842092593452045 4722366482869645213696 Ns576p774 Ns576p202 204428699 67108864 63 16777216 (@Ns576p775 Ns576p202 RS577to588.d55 (Ns576p777 rfl rfl) rfl) 

noncomputable def Ns576p779 := nat_lit 14269470509942175493521408 

noncomputable def Ns576p780 := nat_lit 11188458279836394282083835993481997518853803340192430221545282380471542761435813070070230802149416887496712842200427804769602119668437073891041 

noncomputable def Ns576p781 := nat_lit 4834334451121686483043225781634784008417118235220479723069428313667214358583993171046152652396706676773184392153371959667321202261987041 

noncomputable def Ns576p782 := nat_lit 55888163332488140094798019001121336007054678184205693040610642236710388967399189230796466467791677382357878109560849406840095855279432893042401 

noncomputable def Ns576p783 := BSN.sin_dyadic_bound_f 202781372279 137438953472 4 3 67108864 20500001 Ns576p780 Ns576p274 Ns576p781 Ns576p782 Ns576p277 Ns576p781 66803918 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 202781372279) qz371 0 3 Ns576p780 Ns576p274 Ns576p781 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 202781372279) qz372 0 3 Ns576p782 Ns576p277 Ns576p781 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p784 := @Ns576p773 10240000 (Ns576p778 rfl) (Enclosure.sfrac_false_div 204428699 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 204428699) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p779) qz386) 226375608064910080 72057594037927936 Bool.false 66803918 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 204428699 67108864 226375608064910080 72057594037927936 0 Ns576p779 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 66803918 67108864 Ns576p779 Ns576p112 202781372279 137438953472 20500001 20480000 (Ns576p783 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p785 := @Enclosure.Real.IsNear.inv_image qz110 33401959 33554432 40399 10485760000 33707470 33707732 33554432 (@Enclosure.Real.IsNear.neg qz108 Bool.true 33401959 33554432 40399 10485760000 (Ns576p772 (Ns576p784 rfl rfl) rfl)) 

noncomputable def Ns576p786 := Ns576p770 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz110) Bool.false 33707601 33554432 131 33554432 (@Ns576p771 131 33554432 (Ns576p785 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p787 := @Enclosure.Real.IsNear.recentre' qz109 Bool.true 12795839 33554432 

noncomputable abbrev qz112 := (@HMul.hMul Real Real Real qz355 qz352 qz447)

noncomputable def Ns576p788 := @Enclosure.Real.IsNear.cos_image qz112 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 131670805)) qz384) Bool.true 131670805 67108864 

noncomputable def Ns576p789 := nat_lit 310898899129972332794458364605 

noncomputable def Ns576p790 := nat_lit 4458793874741484775051056231514539 

noncomputable def Ns576p791 := @Enclosure.Real.IsNear.recentre' qz112 Bool.true Ns576p789 Ns576p218 Ns576p790 

noncomputable abbrev qz113 := qz447

noncomputable def Ns576p792 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz113 884279719003555 140737488355328 1 500000000000000 351584337454111 

noncomputable abbrev qz448 := (@HSub.hSub Real Real Real qz594 qz650 qz643)

noncomputable abbrev qz114 := qz448

noncomputable def Ns576p793 := @Enclosure.Real.IsNear.subLit_tf qz114 qz31 281215593276447 1125899906842624 165225725 140737488355328 1 16 

noncomputable abbrev qz449 := qz650

noncomputable abbrev qz115 := qz449

noncomputable def Ns576p794 := @Enclosure.Real.IsNear.subLit_ff_n qz115 qz100 264645188590561 1125899906842624 81339645 140737488355328 16267919 33554432 5 8388608 

noncomputable def Ns576p795 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz100 16267919 33554432 5 8388608 16267919 33554432 5 8388608 264645188590561 1125899906842624 

noncomputable def Ns576p796 := nat_lit 2489669698404014468590394417131312276273639727856744604745493184686740212422295774057622321772523140625 

noncomputable def Ns576p797 := nat_lit 27156505788727493325792277221328467241288272196771386111562991614936494772059335546703984619140625 

noncomputable def Ns576p798 := nat_lit 15015812342312819461171588017364611211938167808667630006274894541086600269067567909290979060994436740625 

noncomputable def Ns576p799 := BSN.cos_dyadic_bound_t 131670805 67108864 4 3 33554432 10240000 Ns576p796 Ns576p227 Ns576p797 Ns576p798 Ns576p230 Ns576p797 12795839 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 131670805) qz606 0 3 Ns576p796 Ns576p227 Ns576p797 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 131670805) (BSN.cosOddQ 67108864) 0 3 Ns576p798 Ns576p230 Ns576p797 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p800 := @Ns576p787 321634304 42949672960000 12795839 33554432 19631 2621440000 (@Ns576p788 31 4194304 Bool.true 12795839 33554432 1 10240000 (@Ns576p791 Ns576p221 131670805 67108864 31 4194304 (@Ns576p792 1125899906842624 165225725 140737488355328 Ns576p789 Ns576p218 Ns576p790 Ns576p221 RS577to588.d55 (@Ns576p793 0 1 5625349399265776 351584337454111 1125899906842624 165225725 140737488355328 (@Ns576p794 9436029501934198063104 281215593276447 1125899906842624 165225725 140737488355328 (@Ns576p795 81339645 140737488355328 (Ns576p777 rfl rfl) (Ns576p777 rfl rfl) rfl) (Ns576p777 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 131670805 67108864) (BSN.cos_neg_of_bound 131670805 67108864 Bool.true 12795839 33554432 1 10240000 (Ns576p799 rfl rfl)) rfl rfl) 

noncomputable def Ns576p801 := @Ns576p762 6048992895782584347 Ns576p675 (Ns576p763 qz33 (@Enclosure.Real.IsNear.of_eq qz648 (@Inv.inv Real Real.instInv (Real.sqrt qz107)) Bool.false 4748197 16777216 1 33554432 (BSN.rpow_neg_quarter_mk qz99 (BSN.t_div_two_pi_nonneg qz98 979365 1000 qz101)) Ns576p767) rfl) (@Ns576p768 1125899906842624 6341391213261 703687441776640000 (BSN.correction_mk qz100 (BSN.cos_two_pi_p_ne_zero_mk qz98 979365 1000 12 qz101 rfl rfl (@BSN.floor_sqrt_eq_dec qz98 979365 1000 12 qz101 rfl rfl rfl))) (@Ns576p769 33554432 12795839 33554432 19631 2621440000 431317035472239 1125899906842624 6341391213261 703687441776640000 Ns576p786 (Ns576p800 rfl) rfl)) 

noncomputable def Ns576p802 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (hardyZApproximantRS₀ qz98) Bool.true 88668148093711940251019 18889465931478580854784 2358344169359756984347 Ns576p675 (@Eq.refl Real (hardyZApproximantRS₀ qz98)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz98) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HMul.hMul Real Real Real qz5 qz644 (Zeta.RiemannSiegel.correction qz100))) Bool.true 88668148093711940251019 18889465931478580854784 2358344169359756984347 Ns576p675 (BSN.hardyZApproximantRS₀_eq qz98 12 (@BSN.floor_sqrt_eq_dec qz98 979365 1000 12 qz101 rfl rfl rfl)) (@Ns576p677 88668148093711940251019 18889465931478580854784 2358344169359756984347 Ns576p675 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz98) qz98 12)) Bool.true 1230946649 268435456 267425 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz98) qz98 12) (Ns576p761 (Ns576p760 rfl rfl rfl rfl) rfl rfl)) (Ns576p801 rfl) rfl rfl)) 

theorem RS577to588.d63 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz98) Bool.true 88668148093711940251019 18889465931478580854784 2358344169359756984347 Ns576p675 := Ns576p802 

noncomputable def Ns576p803 := nat_lit 47223664828696452136960000 

noncomputable def Ns576p804 := nat_lit 2319257240050513148192439140352 

noncomputable abbrev qz768 := (Enclosure.sfrac Bool.false 980609 1000)

noncomputable abbrev qz651 := qz768

noncomputable abbrev qz450 := qz651

noncomputable abbrev qz116 := qz450

noncomputable abbrev qz769 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 980609 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz652 := qz769

noncomputable abbrev qz451 := qz652

noncomputable abbrev qz117 := qz451

noncomputable abbrev qz770 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 980609 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz653 := qz770

noncomputable abbrev qz452 := qz653

noncomputable abbrev qz118 := qz452

noncomputable abbrev qz654 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz117 qz9))

noncomputable def Ns576p805 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HMul.hMul Real Real Real qz5 qz654 (Zeta.RiemannSiegel.correction qz118)) 59765775 268435456 267767 268435456 8182663630221575403783 75557863725914323419136 121093978314440408697 Ns576p803 Ns576p804 

noncomputable def Ns576p806 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin BSN.quadSignPos 11 12 980609 1000 287 536870912 268435456 9007199254740992 Bool.false 1065949702023 4563 1334074092 54 154981288 8 

noncomputable def Ns576p807 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 9 10 11 980609 1000 173 232 536870912 268435456 9007199254740992 Bool.false 1065949702023 4563 

noncomputable def Ns576p808 := Ns576p807 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 93009415 215604 Bool.true 376804969 Bool.true 798269235 28296951008113761 1 Bool.false 346622413 Bool.true Bool.false 44992787 Bool.false Bool.true 3036386 

noncomputable def Ns576p809 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 980609 1000 34 107 536870912 268435456 9007199254740992 Bool.false 1065949702023 4563 

noncomputable def Ns576p810 := Ns576p809 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 122152415 176078 Bool.true 121317865 Bool.true 567429570 28296951008113761 1 Bool.false 523221912 Bool.true Bool.false 467531665 Bool.false Bool.false 93009415 

noncomputable def Ns576p811 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 980609 1000 145 49 536870912 268435456 9007199254740992 Bool.false 1065949702023 4563 

noncomputable def Ns576p812 := Ns576p811 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 331886493 130838 Bool.false 378561874 Bool.false 182560025 28296951008113761 1 Bool.false 347962209 Bool.true Bool.false 179062064 Bool.true Bool.false 122152415 

noncomputable def Ns576p813 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 3 4 5 980609 1000 398 259 536870912 268435456 9007199254740992 Bool.false 1065949702023 4563 

noncomputable def Ns576p814 := Ns576p813 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 401488428 77267 Bool.false 481252190 Bool.false 225765087 28296951008113761 1 Bool.false 335235245 Bool.true Bool.false 219169726 Bool.false Bool.false 331886493 

noncomputable def Ns576p815 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz116) qz116 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 1 2 3 980609 1000 831 578 536870912 268435456 9007199254740992 Bool.false 1065949702023 4563 

noncomputable def Ns576p816 := Ns576p815 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 536870840 4629 Bool.false 240495623 Bool.false 137802364 28296951008113761 1 Bool.false 232532708 Bool.false Bool.false 519282453 Bool.true Bool.false 401488428 

noncomputable def Ns576p817 := nat_lit 286223113435980116914942615819113147620650514756873208925103 

noncomputable def Ns576p818 := nat_lit 144157706178952908721175395374115391553370498736848896000 

noncomputable def Ns576p819 := nat_lit 435232079001406662669485476183520000 

noncomputable def Ns576p820 := nat_lit 2560755273232347461508158576999168182080 

noncomputable abbrev qz655 := (@Eq.refl Real qz768)

noncomputable abbrev qz453 := qz655

noncomputable abbrev qz119 := qz453

noncomputable def Ns576p821 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz116 980609 1000 3846377043524 16000000 1961218 4000 2000 Ns576p819 Ns576p820 qz119 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p822 := nat_lit 91591396299513637412781637062116207238608164722199426856032960 

noncomputable abbrev qz656 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1961218))))

noncomputable abbrev qz454 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 980609 4000) (Real.log (Enclosure.sfrac Bool.false 3846377043524 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz656))

noncomputable abbrev qz657 := (Enclosure.sfrac Bool.false 980609 2000)

noncomputable abbrev qz120 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz454 qz657) (@HMul.hMul Real Real Real qz355 qz657 (Real.log Real.pi)))

noncomputable def Ns576p823 := @Enclosure.Real.IsNear.addLit_ft_p qz120 (Enclosure.sfrac Bool.true Ns576p819 Ns576p820) 35767339853739823592487 18014398509481984000 139207953586548263 16384000000000000000000 Ns576p819 Ns576p820 0 1 Ns576p822 

noncomputable def Ns576p824 := nat_lit 2400305545886405712852201504768000 

noncomputable abbrev qz121 := (@HSub.hSub Real Real Real qz359 qz454 qz657)

noncomputable def Ns576p825 := @Enclosure.Real.IsNear.subLit_ff_p qz121 (@HMul.hMul Real Real Real qz5 qz657 (Real.log Real.pi)) 45878213078572903560231 18014398509481984000 48271990511537 16000000000000000000 37665937933449 67108864000 2941827 536870912000 Ns576p824 35767339853739823592487 18014398509481984000 

noncomputable def Ns576p826 := nat_lit 91756426157145807120462000 

noncomputable abbrev qz122 := qz454

noncomputable def Ns576p827 := @Enclosure.Real.IsNear.subLit_ff_p qz122 qz657 54710753732565212984359 18014398509481984000 48271990511537 16000000000000000000 980609 2000 0 1 Ns576p826 45878213078572903560231 18014398509481984000 48271990511537 16000000000000000000 

noncomputable def Ns576p828 := nat_lit 123197665061569833182217615191973036032 

noncomputable def Ns576p829 := nat_lit 119829244774714519372955648 

noncomputable def Ns576p830 := nat_lit 139149149014847156543511892069399459095462084522824705920366090696965477397042167475959169418780553443908204175292870605623883843430987995771752391243407186462888147798015193819539046400 

noncomputable def Ns576p831 := nat_lit 4240203137250986628186998699326832536117057862051664711854930941707723442333739053181562076246503318419243659435526194552744057315508656328255857753227262791057618080365822533791907840 

noncomputable def Ns576p832 := nat_lit 339318436087708704666042081209872120328916071913185915524494632732995897226543165159264487057072833903472960919241395005388636204889324613070559518896879867388216703270529269760 

noncomputable def Ns576p833 := BSN.log_dyadic_bound 1749225043524 5943529043524 8 7 Ns576p830 268435456 81920000 Ns576p831 Ns576p832 162819913 7692754087048 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1749225043524) (BSN.artanhQ 5943529043524) 0 7 Ns576p831 Ns576p830 Ns576p832 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz455 := (Real.log (Enclosure.sfrac Bool.false 3846377043524 16000000))

noncomputable def Ns576p834 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 980609 4000) qz455 980609 4000 0 1 55799840378907751 4503599627370496 48828193 4000000000000000 54717825674120350800359 18014398509481984000 47881365509537 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 980609 4000) (BSN.isNear_log_sfrac 3846377043524 16000000 55799840378907751 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3846377043524) qz362)) Bool.false Ns576p829 Ns576p112 1000001392640000 81920000000000000000000 55799840378907751 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3846377043524 16000000 17 7692754087048 4194304000000 162819913 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p833 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p835 := BSN.arctan_dyadic_bound_f 1000 1961218 1 0 33554432 10240000 0 1 1 0 1 1 17108 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1961218) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1961218) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p836 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1961218))) 884279719003555 562949953421312 1 2000000000000000 17108 33554432 1 10240000 29661872752480762200064 883992694392227 562949953421312 195312501 2000000000000000 qz17 (Ns576p835 rfl) rfl rfl 

noncomputable abbrev qz456 := (@HMul.hMul Real Real Real qz590 qz595 qz656)

noncomputable abbrev qz123 := qz456

noncomputable abbrev qz457 := qz656

noncomputable abbrev qz124 := qz457

noncomputable def Ns576p837 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 980609 4000) qz455) qz123 54717825674120350800359 18014398509481984000 47881365509537 16000000000000000000 883992694392227 2251799813685248 195312501 8000000000000000 Ns576p828 54710753732565212984359 18014398509481984000 48271990511537 16000000000000000000 (Ns576p834 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz124 1 4 0 1 883992694392227 562949953421312 195312501 2000000000000000 883992694392227 2251799813685248 195312501 8000000000000000 qz369 Ns576p836 rfl) 

noncomputable def Ns576p838 := @Ns576p823 Ns576p817 Ns576p818 139207953586548263 16384000000000000000000 (@Ns576p825 139207953586548263 16384000000000000000000 (Ns576p827 (Ns576p837 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 980609 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz657 (Real.log Real.pi) 980609 2000 0 1 38410761 33554432 3 268435456 37665937933449 67108864000 2941827 536870912000 (Enclosure.Real.IsNear.const Bool.false 980609 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p819 Ns576p820) 

noncomputable def Ns576p839 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns576p817 Ns576p818 139207953586548263 16384000000000000000000 8327732047 4194304 143 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz370 qz120 (Enclosure.sfrac Bool.true Ns576p819 Ns576p820)) Bool.false Ns576p817 Ns576p818 139207953586548263 16384000000000000000000 Ns576p821 (Ns576p838 rfl rfl)) 

noncomputable def Ns576p840 := nat_lit 14361484182743041198934716216492808156707494045915083579056879930278622094153341693761534659492394335156965897541171544398704776646824951540625 

noncomputable def Ns576p841 := nat_lit 10210493324212063962096517428463092809830271899371367889080039054936952654363300139502087974669083065455140279953535927117743828369140625 

noncomputable def Ns576p842 := nat_lit 71718308176988000623345647979969225770360258778603768761923452226217426739194112030113147204941686751672854666810428815703295283771387281140625 

noncomputable def Ns576p843 := BSN.sin_dyadic_bound_f 215817783115 137438953472 4 3 67108864 20500001 Ns576p840 Ns576p274 Ns576p841 Ns576p842 Ns576p277 Ns576p841 67108855 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215817783115) qz371 0 3 Ns576p840 Ns576p274 Ns576p841 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215817783115) qz372 0 3 Ns576p842 Ns576p277 Ns576p841 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p844 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz116) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8327732047) qz640) Bool.false 8327732047 4194304 143 16777216 Bool.false 67108855 67108864 1 10240000 (Ns576p839 rfl) (Enclosure.sfrac_false_div 8327732047 4194304) (BSN.cos_reduce3 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 8327732047) qz640) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 949176648063352070733824) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 67108855 67108864 315 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q3 8327732047 4194304 226375608064910080 72057594037927936 315 949176648063352070733824 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108855 67108864 949176648063352070733824 604462909807314587353088 215817783115 137438953472 20500001 20480000 (Ns576p843 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p845 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz116) Bool.false Ns576p817 Ns576p818 139207953586548263 16384000000000000000000 1065949702023 536870912 4563 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz116) (@HAdd.hAdd Real Real Real qz370 qz120 (Enclosure.sfrac Bool.true Ns576p819 Ns576p820)) Bool.false Ns576p817 Ns576p818 139207953586548263 16384000000000000000000 Ns576p821 (Ns576p838 rfl rfl)) 

noncomputable def Ns576p846 := Ns576p816 77267 BSN.abs_quadSignPos (BSN.cos_quad_nat3 831 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 232532708 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 578 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 519282453 536870912) qz119 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) Bool.false 67108855 67108864 90399 10485760000 536870840 536870912 4629 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 67108855 67108864 90399 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz116) qz116) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz116)) Bool.false 67108855 67108864 1481097216 171798691840000 67108855 67108864 90399 10485760000 (Ns576p844 rfl rfl) rfl)) rfl) (Ns576p845 rfl) RS577to588.d7 

noncomputable def Ns576p847 := nat_lit 840418828070633861293979625236171802969397600537456709271987754419328705 

noncomputable def Ns576p848 := nat_lit 11190704121025875101844553620393566950443831483522573735088120370881 

noncomputable def Ns576p849 := nat_lit 2201078812378321309115019841579350275335264425680460916307253976046212801 

noncomputable def Ns576p850 := BSN.sin_dyadic_bound_f 240495623 536870912 3 2 536870912 268435456 Ns576p847 Ns576p151 Ns576p848 Ns576p849 Ns576p154 Ns576p848 232532708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 240495623) qz375 0 2 Ns576p847 Ns576p151 Ns576p848 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 240495623) qz376 0 2 Ns576p849 Ns576p154 Ns576p848 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p851 := nat_lit 360600788339630932355015940342016 

noncomputable def Ns576p852 := BSN.cos_dyadic_bound_f 137802364 536870912 2 1 536870912 268435456 Ns576p851 Ns576p318 Ns576p851 Ns576p851 Ns576p319 Ns576p851 519282453 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 137802364) qz377 0 1 Ns576p851 Ns576p318 Ns576p851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 137802364) qz378 0 1 Ns576p851 Ns576p319 Ns576p851 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p853 := nat_lit 7489391501908819445693402715631225563189758426027565756461208878000800000 

noncomputable def Ns576p854 := nat_lit 2877277507178096316197442646748749466719152508468267893206544100000000 

noncomputable def Ns576p855 := nat_lit 22462419950712102144447813261600179190635836973065760733597213545802400000 

noncomputable def Ns576p856 := BSN.cos_dyadic_bound_f 481252190 536870912 3 2 536870912 268435456 Ns576p853 Ns576p141 Ns576p854 Ns576p855 Ns576p144 Ns576p854 335235245 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 481252190) qz377 0 2 Ns576p853 Ns576p141 Ns576p854 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 481252190) qz378 0 2 Ns576p855 Ns576p144 Ns576p854 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p857 := nat_lit 652668877016933354399891340198545052951763949970305242353959877352634625 

noncomputable def Ns576p858 := nat_lit 6749230451079973389133148580678532529784971757799981962368047397121 

noncomputable def Ns576p859 := nat_lit 1709359941052190370138037770660392135344809740920334434765765368608733441 

noncomputable def Ns576p860 := BSN.sin_dyadic_bound_f 225765087 536870912 3 2 536870912 268435456 Ns576p857 Ns576p151 Ns576p858 Ns576p859 Ns576p154 Ns576p858 219169726 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 225765087) qz375 0 2 Ns576p857 Ns576p151 Ns576p858 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 225765087) qz376 0 2 Ns576p859 Ns576p154 Ns576p858 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p861 := Ns576p814 130838 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 398 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 335235245 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 259 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 219169726 536870912) qz119 rfl rfl (Ns576p846 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p850 rfl rfl) (Ns576p852 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p845 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p856 rfl rfl) (Ns576p860 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p862 := nat_lit 5159935551358414661687761685005221038891373810882871435776598980303274240 

noncomputable def Ns576p863 := nat_lit 421788741038500030083618520900660793610560927529669061161523417989376 

noncomputable def Ns576p864 := nat_lit 13513434024167499875800192840265549270097276215572472391411116767641354496 

noncomputable def Ns576p865 := BSN.sin_dyadic_bound_f 378561874 536870912 3 2 536870912 268435456 Ns576p862 Ns576p151 Ns576p863 Ns576p864 Ns576p154 Ns576p863 347962209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 378561874) qz375 0 2 Ns576p862 Ns576p151 Ns576p863 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 378561874) qz376 0 2 Ns576p864 Ns576p154 Ns576p863 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p866 := nat_lit 1110766430824090062187410000390625 

noncomputable def Ns576p867 := BSN.sin_dyadic_bound_f 182560025 536870912 2 1 536870912 268435456 Ns576p866 Ns576p300 Ns576p866 Ns576p866 Ns576p301 Ns576p866 179062064 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 182560025) qz375 0 1 Ns576p866 Ns576p300 Ns576p866 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 182560025) qz376 0 1 Ns576p866 Ns576p301 Ns576p866 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p868 := Ns576p812 176078 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 145 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 347962209 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 179062064 536870912) qz119 rfl rfl (Ns576p861 rfl rfl) (Ns576p845 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p865 rfl rfl) (Ns576p867 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p869 := nat_lit 216620241301699318235278635150625 

noncomputable def Ns576p870 := BSN.cos_dyadic_bound_f 121317865 536870912 2 1 536870912 268435456 Ns576p869 Ns576p318 Ns576p869 Ns576p869 Ns576p319 Ns576p869 523221912 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 121317865) qz377 0 1 Ns576p869 Ns576p318 Ns576p869 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 121317865) qz378 0 1 Ns576p869 Ns576p319 Ns576p869 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p871 := nat_lit 26054834375527167322290431464044580758503134436957217604713589915220640000 

noncomputable def Ns576p872 := nat_lit 10747209446900832053558474141432380568545541649917303107226960100000000 

noncomputable def Ns576p873 := nat_lit 68221451692038074973150130590554440037063897410311894283504844223511200000 

noncomputable def Ns576p874 := BSN.sin_dyadic_bound_f 567429570 536870912 3 2 536870912 268435456 Ns576p871 Ns576p151 Ns576p872 Ns576p873 Ns576p154 Ns576p872 467531665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 567429570) qz375 0 2 Ns576p871 Ns576p151 Ns576p872 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 567429570) qz376 0 2 Ns576p873 Ns576p154 Ns576p872 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p875 := Ns576p810 215604 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 34 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 523221912 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 467531665 536870912) qz119 rfl rfl (Ns576p868 rfl) (Ns576p845 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p870 rfl rfl) (Ns576p874 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p876 := nat_lit 5064803685356048789170440085714177337710320607022333933644111284806443585 

noncomputable def Ns576p877 := nat_lit 406380602870371820495423735709392609905022480594037967262492828197441 

noncomputable def Ns576p878 := nat_lit 13264304083527861464879874300345982582158612505804198526644723614675984961 

noncomputable def Ns576p879 := BSN.sin_dyadic_bound_f 376804969 536870912 3 2 536870912 268435456 Ns576p876 Ns576p151 Ns576p877 Ns576p878 Ns576p154 Ns576p877 346622413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 376804969) qz375 0 2 Ns576p876 Ns576p151 Ns576p877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 376804969) qz376 0 2 Ns576p878 Ns576p154 Ns576p877 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p880 := nat_lit 56097630862933595579317866091138733596481607409037111320471577626083633052028584454410675308334400215846105640625 

noncomputable def Ns576p881 := nat_lit 66956493945817800034890881217564739539560699627951956770539388190002730856000581983333305599598398681640625 

noncomputable def Ns576p882 := nat_lit 339667100006760193161836189493650466471784876181365169957363148309919660941752549480404391779601391372969587240625 

noncomputable def Ns576p883 := BSN.cos_dyadic_bound_f 798269235 536870912 4 3 536870912 268435456 Ns576p880 Ns576p162 Ns576p881 Ns576p882 Ns576p165 Ns576p881 44992787 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 798269235) qz377 0 3 Ns576p880 Ns576p162 Ns576p881 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 798269235) qz378 0 3 Ns576p882 Ns576p165 Ns576p881 rfl rfl rfl rfl) rfl rfl 

noncomputable abbrev qz658 := (BSN.cos_quad_nat0 232 rfl)

noncomputable def Ns576p884 := Ns576p808 251153 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 346622413 536870912) BSN.abs_quadSignPos qz658 (BSN.sfrac_eq_quadSignPos_mul Bool.false 44992787 536870912) qz119 rfl rfl (Ns576p875 rfl) (Ns576p845 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p879 rfl rfl) (Ns576p883 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p885 := nat_lit 632444322452417459057965455330545365002600566642932799191193659027513600 

noncomputable def Ns576p886 := nat_lit 6337432182392466567988118312050529306453951106658115061352564285696 

noncomputable def Ns576p887 := nat_lit 1656391536294702804967847068912256445578410082429698932362074536158454016 

noncomputable def Ns576p888 := BSN.sin_dyadic_bound_f 223995434 536870912 3 2 536870912 268435456 Ns576p885 Ns576p151 Ns576p886 Ns576p887 Ns576p154 Ns576p886 217553063 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 223995434) qz375 0 2 Ns576p885 Ns576p151 Ns576p886 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 223995434) qz376 0 2 Ns576p887 Ns576p154 Ns576p886 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p889 := Ns576p806 Bool.true 3036386 251153 Bool.true 223995434 28296951008113761 1 Bool.false 217553063 Bool.false Bool.false 59765775 267767 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 217553063 536870912) qz119 rfl (Ns576p884 rfl) (Ns576p845 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p888 rfl rfl) rfl 

noncomputable def Ns576p890 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) 59765775 536870912 267767 536870912 59765775 536870912 267767 536870912 64173012261273600 59765775 268435456 267767 268435456 (Ns576p889 rfl rfl rfl rfl) 

noncomputable def Ns576p891 := @Enclosure.Real.IsNear.mulLit_ff qz654 (Zeta.RiemannSiegel.correction qz118) 18986761 67108864 1 67108864 430966799983503 1125899906842624 6363624511881 703687441776640000 8182663630221575403783 75557863725914323419136 

noncomputable abbrev qz659 := (@HPow.hPow Real Real Real qz7 qz117 qz9)

noncomputable def Ns576p892 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz659 1 1 0 1 18986761 67108864 1 67108864 18986761 67108864 1 67108864 

noncomputable def Ns576p893 := @Enclosure.Real.IsNear.sqrt_image qz117 10473597410563 67108864000 980609 67108864000 419187058 419187098 33554432 (@Enclosure.Real.IsNear.of_eq qz117 (@HMul.hMul Real Real Real qz5 qz116 qz3) Bool.false 10473597410563 67108864000 980609 67108864000 (BSN.t_div_two_pi_mk qz116 980609 1000 qz119) (@Enclosure.Real.IsNear.mulLit_ff qz116 qz3 980609 1000 0 1 10680707 67108864 1 67108864 10473597410563 67108864000 980609 67108864000 (Enclosure.Real.IsNear.const Bool.false 980609 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz771 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 980609 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz660 := qz771

noncomputable abbrev qz458 := qz660

noncomputable abbrev qz125 := qz458

noncomputable def Ns576p894 := @Enclosure.Real.IsNear.sqrt_image qz125 209593539 16777216 5 8388608 118598413 118598419 33554432 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 838374156 67108864 40 67108864 209593539 16777216 5 8388608 (Ns576p893 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p895 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz125) 7412401 2097152 3 33554432 9493380 9493381 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz125) Bool.false 237196832 67108864 6 67108864 7412401 2097152 3 33554432 (Ns576p894 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p896 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 18986761 67108864 1 67108864 18986761 67108864 1 67108864 (Ns576p895 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz459 := (@HMul.hMul Real Real Real qz590 qz588 qz653)

noncomputable abbrev qz126 := (Real.cos qz459)

noncomputable abbrev qz661 := (@HMul.hMul Real Real Real qz743 qz770 qz770)

noncomputable abbrev qz460 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz661 qz653) qz605)

noncomputable abbrev qz127 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz460))

noncomputable def Ns576p897 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz118) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz126) qz127) Bool.false 430966799983503 

noncomputable def Ns576p898 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz126) qz127 67178583 67108864 261 

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.cos qz459))

noncomputable def Ns576p899 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz126) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz128)) Bool.true 67178583 67108864 261 67108864 (BSN.inv_eq_neg_inv_neg qz126) 

noncomputable def Ns576p900 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz128) Bool.false 67178583 67108864 261 67108864 67178583 67108864 

noncomputable def Ns576p901 := @Enclosure.Real.IsNear.recentre' qz126 Bool.true 67039217 67108864 2657828864 687194767360000 67039217 67108864 162221 41943040000 

noncomputable abbrev qz129 := qz459

noncomputable def Ns576p902 := @Enclosure.Real.IsNear.cos_image qz129 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 207771039) qz384) Bool.false 207771039 67108864 253 67108864 Bool.true 67039217 67108864 1 

noncomputable def Ns576p903 := nat_lit 134930377080726494278610147 

noncomputable def Ns576p904 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz118 884279719003555 140737488355328 1 500000000000000 8266947 16777216 5 8388608 7310293570177281996585 2361183241434822606848 Ns576p903 

noncomputable def Ns576p905 := @Enclosure.Real.IsNear.subLit_ff_p qz125 qz1 209593539 16777216 5 8388608 12 1 0 1 8266947 8266947 16777216 5 

noncomputable def Ns576p906 := @Ns576p905 8388608 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 838374156 67108864 40 67108864 209593539 16777216 5 8388608 (Ns576p893 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p907 := @Enclosure.Real.IsNear.recentre' qz129 Bool.false 7310293570177281996585 2361183241434822606848 Ns576p903 Ns576p202 207771039 67108864 253 67108864 (@Ns576p904 Ns576p202 RS577to588.d55 (Ns576p906 rfl rfl) rfl) 

noncomputable def Ns576p908 := nat_lit 14751152467655631608741888 

noncomputable def Ns576p909 := nat_lit 12780244696841390852119339909925846531212063017662468102882629934031771861150895535479449766062278101811907964020771818034181415833599519756001 

noncomputable def Ns576p910 := nat_lit 7200353460618130749980646129986106165220261507194847162503882348925217995390295079718076569601471543325372694487518934942914901014744801 

noncomputable def Ns576p911 := nat_lit 63830625988087200790207074587805315667656550586241998870999706974595287615083859034009255450018971703597617976939726700454631385327150145998561 

noncomputable def Ns576p912 := BSN.sin_dyadic_bound_f 209626484599 137438953472 4 3 67108864 20500001 Ns576p909 Ns576p274 Ns576p910 Ns576p911 Ns576p277 Ns576p910 67039217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 209626484599) qz371 0 3 Ns576p909 Ns576p274 Ns576p910 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 209626484599) qz372 0 3 Ns576p911 Ns576p277 Ns576p910 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p913 := @Ns576p902 10240000 (Ns576p907 rfl) (Enclosure.sfrac_false_div 207771039 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 207771039) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p908) qz386) 226375608064910080 72057594037927936 Bool.false 67039217 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 207771039 67108864 226375608064910080 72057594037927936 0 Ns576p908 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67039217 67108864 Ns576p908 Ns576p112 209626484599 137438953472 20500001 20480000 (Ns576p912 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p914 := @Enclosure.Real.IsNear.inv_image qz128 67039217 67108864 162221 41943040000 33589161 33589422 33554432 (@Enclosure.Real.IsNear.neg qz126 Bool.true 67039217 67108864 162221 41943040000 (Ns576p901 (Ns576p913 rfl rfl) rfl)) 

noncomputable def Ns576p915 := Ns576p899 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz128) Bool.false 67178583 67108864 261 67108864 (@Ns576p900 261 67108864 (Ns576p914 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p916 := @Enclosure.Real.IsNear.recentre' qz127 Bool.true 12830482 33554432 

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz355 qz352 qz460)

noncomputable def Ns576p917 := @Enclosure.Real.IsNear.cos_image qz130 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 131745773)) qz384) Bool.true 131745773 67108864 

noncomputable def Ns576p918 := nat_lit 77768978083193489700287330245 

noncomputable def Ns576p919 := nat_lit 280917623861018885269888204529579 

noncomputable def Ns576p920 := @Enclosure.Real.IsNear.recentre' qz130 Bool.true Ns576p918 Ns576p524 Ns576p919 

noncomputable def Ns576p921 := nat_lit 37778931862957161709568000000000000000 

noncomputable abbrev qz131 := qz460

noncomputable def Ns576p922 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz131 884279719003555 140737488355328 1 500000000000000 87946128823159 

noncomputable abbrev qz461 := (@HSub.hSub Real Real Real qz594 qz661 qz653)

noncomputable abbrev qz132 := qz461

noncomputable def Ns576p923 := @Enclosure.Real.IsNear.subLit_tf qz132 qz31 70353942778743 281474976710656 10409725 8796093022208 1 16 

noncomputable abbrev qz462 := qz661

noncomputable abbrev qz133 := qz462

noncomputable def Ns576p924 := @Enclosure.Real.IsNear.subLit_ff_n qz133 qz118 68342412700809 281474976710656 5166845 8796093022208 8266947 16777216 5 8388608 

noncomputable def Ns576p925 := @Enclosure.Real.IsNear.mulLit_ff qz118 qz118 8266947 16777216 5 8388608 8266947 16777216 5 8388608 68342412700809 281474976710656 

noncomputable def Ns576p926 := nat_lit 2495394468040884815500492574784332196302376929289873878405797648068971800008606530224139002825747057201 

noncomputable def Ns576p927 := nat_lit 27342629628353289404290943142742660747744093550761726976611942887838116630796306018691259504118321 

noncomputable def Ns576p928 := nat_lit 15050139828774293019365388985520449451218858953229350078345443127457054143855435280518982665039990606385 

noncomputable def Ns576p929 := BSN.cos_dyadic_bound_t 131745773 67108864 4 3 33554432 10240000 Ns576p926 Ns576p227 Ns576p927 Ns576p928 Ns576p230 Ns576p927 12830482 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 131745773) qz606 0 3 Ns576p926 Ns576p227 Ns576p927 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 131745773) (BSN.cosOddQ 67108864) 0 3 Ns576p928 Ns576p230 Ns576p927 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p930 := @Ns576p916 1296777216 171798691840000 6415241 16777216 79149 10485760000 (@Ns576p917 125 16777216 Bool.true 12830482 33554432 1 10240000 (@Ns576p920 Ns576p921 131745773 67108864 125 16777216 (@Ns576p922 281474976710656 10409725 8796093022208 Ns576p918 Ns576p524 Ns576p919 Ns576p921 RS577to588.d55 (@Ns576p923 0 1 1407138061170544 87946128823159 281474976710656 10409725 8796093022208 (@Ns576p924 1180343294450611519488 70353942778743 281474976710656 10409725 8796093022208 (@Ns576p925 5166845 8796093022208 (Ns576p906 rfl rfl) (Ns576p906 rfl rfl) rfl) (Ns576p906 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 131745773 67108864) (BSN.cos_neg_of_bound 131745773 67108864 Bool.true 12830482 33554432 1 10240000 (Ns576p929 rfl rfl)) rfl rfl) 

noncomputable def Ns576p931 := @Ns576p891 121093978314440408697 Ns576p803 (Ns576p892 qz33 (@Enclosure.Real.IsNear.of_eq qz659 (@Inv.inv Real Real.instInv (Real.sqrt qz125)) Bool.false 18986761 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz117 (BSN.t_div_two_pi_nonneg qz116 980609 1000 qz119)) Ns576p896) rfl) (@Ns576p897 1125899906842624 6363624511881 703687441776640000 (BSN.correction_mk qz118 (BSN.cos_two_pi_p_ne_zero_mk qz116 980609 1000 12 qz119 rfl rfl (@BSN.floor_sqrt_eq_dec qz116 980609 1000 12 qz119 rfl rfl rfl))) (@Ns576p898 67108864 6415241 16777216 79149 10485760000 430966799983503 1125899906842624 6363624511881 703687441776640000 Ns576p915 (Ns576p930 rfl) rfl)) 

noncomputable def Ns576p932 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (hardyZApproximantRS₀ qz116) Bool.false 8639906495997731194617 75557863725914323419136 47227162783865831128697 Ns576p803 (@Eq.refl Real (hardyZApproximantRS₀ qz116)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz116) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HMul.hMul Real Real Real qz5 qz654 (Zeta.RiemannSiegel.correction qz118))) Bool.false 8639906495997731194617 75557863725914323419136 47227162783865831128697 Ns576p803 (BSN.hardyZApproximantRS₀_eq qz116 12 (@BSN.floor_sqrt_eq_dec qz116 980609 1000 12 qz119 rfl rfl rfl)) (@Ns576p805 8639906495997731194617 75557863725914323419136 47227162783865831128697 Ns576p803 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz116) qz116 12)) Bool.false 59765775 268435456 267767 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz116) qz116 12) (Ns576p890 (Ns576p889 rfl rfl rfl rfl) rfl rfl)) (Ns576p931 rfl) rfl rfl)) 

theorem RS577to588.d64 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz116) Bool.false 8639906495997731194617 75557863725914323419136 47227162783865831128697 Ns576p803 := Ns576p932 

noncomputable def Ns576p933 := nat_lit 5902958103587056517120000 

noncomputable def Ns576p934 := nat_lit 2802406317608442922165744959488 

noncomputable abbrev qz772 := (Enclosure.sfrac Bool.false 981853 1000)

noncomputable abbrev qz662 := qz772

noncomputable abbrev qz463 := qz662

noncomputable abbrev qz134 := qz463

noncomputable abbrev qz773 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 981853 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz663 := qz773

noncomputable abbrev qz464 := qz663

noncomputable abbrev qz135 := qz464

noncomputable abbrev qz774 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 981853 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz664 := qz774

noncomputable abbrev qz465 := qz664

noncomputable abbrev qz136 := qz465

noncomputable abbrev qz665 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz135 qz9))

noncomputable def Ns576p935 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HMul.hMul Real Real Real qz5 qz665 (Zeta.RiemannSiegel.correction qz136)) 267661785 268435456 268099 268435456 1022265229934158182653 9444732965739290427392 15590742694314867187 Ns576p933 Ns576p934 

noncomputable def Ns576p936 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin BSN.quadSignPos 11 12 981853 1000 287 536870912 268435456 9007199254740992 Bool.false 1067636377900 4568 1334074092 54 154981288 8 

noncomputable def Ns576p937 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 9 10 11 981853 1000 173 232 536870912 268435456 9007199254740992 Bool.false 1067636377900 4568 

noncomputable def Ns576p938 := Ns576p937 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 292186772 215870 Bool.true 227950641 Bool.true 713069472 28296951008113761 1 Bool.false 221163045 Bool.true Bool.false 128971535 Bool.false Bool.true 323238292 

noncomputable def Ns576p939 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 981853 1000 33 107 536870912 268435456 9007199254740992 Bool.false 1067636377900 4568 

noncomputable def Ns576p940 := Ns576p939 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 220648521 176294 Bool.true 666748090 Bool.true 348208372 28296951008113761 1 Bool.false 508096929 Bool.true Bool.false 324303444 Bool.false Bool.true 292186772 

noncomputable def Ns576p941 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignNeg 5 6 7 981853 1000 146 49 536870912 268435456 9007199254740992 Bool.false 1067636377900 4568 

noncomputable def Ns576p942 := Ns576p941 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 175402407 130998 Bool.false 25265139 Bool.false 569625941 28296951008113761 1 Bool.false 536276533 Bool.true Bool.false 468607391 Bool.true Bool.true 220648521 

noncomputable def Ns576p943 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 981853 1000 399 259 536870912 268435456 9007199254740992 Bool.false 1067636377900 4568 

noncomputable def Ns576p944 := Ns576p943 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 246223833 77359 Bool.false 398752397 Bool.false 837549846 28296951008113761 1 Bool.false 363088225 Bool.false Bool.false 536839959 Bool.false Bool.false 175402407 

noncomputable def Ns576p945 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz134) qz134 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 1 2 3 981853 1000 832 579 536870912 268435456 9007199254740992 Bool.false 1067636377900 4568 

noncomputable def Ns576p946 := Ns576p945 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 536870856 4629 Bool.false 620926246 Bool.false 247436043 28296951008113761 1 Bool.false 216083105 Bool.false Bool.false 238768735 Bool.false Bool.true 246223833 

noncomputable def Ns576p947 := nat_lit 57773000856996136624065830724611895177717727939470405481439 

noncomputable def Ns576p948 := nat_lit 29051692412418541398842868681262240572196191736745164800 

noncomputable def Ns576p949 := nat_lit 437999767341384834634598235756640000 

noncomputable def Ns576p950 := nat_lit 2580308625647601896599325204674201523520 

noncomputable abbrev qz666 := (@Eq.refl Real qz772)

noncomputable abbrev qz466 := qz666

noncomputable abbrev qz137 := qz466

noncomputable def Ns576p951 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz134 981853 1000 3856142254436 16000000 1963706 4000 2000 Ns576p949 Ns576p950 qz137 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p952 := nat_lit 18487360274238763719701065831875806456869672940630529754060480 

noncomputable abbrev qz667 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1963706))))

noncomputable abbrev qz467 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 981853 4000) (Real.log (Enclosure.sfrac Bool.false 3856142254436 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz667))

noncomputable abbrev qz668 := (Enclosure.sfrac Bool.false 981853 2000)

noncomputable abbrev qz138 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz467 qz668) (@HMul.hMul Real Real Real qz355 qz668 (Real.log Real.pi)))

noncomputable def Ns576p953 := @Enclosure.Real.IsNear.addLit_ft_p qz138 (Enclosure.sfrac Bool.true Ns576p949 Ns576p950) 7164787060175526569199 3602879701896396800 139384045274732971 16384000000000000000000 Ns576p949 Ns576p950 0 1 Ns576p952 

noncomputable def Ns576p954 := nat_lit 2404103602051396143303811399680000 

noncomputable abbrev qz139 := (@HSub.hSub Real Real Real qz359 qz467 qz668)

noncomputable def Ns576p955 := @Enclosure.Real.IsNear.subLit_ff_p qz139 (@HMul.hMul Real Real Real qz5 qz668 (Real.log Real.pi)) 45947635173530274281643 18014398509481984000 48332732783629 16000000000000000000 37713720920133 67108864000 2945559 536870912000 Ns576p954 7164787060175526569199 3602879701896396800 

noncomputable def Ns576p956 := nat_lit 91895270347060548563286000 

noncomputable abbrev qz140 := qz467

noncomputable def Ns576p957 := @Enclosure.Real.IsNear.subLit_ff_p qz140 qz668 54791380783395481499819 18014398509481984000 48332732783629 16000000000000000000 981853 2000 0 1 Ns576p956 45947635173530274281643 18014398509481984000 48332732783629 16000000000000000000 

noncomputable def Ns576p958 := nat_lit 123379221039607422845397570640634970112 

noncomputable def Ns576p959 := nat_lit 119853767487175101046063104 

noncomputable def Ns576p960 := nat_lit 142384262925076557535047447809415579949426435350856667996334737516448490210449749165029005094491851848914269158712705373667248078236073581715410939568037315237904581941887472629081702400 

noncomputable def Ns576p961 := nat_lit 4374913478448909806778849375665216906599576889401472764354783594490605742637741072359722473760566038171604252964380039932096427008353752922984218923036241294147099648583077308336701440 

noncomputable def Ns576p962 := nat_lit 366822454042932932806461008645533040852422675937013719364405211138802793785993575264014605496711769281866277886525530659502881749653465467012533053616713527179337798682578780160 

noncomputable def Ns576p963 := BSN.log_dyadic_bound 1758990254436 5953294254436 8 7 Ns576p960 268435456 81920000 Ns576p961 Ns576p962 163500555 7712284508872 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1758990254436) (BSN.artanhQ 5953294254436) 0 7 Ns576p961 Ns576p960 Ns576p962 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz468 := (Real.log (Enclosure.sfrac Bool.false 3856142254436 16000000))

noncomputable def Ns576p964 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 981853 4000) qz468 981853 4000 0 1 55811259656760423 4503599627370496 48828193 4000000000000000 54798452727769191603819 18014398509481984000 47942107781629 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 981853 4000) (BSN.isNear_log_sfrac 3856142254436 16000000 55811259656760423 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3856142254436) qz362)) Bool.false Ns576p959 Ns576p112 1000001392640000 81920000000000000000000 55811259656760423 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3856142254436 16000000 17 7712284508872 4194304000000 163500555 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p963 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p965 := BSN.arctan_dyadic_bound_f 1000 1963706 1 0 33554432 10240000 0 1 1 0 1 1 17087 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1963706) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1963706) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p966 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1963706))) 884279719003555 562949953421312 1 2000000000000000 17087 33554432 1 10240000 29661884574429784047616 883993046713763 562949953421312 195312501 2000000000000000 qz17 (Ns576p965 rfl) rfl rfl 

noncomputable abbrev qz469 := (@HMul.hMul Real Real Real qz590 qz595 qz667)

noncomputable abbrev qz141 := qz469

noncomputable abbrev qz470 := qz667

noncomputable abbrev qz142 := qz470

noncomputable def Ns576p967 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 981853 4000) qz468) qz141 54798452727769191603819 18014398509481984000 47942107781629 16000000000000000000 883993046713763 2251799813685248 195312501 8000000000000000 Ns576p958 54791380783395481499819 18014398509481984000 48332732783629 16000000000000000000 (Ns576p964 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz142 1 4 0 1 883993046713763 562949953421312 195312501 2000000000000000 883993046713763 2251799813685248 195312501 8000000000000000 qz369 Ns576p966 rfl) 

noncomputable def Ns576p968 := @Ns576p953 Ns576p947 Ns576p948 139384045274732971 16384000000000000000000 (@Ns576p955 139384045274732971 16384000000000000000000 (Ns576p957 (Ns576p967 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 981853 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz668 (Real.log Real.pi) 981853 2000 0 1 38410761 33554432 3 268435456 37713720920133 67108864000 2945559 536870912000 (Enclosure.Real.IsNear.const Bool.false 981853 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p949 Ns576p950) 

noncomputable def Ns576p969 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns576p947 Ns576p948 139384045274732971 16384000000000000000000 133454547237 67108864 143 16777216 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz370 qz138 (Enclosure.sfrac Bool.true Ns576p949 Ns576p950)) Bool.false Ns576p947 Ns576p948 139384045274732971 16384000000000000000000 Ns576p951 (Ns576p968 rfl rfl)) 

noncomputable def Ns576p970 := nat_lit 15187658038574139377188864 

noncomputable def Ns576p971 := nat_lit 14364636646742303522276621767752536185910056311251767735907333208496348419664276966888014368758783303352926566013148843019337844816104000000000 

noncomputable def Ns576p972 := nat_lit 10217205178981979289692233403642713506711629432289452158374664601780443654377514456221158432238797235649103145992988525390625000000000000 

noncomputable def Ns576p973 := nat_lit 71734031440214514925030965090522095722692104576780322315126545937600251207059127214747235792384358400612662730562219126438229261580520000000000 

noncomputable def Ns576p974 := BSN.sin_dyadic_bound_f 215829601850 137438953472 4 3 67108864 20500001 Ns576p971 Ns576p274 Ns576p972 Ns576p973 Ns576p277 Ns576p972 67108857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215829601850) qz371 0 3 Ns576p971 Ns576p274 Ns576p972 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215829601850) qz372 0 3 Ns576p973 Ns576p277 Ns576p972 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p975 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz134) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 133454547237) qz384) Bool.false 133454547237 67108864 143 16777216 Bool.true 67108857 67108864 1 10240000 (Ns576p969 rfl) (Enclosure.sfrac_false_div 133454547237 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 133454547237) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p970) qz386) 226375608064910080 72057594037927936 Bool.false 67108857 67108864 316 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 133454547237 67108864 226375608064910080 72057594037927936 316 Ns576p970 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108857 67108864 Ns576p970 Ns576p112 215829601850 137438953472 20500001 20480000 (Ns576p974 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p976 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz134) Bool.false Ns576p947 Ns576p948 139384045274732971 16384000000000000000000 1067636377900 536870912 4568 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz134) (@HAdd.hAdd Real Real Real qz370 qz138 (Enclosure.sfrac Bool.true Ns576p949 Ns576p950)) Bool.false Ns576p947 Ns576p948 139384045274732971 16384000000000000000000 Ns576p951 (Ns576p968 rfl rfl)) 

noncomputable def Ns576p977 := Ns576p946 77359 BSN.abs_quadSignPos (BSN.cos_quad_nat0 832 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 216083105 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 579 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 238768735 536870912) qz137 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) Bool.true 67108857 67108864 90399 10485760000 536870856 536870912 4629 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 67108857 67108864 90399 10485760000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz134) qz134) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz134)) Bool.true 67108857 67108864 1481097216 171798691840000 67108857 67108864 90399 10485760000 (Ns576p975 rfl rfl) rfl)) rfl) (Ns576p976 rfl) RS577to588.d7 

noncomputable def Ns576p978 := nat_lit 20497795522741014719511738704522593084378604120607578337116327986811248886918154675792602469759096564867391492096 

noncomputable def Ns576p979 := nat_lit 3284582764992517059897608532718617216568356660009630436033433683973773477056507353005469608554044967817216 

noncomputable def Ns576p980 := nat_lit 124265074903097215111526810636943487729629974102827338084057808216309955817084796857429437965712642883765273825280 

noncomputable def Ns576p981 := BSN.cos_dyadic_bound_f 620926246 536870912 4 3 536870912 268435456 Ns576p978 Ns576p162 Ns576p979 Ns576p980 Ns576p165 Ns576p979 216083105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 620926246) qz377 0 3 Ns576p978 Ns576p162 Ns576p979 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 620926246) qz378 0 3 Ns576p980 Ns576p165 Ns576p979 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p982 := nat_lit 941715266600706900796266659428111808090614577742779791106864981127373665 

noncomputable def Ns576p983 := nat_lit 14050885490857338853417835243001805628511406238470751345602885493601 

noncomputable def Ns576p984 := nat_lit 2466374377758675733060650002959423208742496780382894309777705879233274721 

noncomputable def Ns576p985 := BSN.sin_dyadic_bound_f 247436043 536870912 3 2 536870912 268435456 Ns576p982 Ns576p151 Ns576p983 Ns576p984 Ns576p154 Ns576p983 238768735 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 247436043) qz375 0 2 Ns576p982 Ns576p151 Ns576p983 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 247436043) qz376 0 2 Ns576p984 Ns576p154 Ns576p983 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p986 := nat_lit 6352112981905950726948099236091669702809636077259030986974904102146061345 

noncomputable def Ns576p987 := nat_lit 639184822111023194267876672560017068181493820821307772398254009136161 

noncomputable def Ns576p988 := nat_lit 16635451510517881675882873818008323479724372069492322848540865951510606881 

noncomputable def Ns576p989 := BSN.sin_dyadic_bound_f 398752397 536870912 3 2 536870912 268435456 Ns576p986 Ns576p151 Ns576p987 Ns576p988 Ns576p154 Ns576p987 363088225 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 398752397) qz375 0 2 Ns576p986 Ns576p151 Ns576p987 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 398752397) qz376 0 2 Ns576p988 Ns576p154 Ns576p987 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p990 := nat_lit 176583799340877396146518279784555852881744387800335372493800659675457270057469144467753696744908039105104835055616 

noncomputable def Ns576p991 := nat_lit 119159303849308813336060040125488308981251338449139398681570650515036191574774702623090366869035076599484416 

noncomputable def Ns576p992 := nat_lit 881851510490601541835656323318900446571081585792281112942395606931860175628395002604284360625050286513782214168576 

noncomputable def Ns576p993 := BSN.sin_dyadic_bound_f 837549846 536870912 4 3 536870912 268435456 Ns576p990 Ns576p135 Ns576p991 Ns576p992 Ns576p138 Ns576p991 536839959 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 837549846) qz375 0 3 Ns576p990 Ns576p135 Ns576p991 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 837549846) qz376 0 3 Ns576p992 Ns576p138 Ns576p991 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p994 := Ns576p944 130998 BSN.abs_quadSignPos (BSN.cos_quad_nat3 399 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 363088225 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 259 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536839959 536870912) qz137 rfl rfl (Ns576p977 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p981 rfl rfl) (Ns576p985 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p976 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p989 rfl rfl) (Ns576p993 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p995 := nat_lit 407461676419278258312379441041 

noncomputable def Ns576p996 := BSN.cos_dyadic_bound_f 25265139 536870912 2 1 536870912 268435456 Ns576p995 Ns576p318 Ns576p995 Ns576p995 Ns576p319 Ns576p995 536276533 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 25265139) qz377 0 1 Ns576p995 Ns576p318 Ns576p995 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 25265139) qz378 0 1 Ns576p995 Ns576p319 Ns576p995 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p997 := nat_lit 26460758328996771930600891985973857145033560398807221454544477503665392225 

noncomputable def Ns576p998 := nat_lit 11084550140258551307428199232121939158355403772268227133588192824052321 

noncomputable def Ns576p999 := nat_lit 69284039685240650735171261926412857002164844676482860013209726864075180641 

noncomputable def Ns576p1000 := BSN.sin_dyadic_bound_f 569625941 536870912 3 2 536870912 268435456 Ns576p997 Ns576p151 Ns576p998 Ns576p999 Ns576p154 Ns576p998 468607391 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 569625941) qz375 0 2 Ns576p997 Ns576p151 Ns576p998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 569625941) qz376 0 2 Ns576p999 Ns576p154 Ns576p998 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1001 := Ns576p942 176294 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536276533 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 49 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 468607391 536870912) qz137 rfl rfl (Ns576p994 rfl rfl) (Ns576p976 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p996 rfl rfl) (Ns576p1000 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1002 := nat_lit 70834811018469128232496568005540841399108331956300743542043196115438327561384384192542462718197747509981350400000 

noncomputable def Ns576p1003 := nat_lit 7718650261746844689883914482040912885839904498322627112334735290339060213402898998906256014881000000000000 

noncomputable def Ns576p1004 := nat_lit 354001925650594702100401735922499835845908264972057455896731300552347656235913771541657109766234340872882752000000 

noncomputable def Ns576p1005 := BSN.sin_dyadic_bound_f 666748090 536870912 4 3 536870912 268435456 Ns576p1002 Ns576p135 Ns576p1003 Ns576p1004 Ns576p138 Ns576p1003 508096929 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 666748090) qz375 0 3 Ns576p1002 Ns576p135 Ns576p1003 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 666748090) qz376 0 3 Ns576p1004 Ns576p138 Ns576p1003 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1006 := nat_lit 3693546170705386437945872498220423259591189128558224522724452111046737920 

noncomputable def Ns576p1007 := nat_lit 216129311237211989997211443844702014822046451499942434107002873511936 

noncomputable def Ns576p1008 := nat_lit 9673223380581628041874432486334883781381497737683397652718344190946246656 

noncomputable def Ns576p1009 := BSN.sin_dyadic_bound_f 348208372 536870912 3 2 536870912 268435456 Ns576p1006 Ns576p151 Ns576p1007 Ns576p1008 Ns576p154 Ns576p1007 324303444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 348208372) qz375 0 2 Ns576p1006 Ns576p151 Ns576p1007 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 348208372) qz376 0 2 Ns576p1008 Ns576p154 Ns576p1007 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1010 := Ns576p940 215870 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 508096929 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 324303444 536870912) qz137 rfl rfl (Ns576p1001 rfl) (Ns576p976 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p1005 rfl rfl) (Ns576p1009 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1011 := nat_lit 678311566184418638248901068096198972794184021440361692427697481286385025 

noncomputable def Ns576p1012 := nat_lit 7289983448015641100571905657779694261191983108486217678278796737921 

noncomputable def Ns576p1013 := nat_lit 1776518489557418693899625680976122809241678126275914502482014285317242241 

noncomputable def Ns576p1014 := BSN.sin_dyadic_bound_f 227950641 536870912 3 2 536870912 268435456 Ns576p1011 Ns576p151 Ns576p1012 Ns576p1013 Ns576p154 Ns576p1012 221163045 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 227950641) qz375 0 2 Ns576p1011 Ns576p151 Ns576p1012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 227950641) qz376 0 2 Ns576p1013 Ns576p154 Ns576p1012 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1015 := nat_lit 35679277540842152375286284247139866391842573916849811219718552802494215824231050188481005618554418127836383543296 

noncomputable def Ns576p1016 := nat_lit 17281527447647597316513444441703829132291657718285823470864286849661627782283257208106305957919401931964416 

noncomputable def Ns576p1017 := nat_lit 216187381605333241639125417172325547653515675190057854074063739387278085765269354091388281475888389556012769607680 

noncomputable def Ns576p1018 := BSN.cos_dyadic_bound_f 713069472 536870912 4 3 536870912 268435456 Ns576p1015 Ns576p162 Ns576p1016 Ns576p1017 Ns576p165 Ns576p1016 128971535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 713069472) qz377 0 3 Ns576p1015 Ns576p162 Ns576p1016 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 713069472) qz378 0 3 Ns576p1017 Ns576p165 Ns576p1016 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1019 := Ns576p938 251464 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 221163045 536870912) BSN.abs_quadSignPos qz658 (BSN.sfrac_eq_quadSignPos_mul Bool.false 128971535 536870912) qz137 rfl rfl (Ns576p1010 rfl) (Ns576p976 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p1014 rfl rfl) (Ns576p1018 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1020 := nat_lit 1503318616960004199377541176027841 

noncomputable def Ns576p1021 := BSN.sin_dyadic_bound_f 196907727 536870912 2 1 536870912 268435456 Ns576p1020 Ns576p300 Ns576p1020 Ns576p1020 Ns576p301 Ns576p1020 192522664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 196907727) qz375 0 1 Ns576p1020 Ns576p300 Ns576p1020 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 196907727) qz376 0 1 Ns576p1020 Ns576p301 Ns576p1020 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1022 := Ns576p936 Bool.true 323238292 251464 Bool.true 196907727 28296951008113761 1 Bool.false 192522664 Bool.false Bool.true 267661785 268099 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 192522664 536870912) qz137 rfl (Ns576p1019 rfl) (Ns576p976 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p1021 rfl rfl) rfl 

noncomputable def Ns576p1023 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) 267661785 536870912 268099 536870912 267661785 536870912 268099 536870912 287399653240995840 267661785 268435456 268099 268435456 (Ns576p1022 rfl rfl rfl rfl) 

noncomputable def Ns576p1024 := @Enclosure.Real.IsNear.mulLit_ff qz665 (Zeta.RiemannSiegel.correction qz136) 2372593 8388608 1 33554432 430864134697421 1125899906842624 6542807189251 703687441776640000 1022265229934158182653 9444732965739290427392 

noncomputable abbrev qz669 := (@HPow.hPow Real Real Real qz7 qz135 qz9)

noncomputable def Ns576p1025 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz669 1 1 0 1 2372593 8388608 1 33554432 2372593 8388608 1 33554432 

noncomputable def Ns576p1026 := @Enclosure.Real.IsNear.sqrt_image qz135 10486884210071 67108864000 981853 67108864000 419452863 419452904 33554432 (@Enclosure.Real.IsNear.of_eq qz135 (@HMul.hMul Real Real Real qz5 qz134 qz3) Bool.false 10486884210071 67108864000 981853 67108864000 (BSN.t_div_two_pi_mk qz134 981853 1000 qz137) (@Enclosure.Real.IsNear.mulLit_ff qz134 qz3 981853 1000 0 1 10680707 67108864 1 67108864 10486884210071 67108864000 981853 67108864000 (Enclosure.Real.IsNear.const Bool.false 981853 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz775 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 981853 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz670 := qz775

noncomputable abbrev qz471 := qz670

noncomputable abbrev qz143 := qz471

noncomputable def Ns576p1027 := @Enclosure.Real.IsNear.sqrt_image qz143 838905767 67108864 41 67108864 118636008 118636015 33554432 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 838905767 67108864 41 67108864 838905767 67108864 41 67108864 (Ns576p1026 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p1028 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz143) 237272023 67108864 7 67108864 9490371 9490373 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz143) Bool.false 237272023 67108864 7 67108864 237272023 67108864 7 67108864 (Ns576p1027 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p1029 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 18980744 67108864 2 67108864 2372593 8388608 1 33554432 (Ns576p1028 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz472 := (@HMul.hMul Real Real Real qz590 qz588 qz664)

noncomputable abbrev qz144 := (Real.cos qz472)

noncomputable abbrev qz671 := (@HMul.hMul Real Real Real qz743 qz774 qz774)

noncomputable abbrev qz473 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz671 qz664) qz605)

noncomputable abbrev qz145 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz473))

noncomputable def Ns576p1030 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz136) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz144) qz145) Bool.false 430864134697421 

noncomputable def Ns576p1031 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz144) qz145 67109459 67108864 265 

noncomputable abbrev qz146 := (@Neg.neg Real Real.instNeg (Real.cos qz472))

noncomputable def Ns576p1032 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz144) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz146)) Bool.true 67109459 67108864 265 67108864 (BSN.inv_eq_neg_inv_neg qz144) 

noncomputable def Ns576p1033 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz146) Bool.false 67109459 67108864 265 67108864 67109459 67108864 

noncomputable def Ns576p1034 := @Enclosure.Real.IsNear.recentre' qz144 Bool.true 67108269 67108864 1354514432 343597383680000 67108269 67108864 82673 20971520000 

noncomputable abbrev qz147 := qz472

noncomputable def Ns576p1035 := @Enclosure.Real.IsNear.cos_image qz147 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 105555625) qz373) Bool.false 105555625 33554432 129 33554432 Bool.true 67108269 67108864 1 

noncomputable def Ns576p1036 := nat_lit 221285818411884500680487571 

noncomputable def Ns576p1037 := nat_lit 57646075230342348800000000000000 

noncomputable def Ns576p1038 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz136 884279719003555 140737488355328 1 500000000000000 33599399 67108864 41 67108864 29711267106408326863445 9444732965739290427392 Ns576p1036 

noncomputable def Ns576p1039 := @Enclosure.Real.IsNear.subLit_ff_p qz143 qz1 838905767 67108864 41 67108864 12 1 0 1 33599399 33599399 67108864 41 

noncomputable def Ns576p1040 := @Ns576p1039 67108864 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 838905767 67108864 41 67108864 838905767 67108864 41 67108864 (Ns576p1026 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p1041 := @Enclosure.Real.IsNear.recentre' qz147 Bool.false 29711267106408326863445 9444732965739290427392 Ns576p1036 Ns576p1037 105555625 33554432 129 33554432 (@Ns576p1038 Ns576p1037 RS577to588.d55 (Ns576p1040 rfl rfl) rfl) 

noncomputable def Ns576p1042 := BSN.cos_dyadic_bound_f 578633455 137438953472 1 0 67108864 20500001 0 1 1 0 1 1 67108269 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 578633455) qz443 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 578633455) qz444 0 0 rfl) rfl rfl 

noncomputable def Ns576p1043 := @Ns576p1035 10240000 (Ns576p1041 rfl) (Enclosure.sfrac_false_div 105555625 33554432) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 105555625) qz373) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 20358854794160247930880) qz374) 226375608064910080 72057594037927936 Bool.false 67108269 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 105555625 33554432 226375608064910080 72057594037927936 0 20358854794160247930880 Ns576p124 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108269 67108864 20358854794160247930880 Ns576p124 578633455 137438953472 20500001 20480000 (Ns576p1042 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1044 := @Enclosure.Real.IsNear.inv_image qz146 67108269 67108864 82673 20971520000 33554597 33554862 33554432 (@Enclosure.Real.IsNear.neg qz144 Bool.true 67108269 67108864 82673 20971520000 (Ns576p1034 (Ns576p1043 rfl rfl) rfl)) 

noncomputable def Ns576p1045 := Ns576p1032 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz146) Bool.false 67109459 67108864 265 67108864 (@Ns576p1033 265 67108864 (Ns576p1044 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1046 := @Enclosure.Real.IsNear.recentre' qz145 Bool.true 12840638 33554432 

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz355 qz352 qz473)

noncomputable def Ns576p1047 := @Enclosure.Real.IsNear.cos_image qz148 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 131767757)) qz384) Bool.true 131767757 67108864 

noncomputable def Ns576p1048 := nat_lit 1244511278520072180267040389005 

noncomputable def Ns576p1049 := nat_lit 148601949860202378834396165067295913 

noncomputable def Ns576p1050 := @Enclosure.Real.IsNear.recentre' qz148 Bool.true Ns576p1048 Ns576p660 Ns576p1049 

noncomputable def Ns576p1051 := nat_lit 19342813113834066795298816000000000000000 

noncomputable abbrev qz149 := qz473

noncomputable def Ns576p1052 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz149 884279719003555 140737488355328 1 500000000000000 1407372861522191 

noncomputable abbrev qz474 := (@HSub.hSub Real Real Real qz594 qz671 qz664)

noncomputable abbrev qz150 := qz474

noncomputable def Ns576p1053 := @Enclosure.Real.IsNear.subLit_tf qz150 qz31 1125897884811535 4503599627370496 5506615823 4503599627370496 1 16 

noncomputable abbrev qz475 := qz671

noncomputable abbrev qz151 := qz475

noncomputable def Ns576p1054 := @Enclosure.Real.IsNear.subLit_ff_n qz151 qz136 1128919613161201 4503599627370496 2755152399 4503599627370496 33599399 67108864 41 67108864 

noncomputable def Ns576p1055 := @Enclosure.Real.IsNear.mulLit_ff qz136 qz136 33599399 67108864 41 67108864 33599399 67108864 41 67108864 1128919613161201 4503599627370496 

noncomputable def Ns576p1056 := nat_lit 2497075126092210077313602488040722424280318167435202915273676226909604795170493739456181255054455765681 

noncomputable def Ns576p1057 := nat_lit 27397430841336570924112347507466936875407167593795937309166946461161779738896308210267441513921201 

noncomputable def Ns576p1058 := nat_lit 15060217401910160650110788038997551873912157175612389936591474502065694277584006949139872235359795706545 

noncomputable def Ns576p1059 := BSN.cos_dyadic_bound_t 131767757 67108864 4 3 33554432 10240000 Ns576p1056 Ns576p227 Ns576p1057 Ns576p1058 Ns576p230 Ns576p1057 12840638 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 131767757) qz606 0 3 Ns576p1056 Ns576p227 Ns576p1057 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 131767757) (BSN.cosOddQ 67108864) 0 3 Ns576p1058 Ns576p230 Ns576p1057 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1060 := @Ns576p1046 1337737216 171798691840000 6420319 16777216 81649 10485760000 (@Ns576p1047 129 16777216 Bool.true 12840638 33554432 1 10240000 (@Ns576p1050 Ns576p1051 131767757 67108864 129 16777216 (@Ns576p1052 4503599627370496 5506615823 4503599627370496 Ns576p1048 Ns576p660 Ns576p1049 Ns576p1051 RS577to588.d55 (@Ns576p1053 0 1 22517965784355056 1407372861522191 4503599627370496 5506615823 4503599627370496 (@Ns576p1054 75557728029704967946240 1125897884811535 4503599627370496 5506615823 4503599627370496 (@Ns576p1055 2755152399 4503599627370496 (Ns576p1040 rfl rfl) (Ns576p1040 rfl rfl) rfl) (Ns576p1040 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 131767757 67108864) (BSN.cos_neg_of_bound 131767757 67108864 Bool.true 12840638 33554432 1 10240000 (Ns576p1059 rfl rfl)) rfl rfl) 

noncomputable def Ns576p1061 := @Ns576p1024 15590742694314867187 Ns576p933 (Ns576p1025 qz33 (@Enclosure.Real.IsNear.of_eq qz669 (@Inv.inv Real Real.instInv (Real.sqrt qz143)) Bool.false 2372593 8388608 1 33554432 (BSN.rpow_neg_quarter_mk qz135 (BSN.t_div_two_pi_nonneg qz134 981853 1000 qz137)) Ns576p1029) rfl) (@Ns576p1030 1125899906842624 6542807189251 703687441776640000 (BSN.correction_mk qz136 (BSN.cos_two_pi_p_ne_zero_mk qz134 981853 1000 12 qz137 rfl rfl (@BSN.floor_sqrt_eq_dec qz134 981853 1000 12 qz137 rfl rfl rfl))) (@Ns576p1031 67108864 6420319 16777216 81649 10485760000 430864134697421 1125899906842624 6542807189251 703687441776640000 Ns576p1045 (Ns576p1060 rfl) rfl)) 

noncomputable def Ns576p1062 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (hardyZApproximantRS₀ qz134) Bool.true 10439777067335109867773 9444732965739290427392 5911150100596671347187 Ns576p933 (@Eq.refl Real (hardyZApproximantRS₀ qz134)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz134) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HMul.hMul Real Real Real qz5 qz665 (Zeta.RiemannSiegel.correction qz136))) Bool.true 10439777067335109867773 9444732965739290427392 5911150100596671347187 Ns576p933 (BSN.hardyZApproximantRS₀_eq qz134 12 (@BSN.floor_sqrt_eq_dec qz134 981853 1000 12 qz137 rfl rfl rfl)) (@Ns576p935 10439777067335109867773 9444732965739290427392 5911150100596671347187 Ns576p933 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz134) qz134 12)) Bool.true 267661785 268435456 268099 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz134) qz134 12) (Ns576p1023 (Ns576p1022 rfl rfl rfl rfl) rfl rfl)) (Ns576p1061 rfl) rfl rfl)) 

theorem RS577to588.d65 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz134) Bool.true 10439777067335109867773 9444732965739290427392 5911150100596671347187 Ns576p933 := Ns576p1062 

noncomputable def Ns576p1063 := nat_lit 23611832414348226068480000 

noncomputable def Ns576p1064 := nat_lit 7533190467868903363101583212544 

noncomputable abbrev qz776 := (Enclosure.sfrac Bool.false 983097 1000)

noncomputable abbrev qz672 := qz776

noncomputable abbrev qz476 := qz672

noncomputable abbrev qz152 := qz476

noncomputable abbrev qz777 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 983097 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz673 := qz777

noncomputable abbrev qz477 := qz673

noncomputable abbrev qz153 := qz477

noncomputable abbrev qz778 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 983097 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz674 := qz778

noncomputable abbrev qz478 := qz674

noncomputable abbrev qz154 := qz478

noncomputable abbrev qz675 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz153 qz9))

noncomputable def Ns576p1065 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HMul.hMul Real Real Real qz5 qz675 (Zeta.RiemannSiegel.correction qz154)) 213929421 134217728 268441 268435456 4089136060863536516053 37778931862957161709568 61285626760189543547 Ns576p1063 Ns576p1064 

noncomputable def Ns576p1066 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin BSN.quadSignPos 11 12 983097 1000 287 536870912 268435456 9007199254740992 Bool.false 1069323477268 4574 1334074092 54 154981288 8 

noncomputable def Ns576p1067 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 9 10 11 983097 1000 173 232 536870912 268435456 9007199254740992 Bool.false 1069323477268 4574 

noncomputable def Ns576p1068 := Ns576p1067 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 341208069 216146 Bool.true 78672822 Bool.true 627446217 28296951008113761 1 Bool.false 78391556 Bool.true Bool.false 210098766 Bool.false Bool.false 379765640 

noncomputable def Ns576p1069 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignPos 7 8 9 983097 1000 33 107 536870912 268435456 9007199254740992 Bool.false 1069323477268 4574 

noncomputable def Ns576p1070 := Ns576p1069 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 419038203 176520 Bool.true 368439966 Bool.true 128563683 28296951008113761 1 Bool.false 340192692 Bool.true Bool.false 127338450 Bool.false Bool.false 341208069 

noncomputable def Ns576p1071 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 5 6 7 983097 1000 146 50 536870912 268435456 9007199254740992 Bool.false 1069323477268 4574 

noncomputable def Ns576p1072 := Ns576p1071 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 743012957 131166 Bool.false 515706752 Bool.false 113800491 28296951008113761 1 Bool.false 307651642 Bool.true Bool.false 524854863 Bool.true Bool.false 419038203 

noncomputable def Ns576p1073 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 983097 1000 400 260 536870912 268435456 9007199254740992 Bool.false 1069323477268 4574 

noncomputable def Ns576p1074 := Ns576p1073 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 417408764 77459 Bool.false 316676095 Bool.false 606443240 28296951008113761 1 Bool.false 446151128 Bool.false Bool.false 229260996 Bool.false Bool.false 743012957 

noncomputable def Ns576p1075 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz152) qz152 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignPos 1 2 3 983097 1000 834 580 536870912 268435456 9007199254740992 Bool.false 1069323477268 4574 

noncomputable def Ns576p1076 := Ns576p1075 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 536870856 4637 Bool.false 158465505 Bool.false 357493212 28296951008113761 1 Bool.false 513653476 Bool.true Bool.false 422180047 Bool.false Bool.false 417408764 

noncomputable def Ns576p1077 := nat_lit 32391984467362189862235248542158712526566764436083379890543 

noncomputable def Ns576p1078 := nat_lit 16262912591151478372173625345418180638130655132123136000 

noncomputable def Ns576p1079 := nat_lit 440781517835118471245503850523360000 

noncomputable def Ns576p1080 := nat_lit 2599986240887434003169478346762197875520 

noncomputable abbrev qz676 := (@Eq.refl Real qz776)

noncomputable abbrev qz479 := qz676

noncomputable abbrev qz155 := qz479

noncomputable def Ns576p1081 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz152 983097 1000 3865919845636 16000000 1966194 4000 2000 Ns576p1079 Ns576p1080 qz155 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p1082 := nat_lit 93288915266003106803237515801417092076512281575920134084763840 

noncomputable abbrev qz677 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1966194))))

noncomputable abbrev qz480 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 983097 4000) (Real.log (Enclosure.sfrac Bool.false 3865919845636 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz677))

noncomputable abbrev qz678 := (Enclosure.sfrac Bool.false 983097 2000)

noncomputable abbrev qz156 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz480 qz678) (@HMul.hMul Real Real Real qz355 qz678 (Real.log Real.pi)))

noncomputable def Ns576p1083 := @Enclosure.Real.IsNear.addLit_ft_p qz156 (Enclosure.sfrac Bool.true Ns576p1079 Ns576p1080) 35880544958028473662767 18014398509481984000 139560136962917679 16384000000000000000000 Ns576p1079 Ns576p1080 0 1 Ns576p1082 

noncomputable def Ns576p1084 := nat_lit 2407902611834218547162212466688000 

noncomputable abbrev qz157 := (@HSub.hSub Real Real Real qz359 qz480 qz678)

noncomputable def Ns576p1085 := @Enclosure.Real.IsNear.subLit_ff_p qz157 (@HMul.hMul Real Real Real qz5 qz678 (Real.log Real.pi)) 46017071478500676566319 18014398509481984000 48393475055721 16000000000000000000 37761503906817 67108864000 2949291 536870912000 Ns576p1084 35880544958028473662767 18014398509481984000 

noncomputable def Ns576p1086 := nat_lit 92034142957001353132638000 

noncomputable abbrev qz158 := qz480

noncomputable def Ns576p1087 := @Enclosure.Real.IsNear.subLit_ff_p qz158 qz678 54872022044238781578543 18014398509481984000 48393475055721 16000000000000000000 983097 2000 0 1 Ns576p1086 46017071478500676566319 18014398509481984000 48393475055721 16000000000000000000 

noncomputable def Ns576p1088 := nat_lit 123560809015749709447681508811592433664 

noncomputable def Ns576p1089 := nat_lit 119878259178841449391194112 

noncomputable def Ns576p1090 := nat_lit 145693337540791954227122976817601638754397013373520476817401828954349238196925966523207984383176241565468837266262339107013327698206763673493127285649084997344248248292711955423454822400 

noncomputable def Ns576p1091 := nat_lit 4513660230333685230779614200034255618174912453573280118731478062839698136925422474396533548888430556012965461137236483214645299389781312137065876293431017989498684995030348018944573440 

noncomputable def Ns576p1092 := nat_lit 396423626948751649288982688924753884705421667870497517617644868634478611955897069476949559206109691926160076350207009776462462811172605424604386997184472881598880420479536988160 

noncomputable def Ns576p1093 := BSN.log_dyadic_bound 1768767845636 5963071845636 8 7 Ns576p1090 268435456 81920000 Ns576p1091 Ns576p1092 164180336 7731839691272 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1768767845636) (BSN.artanhQ 5963071845636) 0 7 Ns576p1091 Ns576p1090 Ns576p1092 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz481 := (Real.log (Enclosure.sfrac Bool.false 3865919845636 16000000))

noncomputable def Ns576p1094 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 983097 4000) qz481 983097 4000 0 1 55822664489430119 4503599627370496 48828193 4000000000000000 54879093991565281698543 18014398509481984000 48002850053721 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 983097 4000) (BSN.isNear_log_sfrac 3865919845636 16000000 55822664489430119 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3865919845636) qz362)) Bool.false Ns576p1089 Ns576p112 1000001392640000 81920000000000000000000 55822664489430119 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3865919845636 16000000 17 7731839691272 4194304000000 164180336 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p1093 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1095 := BSN.arctan_dyadic_bound_f 1000 1966194 1 0 33554432 10240000 0 1 1 0 1 1 17065 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1966194) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1966194) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p1096 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1966194))) 884279719003555 562949953421312 1 2000000000000000 17065 33554432 1 10240000 29661896959328759316480 883993415812515 562949953421312 195312501 2000000000000000 qz17 (Ns576p1095 rfl) rfl rfl 

noncomputable abbrev qz482 := (@HMul.hMul Real Real Real qz590 qz595 qz677)

noncomputable abbrev qz159 := qz482

noncomputable abbrev qz483 := qz677

noncomputable abbrev qz160 := qz483

noncomputable def Ns576p1097 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 983097 4000) qz481) qz159 54879093991565281698543 18014398509481984000 48002850053721 16000000000000000000 883993415812515 2251799813685248 195312501 8000000000000000 Ns576p1088 54872022044238781578543 18014398509481984000 48393475055721 16000000000000000000 (Ns576p1094 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz160 1 4 0 1 883993415812515 562949953421312 195312501 2000000000000000 883993415812515 2251799813685248 195312501 8000000000000000 qz369 Ns576p1096 rfl) 

noncomputable def Ns576p1098 := @Ns576p1083 Ns576p1077 Ns576p1078 139560136962917679 16384000000000000000000 (@Ns576p1085 139560136962917679 16384000000000000000000 (Ns576p1087 (Ns576p1097 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 983097 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz678 (Real.log Real.pi) 983097 2000 0 1 38410761 33554432 3 268435456 37761503906817 67108864000 2949291 536870912000 (Enclosure.Real.IsNear.const Bool.false 983097 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p1079 Ns576p1080) 

noncomputable def Ns576p1099 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns576p1077 Ns576p1078 139560136962917679 16384000000000000000000 66832717329 33554432 573 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz370 qz156 (Enclosure.sfrac Bool.true Ns576p1079 Ns576p1080)) Bool.false Ns576p1077 Ns576p1078 139560136962917679 16384000000000000000000 Ns576p1081 (Ns576p1098 rfl rfl)) 

noncomputable def Ns576p1100 := BSN.cos_dyadic_bound_f 61230241 137438953472 1 0 67108864 20500001 0 1 1 0 1 1 67108857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 61230241) qz443 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 61230241) qz444 0 0 rfl) rfl rfl 

noncomputable def Ns576p1101 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz152) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66832717329) qz373) Bool.false 66832717329 33554432 573 67108864 Bool.false 67108857 67108864 1 10240000 (Ns576p1099 rfl) (Enclosure.sfrac_false_div 66832717329 33554432) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66832717329) qz373) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 2154347592637699063808) qz374) 226375608064910080 72057594037927936 Bool.false 67108857 67108864 317 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q0 66832717329 33554432 226375608064910080 72057594037927936 317 2154347592637699063808 Ns576p124 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67108857 67108864 2154347592637699063808 Ns576p124 61230241 137438953472 20500001 20480000 (Ns576p1100 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1102 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz152) Bool.false Ns576p1077 Ns576p1078 139560136962917679 16384000000000000000000 1069323477268 536870912 4574 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz152) (@HAdd.hAdd Real Real Real qz370 qz156 (Enclosure.sfrac Bool.true Ns576p1079 Ns576p1080)) Bool.false Ns576p1077 Ns576p1078 139560136962917679 16384000000000000000000 Ns576p1081 (Ns576p1098 rfl rfl)) 

noncomputable def Ns576p1103 := Ns576p1076 77459 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 834 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 513653476 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 580 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 422180047 536870912) qz155 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) Bool.false 67108857 67108864 362221 41943040000 536870856 536870912 4637 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 67108857 67108864 362221 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz152) qz152) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz152)) Bool.false 67108857 67108864 5934628864 687194767360000 67108857 67108864 362221 41943040000 (Ns576p1101 rfl rfl) rfl)) rfl) (Ns576p1102 rfl) RS577to588.d7 

noncomputable def Ns576p1104 := nat_lit 88009529016879937594799748286281717638430291996720636531324497645690625 

noncomputable def Ns576p1105 := nat_lit 397628872694560031432843944948748938986829209011132501025312890625 

noncomputable def Ns576p1106 := nat_lit 264027791792894423664336379170955255417412902331743887328971442311290625 

noncomputable def Ns576p1107 := BSN.cos_dyadic_bound_f 158465505 536870912 3 2 536870912 268435456 Ns576p1104 Ns576p141 Ns576p1105 Ns576p1106 Ns576p144 Ns576p1105 513653476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 158465505) qz377 0 2 Ns576p1104 Ns576p141 Ns576p1105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 158465505) qz378 0 2 Ns576p1106 Ns576p144 Ns576p1105 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1108 := nat_lit 2279873755345365117150972375332615620105950308406826972548783995082571776 

noncomputable def Ns576p1109 := nat_lit 266773323573625058057015838234324939702066866423639810019291520106496 

noncomputable def Ns576p1110 := nat_lit 6839087719388948101336803094321378210438446791487633638026313402207502336 

noncomputable def Ns576p1111 := BSN.cos_dyadic_bound_f 357493212 536870912 3 2 536870912 268435456 Ns576p1108 Ns576p141 Ns576p1109 Ns576p1110 Ns576p144 Ns576p1109 422180047 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 357493212) qz377 0 2 Ns576p1108 Ns576p141 Ns576p1109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 357493212) qz378 0 2 Ns576p1110 Ns576p144 Ns576p1109 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1112 := nat_lit 1403722286043472183318606561985428911219062295105545293471322745681690625 

noncomputable def Ns576p1113 := nat_lit 101139836537160502634323623238076382373494782990962839783431812890625 

noncomputable def Ns576p1114 := nat_lit 4210964578457342228950551038709810580892439895750653954734401373419290625 

noncomputable def Ns576p1115 := BSN.cos_dyadic_bound_f 316676095 536870912 3 2 536870912 268435456 Ns576p1112 Ns576p141 Ns576p1113 Ns576p1114 Ns576p144 Ns576p1113 446151128 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 316676095) qz377 0 2 Ns576p1112 Ns576p141 Ns576p1113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 316676095) qz378 0 2 Ns576p1114 Ns576p144 Ns576p1113 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1116 := nat_lit 18649452458130037464607717186560893898631820911527583911925897073283563964842506683681402009856995349233664000000 

noncomputable def Ns576p1117 := nat_lit 2474468400940610040150818049342821155077567909887845370289071952320070496520555338175113854976000000000000 

noncomputable def Ns576p1118 := nat_lit 113066973281814366763416444985372170822043427846566432902957562889742276593581397569593610102772496116324761600000 

noncomputable def Ns576p1119 := BSN.cos_dyadic_bound_f 606443240 536870912 4 3 536870912 268435456 Ns576p1116 Ns576p162 Ns576p1117 Ns576p1118 Ns576p165 Ns576p1117 229260996 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 606443240) qz377 0 3 Ns576p1116 Ns576p162 Ns576p1117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 606443240) qz378 0 3 Ns576p1118 Ns576p165 Ns576p1117 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1120 := Ns576p1074 131166 BSN.abs_quadSignPos (BSN.cos_quad_nat0 400 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 446151128 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 260 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 229260996 536870912) qz155 rfl rfl (Ns576p1103 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p1107 rfl rfl) (Ns576p1111 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p1102 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p1115 rfl rfl) (Ns576p1119 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p1121 := nat_lit 9748011657186674446911996055714980165766191834504598447914781582602406355020759112322347592103197410225161240576 

noncomputable def Ns576p1122 := nat_lit 353861904391077486649175087662212226926325237226218491203004822763007588061728467761002524935422105092096 

noncomputable def Ns576p1123 := nat_lit 59117965626804045576290886242327756431986387944219737811486937728058243111349964413299530616321239832759988387840 

noncomputable def Ns576p1124 := BSN.cos_dyadic_bound_f 515706752 536870912 4 3 536870912 268435456 Ns576p1121 Ns576p162 Ns576p1122 Ns576p1123 Ns576p165 Ns576p1122 307651642 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 515706752) qz377 0 3 Ns576p1121 Ns576p162 Ns576p1122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 515706752) qz378 0 3 Ns576p1123 Ns576p165 Ns576p1122 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1125 := nat_lit 167716790677114092036273079248561 

noncomputable def Ns576p1126 := BSN.cos_dyadic_bound_f 113800491 536870912 2 1 536870912 268435456 Ns576p1125 Ns576p318 Ns576p1125 Ns576p1125 Ns576p319 Ns576p1125 524854863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 113800491) qz377 0 1 Ns576p1125 Ns576p318 Ns576p1125 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 113800491) qz378 0 1 Ns576p1125 Ns576p319 Ns576p1125 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1127 := Ns576p1072 176520 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 146 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 307651642 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 524854863 536870912) qz155 rfl rfl (Ns576p1120 rfl rfl) (Ns576p1102 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p1124 rfl rfl) (Ns576p1126 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1128 := nat_lit 4629776996981872736413755482371530828669243979143115397915445240544723200 

noncomputable def Ns576p1129 := nat_lit 339573560582359528009387755295408090705395681370985544579342151024896 

noncomputable def Ns576p1130 := nat_lit 12125056634902057156133534873654959604844020733319273017944466218896425216 

noncomputable def Ns576p1131 := BSN.sin_dyadic_bound_f 368439966 536870912 3 2 536870912 268435456 Ns576p1128 Ns576p151 Ns576p1129 Ns576p1130 Ns576p154 Ns576p1129 340192692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 368439966) qz375 0 2 Ns576p1128 Ns576p151 Ns576p1129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 368439966) qz376 0 2 Ns576p1130 Ns576p154 Ns576p1129 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1132 := nat_lit 273195298493281142761336196711121 

noncomputable def Ns576p1133 := BSN.sin_dyadic_bound_f 128563683 536870912 2 1 536870912 268435456 Ns576p1132 Ns576p300 Ns576p1132 Ns576p1132 Ns576p301 Ns576p1132 127338450 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 128563683) qz375 0 1 Ns576p1132 Ns576p300 Ns576p1132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 128563683) qz376 0 1 Ns576p1132 Ns576p301 Ns576p1132 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1134 := Ns576p1070 216146 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 340192692 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 107 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 127338450 536870912) qz155 rfl rfl (Ns576p1127 rfl) (Ns576p1102 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p1131 rfl rfl) (Ns576p1133 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1135 := nat_lit 38308832312134039206078783491856 

noncomputable def Ns576p1136 := BSN.sin_dyadic_bound_f 78672822 536870912 2 1 536870912 268435456 Ns576p1135 Ns576p300 Ns576p1135 Ns576p1135 Ns576p301 Ns576p1135 78391556 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 78672822) qz375 0 1 Ns576p1135 Ns576p300 Ns576p1135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 78672822) qz376 0 1 Ns576p1135 Ns576p301 Ns576p1135 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1137 := nat_lit 21373361328828876898616786359660028328398063151301214083280039163355967740076129619865912190068288560038893430241 

noncomputable def Ns576p1138 := nat_lit 3723214543220872685701405223083692085656501555866943904329499855985166152206189774190856151596973874324961 

noncomputable def Ns576p1139 := nat_lit 129569151291411916332011719551562431834743648283022474090662373231702593852497209876708731586221450136912357336545 

noncomputable def Ns576p1140 := BSN.cos_dyadic_bound_f 627446217 536870912 4 3 536870912 268435456 Ns576p1137 Ns576p162 Ns576p1138 Ns576p1139 Ns576p165 Ns576p1138 210098766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 627446217) qz377 0 3 Ns576p1137 Ns576p162 Ns576p1138 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 627446217) qz378 0 3 Ns576p1139 Ns576p165 Ns576p1138 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1141 := Ns576p1068 251785 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 78391556 536870912) BSN.abs_quadSignPos qz658 (BSN.sfrac_eq_quadSignPos_mul Bool.false 210098766 536870912) qz155 rfl rfl (Ns576p1134 rfl) (Ns576p1102 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p1136 rfl rfl) (Ns576p1140 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1142 := nat_lit 823413606374981775457958472810000 

noncomputable def Ns576p1143 := BSN.sin_dyadic_bound_f 169396530 536870912 2 1 536870912 268435456 Ns576p1142 Ns576p300 Ns576p1142 Ns576p1142 Ns576p301 Ns576p1142 166599736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 169396530) qz375 0 1 Ns576p1142 Ns576p300 Ns576p1142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 169396530) qz376 0 1 Ns576p1142 Ns576p301 Ns576p1142 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1144 := Ns576p1066 Bool.false 379765640 251785 Bool.true 169396530 28296951008113761 1 Bool.false 166599736 Bool.false Bool.false 427858842 268441 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 166599736 536870912) qz155 rfl (Ns576p1141 rfl) (Ns576p1102 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p1143 rfl rfl) rfl 

noncomputable def Ns576p1145 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) 427858842 536870912 268441 536870912 427858842 536870912 268441 536870912 459409933423607808 213929421 134217728 268441 268435456 (Ns576p1144 rfl rfl rfl rfl) 

noncomputable def Ns576p1146 := @Enclosure.Real.IsNear.mulLit_ff qz675 (Zeta.RiemannSiegel.correction qz154) 18974737 67108864 1 67108864 215504228641669 562949953421312 3222755255819 351843720888320000 4089136060863536516053 37778931862957161709568 

noncomputable abbrev qz679 := (@HPow.hPow Real Real Real qz7 qz153 qz9)

noncomputable def Ns576p1147 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz679 1 1 0 1 18974737 67108864 1 67108864 18974737 67108864 1 67108864 

noncomputable def Ns576p1148 := @Enclosure.Real.IsNear.sqrt_image qz153 10500171009579 67108864000 983097 67108864000 419718501 419718541 33554432 (@Enclosure.Real.IsNear.of_eq qz153 (@HMul.hMul Real Real Real qz5 qz152 qz3) Bool.false 10500171009579 67108864000 983097 67108864000 (BSN.t_div_two_pi_mk qz152 983097 1000 qz155) (@Enclosure.Real.IsNear.mulLit_ff qz152 qz3 983097 1000 0 1 10680707 67108864 1 67108864 10500171009579 67108864000 983097 67108864000 (Enclosure.Real.IsNear.const Bool.false 983097 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz779 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 983097 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz680 := qz779

noncomputable abbrev qz484 := qz680

noncomputable abbrev qz161 := qz484

noncomputable def Ns576p1149 := @Enclosure.Real.IsNear.sqrt_image qz161 419718521 33554432 5 8388608 118673568 118673575 33554432 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 839437042 67108864 40 67108864 419718521 33554432 5 8388608 (Ns576p1148 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p1150 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz161) 237347143 67108864 7 67108864 9487368 9487369 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz161) Bool.false 237347143 67108864 7 67108864 237347143 67108864 7 67108864 (Ns576p1149 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p1151 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 18974737 67108864 1 67108864 18974737 67108864 1 67108864 (Ns576p1150 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz485 := (@HMul.hMul Real Real Real qz590 qz588 qz674)

noncomputable abbrev qz162 := (Real.cos qz485)

noncomputable abbrev qz681 := (@HMul.hMul Real Real Real qz743 qz778 qz778)

noncomputable abbrev qz486 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz681 qz674) qz605)

noncomputable abbrev qz163 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz486))

noncomputable def Ns576p1152 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz154) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz162) qz163) Bool.false 215504228641669 

noncomputable def Ns576p1153 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz162) qz163 16801663 16777216 65 

noncomputable abbrev qz164 := (@Neg.neg Real Real.instNeg (Real.cos qz485))

noncomputable def Ns576p1154 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz162) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz164)) Bool.true 16801663 16777216 65 16777216 (BSN.inv_eq_neg_inv_neg qz162) 

noncomputable def Ns576p1155 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz164) Bool.false 67206652 67108864 260 67108864 16801663 16777216 

noncomputable def Ns576p1156 := @Enclosure.Real.IsNear.recentre' qz162 Bool.true 67011218 67108864 661897216 171798691840000 33505609 33554432 40399 10485760000 

noncomputable abbrev qz165 := qz485

noncomputable def Ns576p1157 := @Enclosure.Real.IsNear.cos_image qz165 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 214449349) qz384) Bool.false 214449349 67108864 63 16777216 Bool.true 67011218 67108864 1 

noncomputable def Ns576p1158 := nat_lit 134930377081867759430954211 

noncomputable def Ns576p1159 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz154 884279719003555 140737488355328 1 500000000000000 17065337 33554432 5 8388608 15090531407060970273035 4722366482869645213696 Ns576p1158 

noncomputable def Ns576p1160 := @Enclosure.Real.IsNear.subLit_ff_p qz161 qz1 419718521 33554432 5 8388608 12 1 0 1 17065337 17065337 33554432 5 

noncomputable def Ns576p1161 := @Ns576p1160 8388608 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 839437042 67108864 40 67108864 419718521 33554432 5 8388608 (Ns576p1148 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p1162 := @Enclosure.Real.IsNear.recentre' qz165 Bool.false 15090531407060970273035 4722366482869645213696 Ns576p1158 Ns576p202 214449349 67108864 63 16777216 (@Ns576p1159 Ns576p202 RS577to588.d55 (Ns576p1161 rfl rfl) rfl) 

noncomputable def Ns576p1163 := nat_lit 3023143251084034474024215243446354356801 

noncomputable def Ns576p1164 := nat_lit 8563486156235759286349715816696970818296479744 

noncomputable def Ns576p1165 := nat_lit 128452292343536389295245737250454562274447196160 

noncomputable def Ns576p1166 := BSN.cos_dyadic_bound_f 7415060207 137438953472 2 1 67108864 20500001 Ns576p1163 Ns576p1164 Ns576p1163 Ns576p1163 Ns576p1165 Ns576p1163 67011218 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 7415060207) qz443 0 1 Ns576p1163 Ns576p1164 Ns576p1163 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 7415060207) qz444 0 1 Ns576p1163 Ns576p1165 Ns576p1163 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1167 := @Ns576p1157 10240000 (Ns576p1162 rfl) (Enclosure.sfrac_false_div 214449349 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 214449349) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 521788474789146906329088) qz386) 226375608064910080 72057594037927936 Bool.false 67011218 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 214449349 67108864 226375608064910080 72057594037927936 0 521788474789146906329088 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 67011218 67108864 521788474789146906329088 Ns576p112 7415060207 137438953472 20500001 20480000 (Ns576p1166 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1168 := @Enclosure.Real.IsNear.inv_image qz164 33505609 33554432 40399 10485760000 33603196 33603456 33554432 (@Enclosure.Real.IsNear.neg qz162 Bool.true 33505609 33554432 40399 10485760000 (Ns576p1156 (Ns576p1167 rfl rfl) rfl)) 

noncomputable def Ns576p1169 := Ns576p1154 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz164) Bool.false 16801663 16777216 65 16777216 (@Ns576p1155 65 16777216 (Ns576p1168 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1170 := @Enclosure.Real.IsNear.recentre' qz163 Bool.true 12826363 33554432 

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz355 qz352 qz486)

noncomputable def Ns576p1171 := @Enclosure.Real.IsNear.cos_image qz166 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 131736857)) qz384) Bool.true 131736857 67108864 

noncomputable def Ns576p1172 := nat_lit 311054859299569778506217648845 

noncomputable def Ns576p1173 := nat_lit 4566389786144319573793588148258601 

noncomputable def Ns576p1174 := @Enclosure.Real.IsNear.recentre' qz166 Bool.true Ns576p1172 Ns576p218 Ns576p1173 

noncomputable abbrev qz167 := qz486

noncomputable def Ns576p1175 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz167 884279719003555 140737488355328 1 500000000000000 351760707177679 

noncomputable abbrev qz487 := (@HSub.hSub Real Real Real qz594 qz681 qz674)

noncomputable abbrev qz168 := qz487

noncomputable def Ns576p1176 := @Enclosure.Real.IsNear.subLit_tf qz168 qz31 281391963000015 1125899906842624 169212815 140737488355328 1 16 

noncomputable abbrev qz488 := qz681

noncomputable abbrev qz169 := qz488

noncomputable def Ns576p1177 := @Enclosure.Real.IsNear.subLit_ff_n qz169 qz154 291225726923569 1125899906842624 85326735 140737488355328 17065337 33554432 5 8388608 

noncomputable def Ns576p1178 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz154 17065337 33554432 5 8388608 17065337 33554432 5 8388608 291225726923569 1125899906842624 

noncomputable def Ns576p1179 := nat_lit 2494713092779294522790643909896040524075953220486622485039708897000515575766722126354632626605919013281 

noncomputable def Ns576p1180 := nat_lit 27320432681088161142411882113289350660723361414894028661132201156295845757276026057262210243856801 

noncomputable def Ns576p1181 := nat_lit 15046054139661328495447719506661865701103723834941189896322994608147997684878061449469710232670087907745 

noncomputable def Ns576p1182 := BSN.cos_dyadic_bound_t 131736857 67108864 4 3 33554432 10240000 Ns576p1179 Ns576p227 Ns576p1180 Ns576p1181 Ns576p230 Ns576p1180 12826363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 131736857) qz606 0 3 Ns576p1179 Ns576p227 Ns576p1180 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 131736857) (BSN.cosOddQ 67108864) 0 3 Ns576p1181 Ns576p230 Ns576p1180 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1183 := @Ns576p1170 1317257216 171798691840000 12826363 33554432 80399 10485760000 (@Ns576p1171 127 16777216 Bool.true 12826363 33554432 1 10240000 (@Ns576p1174 Ns576p221 131736857 67108864 127 16777216 (@Ns576p1175 1125899906842624 169212815 140737488355328 Ns576p1172 Ns576p218 Ns576p1173 Ns576p221 RS577to588.d55 (@Ns576p1176 0 1 5628171314842864 351760707177679 1125899906842624 169212815 140737488355328 (@Ns576p1177 9441947487830519316480 281391963000015 1125899906842624 169212815 140737488355328 (@Ns576p1178 85326735 140737488355328 (Ns576p1161 rfl rfl) (Ns576p1161 rfl rfl) rfl) (Ns576p1161 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 131736857 67108864) (BSN.cos_neg_of_bound 131736857 67108864 Bool.true 12826363 33554432 1 10240000 (Ns576p1182 rfl rfl)) rfl rfl) 

noncomputable def Ns576p1184 := @Ns576p1146 61285626760189543547 Ns576p1063 (Ns576p1147 qz33 (@Enclosure.Real.IsNear.of_eq qz679 (@Inv.inv Real Real.instInv (Real.sqrt qz161)) Bool.false 18974737 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz153 (BSN.t_div_two_pi_nonneg qz152 983097 1000 qz155)) Ns576p1151) rfl) (@Ns576p1152 562949953421312 3222755255819 351843720888320000 (BSN.correction_mk qz154 (BSN.cos_two_pi_p_ne_zero_mk qz152 983097 1000 12 qz155 rfl rfl (@BSN.floor_sqrt_eq_dec qz152 983097 1000 12 qz155 rfl rfl rfl))) (@Ns576p1153 16777216 12826363 33554432 80399 10485760000 215504228641669 562949953421312 3222755255819 351843720888320000 Ns576p1169 (Ns576p1183 rfl) rfl)) 

noncomputable def Ns576p1185 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (hardyZApproximantRS₀ qz152) Bool.false 56126642732835586094123 37778931862957161709568 23673605696505566823547 Ns576p1063 (@Eq.refl Real (hardyZApproximantRS₀ qz152)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz152) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HMul.hMul Real Real Real qz5 qz675 (Zeta.RiemannSiegel.correction qz154))) Bool.false 56126642732835586094123 37778931862957161709568 23673605696505566823547 Ns576p1063 (BSN.hardyZApproximantRS₀_eq qz152 12 (@BSN.floor_sqrt_eq_dec qz152 983097 1000 12 qz155 rfl rfl rfl)) (@Ns576p1065 56126642732835586094123 37778931862957161709568 23673605696505566823547 Ns576p1063 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz152) qz152 12)) Bool.false 213929421 134217728 268441 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz152) qz152 12) (Ns576p1145 (Ns576p1144 rfl rfl rfl rfl) rfl rfl)) (Ns576p1184 rfl) rfl rfl)) 

theorem RS577to588.d66 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz152) Bool.false 56126642732835586094123 37778931862957161709568 23673605696505566823547 Ns576p1063 := Ns576p1185 

noncomputable def Ns576p1186 := nat_lit 420220519765187683090805293056 

noncomputable abbrev qz780 := (Enclosure.sfrac Bool.false 984340 1000)

noncomputable abbrev qz682 := qz780

noncomputable abbrev qz489 := qz682

noncomputable abbrev qz170 := qz489

noncomputable abbrev qz781 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 984340 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz683 := qz781

noncomputable abbrev qz490 := qz683

noncomputable abbrev qz171 := qz490

noncomputable abbrev qz782 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 984340 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz684 := qz782

noncomputable abbrev qz491 := qz684

noncomputable abbrev qz172 := qz491

noncomputable abbrev qz685 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz171 qz9))

noncomputable def Ns576p1187 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HMul.hMul Real Real Real qz5 qz685 (Zeta.RiemannSiegel.correction qz172)) 85351131 33554432 268775 268435456 511443598740438775215 4722366482869645213696 63651689328111980013 Ns576p1063 Ns576p1186 

noncomputable def Ns576p1188 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin BSN.quadSignPos 11 12 984340 1000 287 536870912 268435456 9007199254740992 Bool.false 1071009642033 4580 1334074092 54 154981288 8 

noncomputable def Ns576p1189 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 984340 1000 172 232 536870912 268435456 9007199254740992 Bool.false 1071009642033 4580 

noncomputable def Ns576p1190 := Ns576p1189 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 831828936 216414 Bool.true 772408272 Bool.true 541470206 28296951008113761 1 Bool.false 70700621 Bool.false Bool.false 286191822 Bool.false Bool.true 723181359 

noncomputable def Ns576p1191 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 7 8 9 984340 1000 33 106 536870912 268435456 9007199254740992 Bool.false 1071009642033 4580 

noncomputable def Ns576p1192 := Ns576p1191 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 776872363 176737 Bool.true 69950055 Bool.true 751988828 28296951008113761 1 Bool.false 69752310 Bool.true Bool.false 90886219 Bool.true Bool.true 831828936 

noncomputable def Ns576p1193 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.cos BSN.quadSignPos BSN.quadSignNeg 5 6 7 984340 1000 147 50 536870912 268435456 9007199254740992 Bool.false 1071009642033 4580 

noncomputable def Ns576p1194 := Ns576p1193 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 721673871 131326 Bool.false 162860849 Bool.false 501399998 28296951008113761 1 Bool.false 160374508 Bool.false Bool.false 319265742 Bool.true Bool.true 776872363 

noncomputable def Ns576p1195 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignNeg BSN.quadSignNeg 3 4 5 984340 1000 401 261 536870912 268435456 9007199254740992 Bool.false 1071009642033 4580 

noncomputable def Ns576p1196 := Ns576p1195 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 453669691 77551 Bool.false 234409452 Bool.false 375266091 28296951008113761 1 Bool.false 227032214 Bool.true Bool.false 345445832 Bool.true Bool.true 721673871 

noncomputable def Ns576p1197 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz170) qz170 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 1 2 3 984340 1000 835 581 536870912 268435456 9007199254740992 Bool.false 1071009642033 4580 

noncomputable def Ns576p1198 := Ns576p1197 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 536870864 4637 Bool.false 538757147 Bool.false 467205591 28296951008113761 1 Bool.false 452777641 Bool.false Bool.false 410428433 Bool.true Bool.true 453669691 

noncomputable def Ns576p1199 := nat_lit 28731411543705365473830546915568606081026926858119 

noncomputable def Ns576p1200 := nat_lit 14402353175116001373707925120070282914457190400 

noncomputable def Ns576p1201 := nat_lit 443575130836103581640292352000000000 

noncomputable def Ns576p1202 := nat_lit 2619772781166102754233711515566080000000 

noncomputable abbrev qz686 := (@Eq.refl Real qz780)

noncomputable abbrev qz492 := qz686

noncomputable abbrev qz173 := qz492

noncomputable def Ns576p1203 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz170 984340 1000 3875701942400 16000000 1968680 4000 2000 Ns576p1201 Ns576p1202 qz173 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p1204 := nat_lit 4707354467320687079232396806646760420315451696434216960000000 

noncomputable abbrev qz687 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1968680))))

noncomputable abbrev qz493 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 984340 4000) (Real.log (Enclosure.sfrac Bool.false 3875701942400 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz687))

noncomputable abbrev qz688 := (Enclosure.sfrac Bool.false 984340 2000)

noncomputable abbrev qz174 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz493 qz688) (@HMul.hMul Real Real Real qz355 qz688 (Real.log Real.pi)))

noncomputable def Ns576p1205 := @Enclosure.Real.IsNear.addLit_ft_p qz174 (Enclosure.sfrac Bool.true Ns576p1201 Ns576p1202) 1796856162755583309687 900719925474099200 6986804354914919 819200000000000000000 Ns576p1201 Ns576p1202 0 1 Ns576p1204 

noncomputable def Ns576p1206 := nat_lit 6029248792696315278522738278400 

noncomputable abbrev qz175 := (@HSub.hSub Real Real Real qz359 qz493 qz688)

noncomputable def Ns576p1207 := @Enclosure.Real.IsNear.subLit_ff_p qz175 (@HMul.hMul Real Real Real qz5 qz688 (Real.log Real.pi)) 2304323305629664311159 900719925474099200 2422708424981 800000000000000000 1890462424137 3355443200 147651 26843545600 Ns576p1206 1796856162755583309687 900719925474099200 

noncomputable def Ns576p1208 := nat_lit 4608646611259328622318000 

noncomputable abbrev qz176 := qz493

noncomputable def Ns576p1209 := @Enclosure.Real.IsNear.subLit_ff_p qz176 qz688 2747630631350251714423 900719925474099200 2422708424981 800000000000000000 984340 2000 0 1 Ns576p1208 2304323305629664311159 900719925474099200 2422708424981 800000000000000000 

noncomputable def Ns576p1210 := nat_lit 6187114143750377142912138089703931904 

noncomputable def Ns576p1211 := nat_lit 119902700214019189072986112 

noncomputable def Ns576p1212 := nat_lit 149075279612604569635727351806770894933851398876166323054786563901627458689159354259568803111715605038222471916983923049068511849725684417541855725762904064000000000000000000000000000000 

noncomputable def Ns576p1213 := nat_lit 4656441617288839467837434396554926376611522784673271376563957540548794816622748166732576377321781907133891483035123058547291939907709972623859805803931238400000000000000000000000000000 

noncomputable def Ns576p1214 := nat_lit 428245446631593266556279059442166130736705897654285659994740806860312580295307161363892856915859821043446002769285910827402416552005785514690582937600000000000000000000000000000 

noncomputable def Ns576p1215 := BSN.log_dyadic_bound 1778549942400 5972853942400 8 7 Ns576p1212 268435456 81920000 Ns576p1213 Ns576p1214 164858711 7751403884800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1778549942400) (BSN.artanhQ 5972853942400) 0 7 Ns576p1213 Ns576p1212 Ns576p1214 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz494 := (Real.log (Enclosure.sfrac Bool.false 3875701942400 16000000))

noncomputable def Ns576p1216 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 984340 4000) qz494 984340 4000 0 1 55834045733334119 4503599627370496 48828193 4000000000000000 2747984228857505334823 900719925474099200 2403177174881 800000000000000000 (Enclosure.Real.IsNear.const Bool.false 984340 4000) (BSN.isNear_log_sfrac 3875701942400 16000000 55834045733334119 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3875701942400) qz362)) Bool.false Ns576p1211 Ns576p112 1000001392640000 81920000000000000000000 55834045733334119 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3875701942400 16000000 17 7751403884800 4194304000000 164858711 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p1215 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1217 := BSN.arctan_dyadic_bound_f 1000 1968680 1 0 33554432 10240000 0 1 1 0 1 1 17044 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1968680) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1968680) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p1218 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1968680))) 884279719003555 562949953421312 1 2000000000000000 17044 33554432 1 10240000 29661908781277781164032 883993768134051 562949953421312 195312501 2000000000000000 qz17 (Ns576p1217 rfl) rfl rfl 

noncomputable abbrev qz495 := (@HMul.hMul Real Real Real qz590 qz595 qz687)

noncomputable abbrev qz177 := qz495

noncomputable abbrev qz496 := qz687

noncomputable abbrev qz178 := qz496

noncomputable def Ns576p1219 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 984340 4000) qz494) qz177 2747984228857505334823 900719925474099200 2403177174881 800000000000000000 883993768134051 2251799813685248 195312501 8000000000000000 Ns576p1210 2747630631350251714423 900719925474099200 2422708424981 800000000000000000 (Ns576p1216 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz178 1 4 0 1 883993768134051 562949953421312 195312501 2000000000000000 883993768134051 2251799813685248 195312501 8000000000000000 qz369 Ns576p1218 rfl) 

noncomputable def Ns576p1220 := @Ns576p1205 Ns576p1199 Ns576p1200 6986804354914919 819200000000000000000 (@Ns576p1207 6986804354914919 819200000000000000000 (Ns576p1209 (Ns576p1219 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 984340 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz688 (Real.log Real.pi) 984340 2000 0 1 38410761 33554432 3 268435456 1890462424137 3355443200 147651 26843545600 (Enclosure.Real.IsNear.const Bool.false 984340 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p1201 Ns576p1202) 

noncomputable def Ns576p1221 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns576p1199 Ns576p1200 6986804354914919 819200000000000000000 66938102627 33554432 573 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz370 qz174 (Enclosure.sfrac Bool.true Ns576p1201 Ns576p1202)) Bool.false Ns576p1199 Ns576p1200 6986804354914919 819200000000000000000 Ns576p1203 (Ns576p1220 rfl rfl)) 

noncomputable def Ns576p1222 := nat_lit 7593871442020078509359104 

noncomputable def Ns576p1223 := nat_lit 14364958284694954510891107825543453740632034652661345214110723495892930235100660811357385902846138968312833239934129315070601654224878856830976 

noncomputable def Ns576p1224 := nat_lit 10217890137579667425330769882003999336042544541968280773362010392249378794645409720191174938518868097430660875399382583783721269802827776 

noncomputable def Ns576p1225 := nat_lit 71735635644634671743680291161444108587345758668393213245393983198633125083846310392645623652355917310206938908114416315606569126776531148865536 

noncomputable def Ns576p1226 := BSN.sin_dyadic_bound_f 215830807576 137438953472 4 3 67108864 20500001 Ns576p1223 Ns576p274 Ns576p1224 Ns576p1225 Ns576p277 Ns576p1224 67108858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215830807576) qz371 0 3 Ns576p1223 Ns576p274 Ns576p1224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215830807576) qz372 0 3 Ns576p1225 Ns576p277 Ns576p1224 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1227 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz170) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66938102627) qz373) Bool.false 66938102627 33554432 573 67108864 Bool.true 67108858 67108864 1 10240000 (Ns576p1221 rfl) (Enclosure.sfrac_false_div 66938102627 33554432) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 66938102627) qz373) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p1222) qz374) 226375608064910080 72057594037927936 Bool.false 67108858 67108864 317 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 66938102627 33554432 226375608064910080 72057594037927936 317 Ns576p1222 Ns576p124 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108858 67108864 Ns576p1222 Ns576p124 215830807576 137438953472 20500001 20480000 (Ns576p1226 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1228 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz170) Bool.false Ns576p1199 Ns576p1200 6986804354914919 819200000000000000000 1071009642033 536870912 4580 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz170) (@HAdd.hAdd Real Real Real qz370 qz174 (Enclosure.sfrac Bool.true Ns576p1201 Ns576p1202)) Bool.false Ns576p1199 Ns576p1200 6986804354914919 819200000000000000000 Ns576p1203 (Ns576p1220 rfl rfl)) 

noncomputable def Ns576p1229 := Ns576p1198 77551 BSN.abs_quadSignPos (BSN.cos_quad_nat3 835 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 452777641 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 581 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 410428433 536870912) qz173 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) Bool.true 33554429 33554432 362221 41943040000 536870864 536870912 4637 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 33554429 33554432 362221 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz170) qz170) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz170)) Bool.true 67108858 67108864 5934628864 687194767360000 33554429 33554432 362221 41943040000 (Ns576p1227 rfl rfl) rfl)) rfl) (Ns576p1228 rfl) RS577to588.d7 

noncomputable def Ns576p1230 := nat_lit 21172838362845445624632211176090813919070383879710974145688760368842373345 

noncomputable def Ns576p1231 := nat_lit 7098136642688988503588512487263206750075110843865925496164633747880161 

noncomputable def Ns576p1232 := nat_lit 55441179681459432559316647869544181739017550457876768406952962987566790881 

noncomputable def Ns576p1233 := BSN.sin_dyadic_bound_f 538757147 536870912 3 2 536870912 268435456 Ns576p1230 Ns576p151 Ns576p1231 Ns576p1232 Ns576p154 Ns576p1231 452777641 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 538757147) qz375 0 2 Ns576p1230 Ns576p151 Ns576p1231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 538757147) qz376 0 2 Ns576p1232 Ns576p154 Ns576p1231 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1234 := nat_lit 11972249766587610293028778341752405551215349291626285640557605901818613825 

noncomputable def Ns576p1235 := nat_lit 2270200684752836826569113970959728968661523675522779004765540960915521 

noncomputable def Ns576p1236 := nat_lit 31352216682811284269737117091493794025329034249260854083071728390826315841 

noncomputable def Ns576p1237 := BSN.sin_dyadic_bound_f 467205591 536870912 3 2 536870912 268435456 Ns576p1234 Ns576p151 Ns576p1235 Ns576p1236 Ns576p154 Ns576p1235 410428433 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 467205591) qz375 0 2 Ns576p1234 Ns576p151 Ns576p1235 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 467205591) qz376 0 2 Ns576p1236 Ns576p154 Ns576p1235 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1238 := nat_lit 758519904318716449999926388032600960481927421221238937152894404546068480 

noncomputable def Ns576p1239 := nat_lit 9115929476155211493660972825671135565727565649346769877966541357056 

noncomputable def Ns576p1240 := nat_lit 1986584990282248355847865088986522857518893972854098273963492447029886976 

noncomputable def Ns576p1241 := BSN.sin_dyadic_bound_f 234409452 536870912 3 2 536870912 268435456 Ns576p1238 Ns576p151 Ns576p1239 Ns576p1240 Ns576p154 Ns576p1239 227032214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 234409452) qz375 0 2 Ns576p1238 Ns576p151 Ns576p1239 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 234409452) qz376 0 2 Ns576p1240 Ns576p154 Ns576p1239 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1242 := nat_lit 4982563694085520091051066038931703293858037472914777403374970523014665825 

noncomputable def Ns576p1243 := nat_lit 393291524237405382021158857895732394999706671676556524124777399719521 

noncomputable def Ns576p1244 := nat_lit 13048934822041882534515233940003582202893431951594083536371577920676959841 

noncomputable def Ns576p1245 := BSN.sin_dyadic_bound_f 375266091 536870912 3 2 536870912 268435456 Ns576p1242 Ns576p151 Ns576p1243 Ns576p1244 Ns576p154 Ns576p1243 345445832 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 375266091) qz375 0 2 Ns576p1242 Ns576p151 Ns576p1243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 375266091) qz376 0 2 Ns576p1244 Ns576p154 Ns576p1243 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1246 := Ns576p1196 131326 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 401 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 227032214 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 261 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 345445832 536870912) qz173 rfl rfl (Ns576p1229 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p1233 rfl rfl) (Ns576p1237 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p1228 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p1241 rfl rfl) (Ns576p1245 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p1247 := nat_lit 703504334873860253666131474641601 

noncomputable def Ns576p1248 := BSN.sin_dyadic_bound_f 162860849 536870912 2 1 536870912 268435456 Ns576p1247 Ns576p300 Ns576p1247 Ns576p1247 Ns576p301 Ns576p1247 160374508 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 162860849) qz375 0 1 Ns576p1247 Ns576p300 Ns576p1247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 162860849) qz376 0 1 Ns576p1247 Ns576p301 Ns576p1247 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1249 := nat_lit 8825162550648279358457998876164112130569874523089335574220323712041287936 

noncomputable def Ns576p1250 := nat_lit 3994612191374025899174521246061718750329273455719053264311806566400256 

noncomputable def Ns576p1251 := nat_lit 26467498427562090023575647586000212954208965022356568616132347522991063296 

noncomputable def Ns576p1252 := BSN.cos_dyadic_bound_f 501399998 536870912 3 2 536870912 268435456 Ns576p1249 Ns576p141 Ns576p1250 Ns576p1251 Ns576p144 Ns576p1250 319265742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 501399998) qz377 0 2 Ns576p1249 Ns576p141 Ns576p1250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 501399998) qz378 0 2 Ns576p1251 Ns576p144 Ns576p1250 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1253 := Ns576p1194 176737 BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 160374508 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 50 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 319265742 536870912) qz173 rfl rfl (Ns576p1246 rfl rfl) (Ns576p1228 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p1248 rfl rfl) (Ns576p1252 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1254 := nat_lit 23941548763510530541926734150625 

noncomputable def Ns576p1255 := BSN.sin_dyadic_bound_f 69950055 536870912 2 1 536870912 268435456 Ns576p1254 Ns576p300 Ns576p1254 Ns576p1254 Ns576p301 Ns576p1254 69752310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 69950055) qz375 0 1 Ns576p1254 Ns576p300 Ns576p1254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 69950055) qz376 0 1 Ns576p1254 Ns576p301 Ns576p1254 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1256 := nat_lit 44149368421107605420866306741402429387393469997066372360305324133386371916360152313256783134827425253488376938496 

noncomputable def Ns576p1257 := nat_lit 32699164943285123019546041907608693762294152903355839226178722065442233223908316258757997126151064430575616 

noncomputable def Ns576p1258 := nat_lit 267431161531545297979711944692706168407657563899409448184241951023678607799004033400277656659241010217680455598080 

noncomputable def Ns576p1259 := BSN.cos_dyadic_bound_f 751988828 536870912 4 3 536870912 268435456 Ns576p1256 Ns576p162 Ns576p1257 Ns576p1258 Ns576p165 Ns576p1257 90886219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 751988828) qz377 0 3 Ns576p1256 Ns576p162 Ns576p1257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 751988828) qz378 0 3 Ns576p1258 Ns576p165 Ns576p1257 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1260 := Ns576p1192 216414 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 33 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 69752310 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 90886219 536870912) qz173 rfl rfl (Ns576p1253 rfl) (Ns576p1228 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p1255 rfl rfl) (Ns576p1259 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1261 := nat_lit 49156275558194505651385479923460210439518274485696352701667346385741665712222724769194752790581526046654223876096 

noncomputable def Ns576p1262 := nat_lit 45098593099278797670249946423124717158207674609526901744316550784937117764143762099060232229640831254921216 

noncomputable def Ns576p1263 := nat_lit 297708766583292491332390042780798659399228358917829387254885392018757721520287423987756478071686354907553888993280 

noncomputable def Ns576p1264 := BSN.cos_dyadic_bound_f 772408272 536870912 4 3 536870912 268435456 Ns576p1261 Ns576p162 Ns576p1262 Ns576p1263 Ns576p165 Ns576p1262 70700621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 772408272) qz377 0 3 Ns576p1261 Ns576p162 Ns576p1262 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 772408272) qz378 0 3 Ns576p1263 Ns576p165 Ns576p1262 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1265 := nat_lit 11848146033779246740821550374907350717294639673145388154136966822397184383645206068285782978398074715577432150016 

noncomputable def Ns576p1266 := nat_lit 635177021754488863661252654369140711326312603386156097258848252066390558307820875626101563997020110196736 

noncomputable def Ns576p1267 := nat_lit 71849254187676078890892661755643134990097196804101888121619698071145279213041355206416403118291080705824075550720 

noncomputable def Ns576p1268 := BSN.cos_dyadic_bound_f 541470206 536870912 4 3 536870912 268435456 Ns576p1265 Ns576p162 Ns576p1266 Ns576p1267 Ns576p165 Ns576p1266 286191822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 541470206) qz377 0 3 Ns576p1265 Ns576p162 Ns576p1266 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 541470206) qz378 0 3 Ns576p1267 Ns576p165 Ns576p1266 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1269 := Ns576p1190 252098 BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 70700621 536870912) BSN.abs_quadSignPos qz658 (BSN.sfrac_eq_quadSignPos_mul Bool.false 286191822 536870912) qz173 rfl rfl (Ns576p1260 rfl) (Ns576p1228 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p1264 rfl rfl) (Ns576p1268 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1270 := nat_lit 400730287537450396187163909965041 

noncomputable def Ns576p1271 := BSN.sin_dyadic_bound_f 141485861 536870912 2 1 536870912 268435456 Ns576p1270 Ns576p300 Ns576p1270 Ns576p1270 Ns576p301 Ns576p1270 139853786 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 141485861) qz375 0 1 Ns576p1270 Ns576p300 Ns576p1270 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 141485861) qz376 0 1 Ns576p1270 Ns576p301 Ns576p1270 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1272 := Ns576p1188 Bool.true 723181359 252098 Bool.true 141485861 28296951008113761 1 Bool.false 139853786 Bool.false Bool.true 682809048 268775 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 139853786 536870912) qz173 rfl (Ns576p1269 rfl) (Ns576p1228 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p1271 rfl rfl) rfl 

noncomputable def Ns576p1273 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) 682809048 536870912 268775 536870912 682809048 536870912 268775 536870912 733160632643223552 85351131 33554432 268775 268435456 (Ns576p1272 rfl rfl rfl rfl) 

noncomputable def Ns576p1274 := @Enclosure.Real.IsNear.mulLit_ff qz685 (Zeta.RiemannSiegel.correction qz172) 2371093 8388608 1 33554432 215699510200755 562949953421312 6682789145931 703687441776640000 511443598740438775215 4722366482869645213696 

noncomputable abbrev qz689 := (@HPow.hPow Real Real Real qz7 qz171 qz9)

noncomputable def Ns576p1275 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz689 1 1 0 1 2371093 8388608 1 33554432 2371093 8388608 1 33554432 

noncomputable def Ns576p1276 := @Enclosure.Real.IsNear.sqrt_image qz171 525672356419 3355443200 49217 3355443200 419983757 419983798 33554432 (@Enclosure.Real.IsNear.of_eq qz171 (@HMul.hMul Real Real Real qz5 qz170 qz3) Bool.false 525672356419 3355443200 49217 3355443200 (BSN.t_div_two_pi_mk qz170 984340 1000 qz173) (@Enclosure.Real.IsNear.mulLit_ff qz170 qz3 984340 1000 0 1 10680707 67108864 1 67108864 525672356419 3355443200 49217 3355443200 (Enclosure.Real.IsNear.const Bool.false 984340 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz783 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 984340 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz690 := qz783

noncomputable abbrev qz497 := qz690

noncomputable abbrev qz179 := qz497

noncomputable def Ns576p1277 := @Enclosure.Real.IsNear.sqrt_image qz179 839967555 67108864 41 67108864 118711062 118711069 33554432 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 839967555 67108864 41 67108864 839967555 67108864 41 67108864 (Ns576p1276 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p1278 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz179) 237422131 67108864 7 67108864 9484371 9484373 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz179) Bool.false 237422131 67108864 7 67108864 237422131 67108864 7 67108864 (Ns576p1277 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p1279 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 18968744 67108864 2 67108864 2371093 8388608 1 33554432 (Ns576p1278 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz498 := (@HMul.hMul Real Real Real qz590 qz588 qz684)

noncomputable abbrev qz180 := (Real.cos qz498)

noncomputable abbrev qz691 := (@HMul.hMul Real Real Real qz743 qz782 qz782)

noncomputable abbrev qz499 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz691 qz684) qz605)

noncomputable abbrev qz181 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz499))

noncomputable def Ns576p1280 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz172) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz180) qz181) Bool.false 215699510200755 

noncomputable def Ns576p1281 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz180) qz181 33735387 33554432 135 

noncomputable abbrev qz182 := (@Neg.neg Real Real.instNeg (Real.cos qz498))

noncomputable def Ns576p1282 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz180) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz182)) Bool.true 33735387 33554432 135 33554432 (BSN.inv_eq_neg_inv_neg qz180) 

noncomputable def Ns576p1283 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz182) Bool.false 67470774 67108864 270 67108864 33735387 33554432 

noncomputable def Ns576p1284 := @Enclosure.Real.IsNear.recentre' qz180 Bool.true 66748895 67108864 2719268864 687194767360000 66748895 67108864 165971 41943040000 

noncomputable abbrev qz183 := qz498

noncomputable def Ns576p1285 := @Enclosure.Real.IsNear.cos_image qz183 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 54445665) qz629) Bool.false 54445665 16777216 259 67108864 Bool.true 66748895 67108864 1 

noncomputable def Ns576p1286 := nat_lit 1106429092068543192873008351 

noncomputable def Ns576p1287 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz172 884279719003555 140737488355328 1 500000000000000 34661187 67108864 41 67108864 30650184700689673519785 9444732965739290427392 Ns576p1286 

noncomputable def Ns576p1288 := @Enclosure.Real.IsNear.subLit_ff_p qz179 qz1 839967555 67108864 41 67108864 12 1 0 1 34661187 34661187 67108864 41 

noncomputable def Ns576p1289 := @Ns576p1288 67108864 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 839967555 67108864 41 67108864 839967555 67108864 41 67108864 (Ns576p1276 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p1290 := @Enclosure.Real.IsNear.recentre' qz183 Bool.false 30650184700689673519785 9444732965739290427392 Ns576p1286 Ns576p645 54445665 16777216 259 67108864 (@Ns576p1287 Ns576p645 RS577to588.d55 (Ns576p1289 rfl rfl) rfl) 

noncomputable def Ns576p1291 := nat_lit 41138175966401080788411129495609243650625 

noncomputable def Ns576p1292 := BSN.cos_dyadic_bound_f 14241681135 137438953472 2 1 67108864 20500001 Ns576p1291 Ns576p1164 Ns576p1291 Ns576p1291 Ns576p1165 Ns576p1291 66748895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 14241681135) qz443 0 1 Ns576p1291 Ns576p1164 Ns576p1291 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 14241681135) qz444 0 1 Ns576p1291 Ns576p1165 Ns576p1291 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1293 := @Ns576p1285 10240000 (Ns576p1290 rfl) (Enclosure.sfrac_false_div 54445665 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 54445665) qz629) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 250542304117366529720320) (@Nat.cast Real Real.instNatCast Ns576p513)) 226375608064910080 72057594037927936 Bool.false 66748895 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 54445665 16777216 226375608064910080 72057594037927936 0 250542304117366529720320 Ns576p513 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 66748895 67108864 250542304117366529720320 Ns576p513 14241681135 137438953472 20500001 20480000 (Ns576p1292 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1294 := @Enclosure.Real.IsNear.inv_image qz182 66748895 67108864 165971 41943040000 33735252 33735522 33554432 (@Enclosure.Real.IsNear.neg qz180 Bool.true 66748895 67108864 165971 41943040000 (Ns576p1284 (Ns576p1293 rfl rfl) rfl)) 

noncomputable def Ns576p1295 := Ns576p1282 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz182) Bool.false 33735387 33554432 135 33554432 (@Ns576p1283 135 33554432 (Ns576p1294 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1296 := @Enclosure.Real.IsNear.recentre' qz181 Bool.true 12787730 33554432 

noncomputable abbrev qz184 := (@HMul.hMul Real Real Real qz355 qz352 qz499)

noncomputable def Ns576p1297 := @Enclosure.Real.IsNear.cos_image qz184 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65826631)) qz373) Bool.true 65826631 33554432 

noncomputable def Ns576p1298 := nat_lit 1243429906470551279133307171525 

noncomputable def Ns576p1299 := nat_lit 150951536125178155168409482339407473 

noncomputable def Ns576p1300 := @Enclosure.Real.IsNear.recentre' qz184 Bool.true Ns576p1298 Ns576p660 Ns576p1299 

noncomputable abbrev qz185 := qz499

noncomputable def Ns576p1301 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz185 884279719003555 140737488355328 1 500000000000000 1406149976923255 

noncomputable abbrev qz500 := (@HSub.hSub Real Real Real qz594 qz691 qz684)

noncomputable abbrev qz186 := qz500

noncomputable def Ns576p1302 := @Enclosure.Real.IsNear.subLit_tf qz186 qz31 1124675000212599 4503599627370496 5593682439 4503599627370496 1 16 

noncomputable abbrev qz501 := qz691

noncomputable abbrev qz187 := qz501

noncomputable def Ns576p1303 := @Enclosure.Real.IsNear.subLit_ff_n qz187 qz172 1201397884248969 4503599627370496 2842219015 4503599627370496 34661187 67108864 41 67108864 

noncomputable def Ns576p1304 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz172 34661187 67108864 41 67108864 34661187 67108864 41 67108864 1201397884248969 4503599627370496 

noncomputable def Ns576p1305 := nat_lit 607502809769799338143331532032090798265820190932123064751877921683880794444411323788616818057009441 

noncomputable def Ns576p1306 := nat_lit 6619413970055775279187566220322471555450641567476343799593015305679038313438598064865915164961 

noncomputable def Ns576p1307 := nat_lit 3664010745627864497706137818811732695113894678282197203345078165358742361276599301335927881203439905 

noncomputable def Ns576p1308 := BSN.cos_dyadic_bound_t 65826631 33554432 4 3 33554432 10240000 Ns576p1305 Ns576p367 Ns576p1306 Ns576p1307 Ns576p370 Ns576p1306 12787730 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65826631) (BSN.cosEvenQ 33554432) 0 3 Ns576p1305 Ns576p367 Ns576p1306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65826631) (BSN.cosOddQ 33554432) 0 3 Ns576p1307 Ns576p370 Ns576p1306 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1309 := @Ns576p1296 5443108864 687194767360000 6393865 16777216 332221 41943040000 (@Ns576p1297 525 67108864 Bool.true 12787730 33554432 1 10240000 (@Ns576p1300 Ns576p1051 65826631 33554432 525 67108864 (@Ns576p1301 4503599627370496 5593682439 4503599627370496 Ns576p1298 Ns576p660 Ns576p1299 Ns576p1051 RS577to588.d55 (@Ns576p1302 0 1 22498399630772080 1406149976923255 4503599627370496 5593682439 4503599627370496 (@Ns576p1303 75475661633467277377536 1124675000212599 4503599627370496 5593682439 4503599627370496 (@Ns576p1304 2842219015 4503599627370496 (Ns576p1289 rfl rfl) (Ns576p1289 rfl rfl) rfl) (Ns576p1289 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65826631 33554432) (BSN.cos_neg_of_bound 65826631 33554432 Bool.true 12787730 33554432 1 10240000 (Ns576p1308 rfl rfl)) rfl rfl) 

noncomputable def Ns576p1310 := @Ns576p1274 63651689328111980013 Ns576p1063 (Ns576p1275 qz33 (@Enclosure.Real.IsNear.of_eq qz689 (@Inv.inv Real Real.instInv (Real.sqrt qz179)) Bool.false 2371093 8388608 1 33554432 (BSN.rpow_neg_quarter_mk qz171 (BSN.t_div_two_pi_nonneg qz170 984340 1000 qz173)) Ns576p1279) rfl) (@Ns576p1280 562949953421312 6682789145931 703687441776640000 (BSN.correction_mk qz172 (BSN.cos_two_pi_p_ne_zero_mk qz170 984340 1000 12 qz173 rfl rfl (@BSN.floor_sqrt_eq_dec qz170 984340 1000 12 qz173 rfl rfl rfl))) (@Ns576p1281 33554432 6393865 16777216 332221 41943040000 215699510200755 562949953421312 6682789145931 703687441776640000 Ns576p1295 (Ns576p1309 rfl) rfl)) 

noncomputable def Ns576p1311 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (hardyZApproximantRS₀ qz170) Bool.true 12523547403967013451183 4722366482869645213696 23705350709767663980013 Ns576p1063 (@Eq.refl Real (hardyZApproximantRS₀ qz170)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz170) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HMul.hMul Real Real Real qz5 qz685 (Zeta.RiemannSiegel.correction qz172))) Bool.true 12523547403967013451183 4722366482869645213696 23705350709767663980013 Ns576p1063 (BSN.hardyZApproximantRS₀_eq qz170 12 (@BSN.floor_sqrt_eq_dec qz170 984340 1000 12 qz173 rfl rfl rfl)) (@Ns576p1187 12523547403967013451183 4722366482869645213696 23705350709767663980013 Ns576p1063 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz170) qz170 12)) Bool.true 85351131 33554432 268775 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz170) qz170 12) (Ns576p1273 (Ns576p1272 rfl rfl rfl rfl) rfl rfl)) (Ns576p1310 rfl) rfl rfl)) 

theorem RS577to588.d67 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz170) Bool.true 12523547403967013451183 4722366482869645213696 23705350709767663980013 Ns576p1063 := Ns576p1311 

noncomputable def Ns576p1312 := nat_lit 877171565658521805920462176256 

noncomputable abbrev qz784 := (Enclosure.sfrac Bool.false 985816 1000)

noncomputable abbrev qz692 := qz784

noncomputable abbrev qz502 := qz692

noncomputable abbrev qz188 := qz502

noncomputable abbrev qz785 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 985816 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz693 := qz785

noncomputable abbrev qz503 := qz693

noncomputable abbrev qz189 := qz503

noncomputable abbrev qz786 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 985816 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz694 := qz786

noncomputable abbrev qz504 := qz694

noncomputable abbrev qz190 := qz504

noncomputable abbrev qz695 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz189 qz9))

noncomputable def Ns576p1313 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (@HMul.hMul Real Real Real qz5 qz695 (Zeta.RiemannSiegel.correction qz190)) 53715599 67108864 67295 67108864 2048722082986580138865 18889465931478580854784 3230207853890247321 1180591620717411303424000 Ns576p1312 

noncomputable def Ns576p1314 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin BSN.quadSignPos 11 12 985816 1000 287 536870912 268435456 9007199254740992 Bool.false 1073012425309 4587 1334074092 54 154981288 8 

noncomputable def Ns576p1315 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 985816 1000 172 232 536870912 268435456 9007199254740992 Bool.false 1073012425309 4587 

noncomputable def Ns576p1316 := Ns576p1315 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 2757255 216740 Bool.true 594242847 Bool.true 438830614 28296951008113761 1 Bool.false 240232893 Bool.false Bool.false 367289656 Bool.false Bool.false 183953052 

noncomputable def Ns576p1317 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 985816 1000 32 106 536870912 268435456 9007199254740992 Bool.false 1073012425309 4587 

noncomputable def Ns576p1318 := Ns576p1317 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 10499246 177004 Bool.true 558275749 Bool.true 490333452 28296951008113761 1 Bool.false 271835296 Bool.false Bool.false 328094384 Bool.true Bool.true 2757255 

noncomputable def Ns576p1319 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 985816 1000 147 51 536870912 268435456 9007199254740992 Bool.false 1073012425309 4587 

noncomputable def Ns576p1320 := Ns576p1319 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 249641858 131524 Bool.false 745815470 Bool.false 118887467 28296951008113761 1 Bool.false 528041943 Bool.false Bool.false 117918180 Bool.false Bool.false 10499246 

noncomputable def Ns576p1321 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 985816 1000 402 262 536870912 268435456 9007199254740992 Bool.false 1073012425309 4587 

noncomputable def Ns576p1322 := Ns576p1321 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 191803015 77669 Bool.false 295348482 Bool.false 259381384 28296951008113761 1 Bool.false 457659297 Bool.true Bool.false 475422099 Bool.true Bool.true 249641858 

noncomputable def Ns576p1323 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz188) qz188 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 985816 1000 837 582 536870912 268435456 9007199254740992 Bool.false 1073012425309 4587 

noncomputable def Ns576p1324 := Ns576p1323 372130544 53 379625064 8 589812976 53 309962568 8 Bool.false 446566928 4645 Bool.false 305646027 Bool.false 756110058 28296951008113761 1 Bool.false 289400847 Bool.true Bool.false 86821835 Bool.true Bool.false 191803015 

noncomputable def Ns576p1325 := nat_lit 9076590196136741510869395550042327056683797276331939633 

noncomputable def Ns576p1326 := nat_lit 4541380082383472697369444644127634189536693583872000 

noncomputable def Ns576p1327 := nat_lit 446910782844941957856305532436480000 

noncomputable def Ns576p1328 := nat_lit 2643431119145518574729471376705701806080 

noncomputable abbrev qz696 := (@Eq.refl Real qz784)

noncomputable abbrev qz505 := qz696

noncomputable abbrev qz191 := qz505

noncomputable def Ns576p1329 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz188 985816 1000 3887333743424 16000000 1971632 4000 2000 Ns576p1327 Ns576p1328 qz191 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p1330 := nat_lit 11896868301880349833126734135351478919736586766033799915765760 

noncomputable abbrev qz697 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1971632))))

noncomputable abbrev qz506 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 985816 4000) (Real.log (Enclosure.sfrac Bool.false 3887333743424 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz697))

noncomputable abbrev qz698 := (Enclosure.sfrac Bool.false 985816 2000)

noncomputable abbrev qz192 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz506 qz698) (@HMul.hMul Real Real Real qz355 qz698 (Real.log Real.pi)))

noncomputable def Ns576p1331 := @Enclosure.Real.IsNear.addLit_ft_p qz192 (Enclosure.sfrac Bool.true Ns576p1327 Ns576p1328) 4500540688224778029797 2251799813685248000 17493127379626589 2048000000000000000000 Ns576p1327 Ns576p1328 0 1 Ns576p1330 

noncomputable def Ns576p1332 := nat_lit 37753271621567878778979352576000 

noncomputable abbrev qz193 := (@HSub.hSub Real Real Real qz359 qz506 qz698)

noncomputable def Ns576p1333 := @Enclosure.Real.IsNear.subLit_ff_p qz193 (@HMul.hMul Real Real Real qz5 qz698 (Real.log Real.pi)) 5771110889881611635429 2251799813685248000 6065779864061 2000000000000000000 4733242845747 8388608000 369681 67108864000 Ns576p1332 4500540688224778029797 2251799813685248000 

noncomputable def Ns576p1334 := nat_lit 11542221779763223270858000 

noncomputable abbrev qz194 := qz506

noncomputable def Ns576p1335 := @Enclosure.Real.IsNear.subLit_ff_p qz194 qz698 6881041032445579856613 2251799813685248000 6065779864061 2000000000000000000 985816 2000 0 1 Ns576p1334 5771110889881611635429 2251799813685248000 6065779864061 2000000000000000000 

noncomputable def Ns576p1336 := nat_lit 15494726914821503259198988918953345024 

noncomputable def Ns576p1337 := nat_lit 119931682679061169162944512 

noncomputable def Ns576p1338 := nat_lit 153191553050670703364601668580787872045966671656451396877565202234101788922467305004926133042983718115194480422337380325686489560896017446837486490331749975212759766175563987944892006400 

noncomputable def Ns576p1339 := nat_lit 4831532525948733785093343413347415644497199157979120997642989530902542726245908826346922686496481476829285343516027153387282997643006969980183125268168163567518839138297756522475683840 

noncomputable def Ns576p1340 := nat_lit 469167131691368022318136528314249075652386727040436164116630459763947998142588361144708769533536412505590356139387438358508892856588559163055000454297210749432145762206886133760 

noncomputable def Ns576p1341 := BSN.log_dyadic_bound 1790181743424 5984485743424 8 7 Ns576p1338 268435456 81920000 Ns576p1339 Ns576p1340 165663136 7774667486848 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1790181743424) (BSN.artanhQ 5984485743424) 0 7 Ns576p1339 Ns576p1338 Ns576p1340 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz507 := (Real.log (Enclosure.sfrac Bool.false 3887333743424 16000000))

noncomputable def Ns576p1342 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 985816 4000) qz507 985816 4000 0 1 55847541745314919 4503599627370496 48828193 4000000000000000 6881925026649921523613 2251799813685248000 6016951738811 2000000000000000000 (Enclosure.Real.IsNear.const Bool.false 985816 4000) (BSN.isNear_log_sfrac 3887333743424 16000000 55847541745314919 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3887333743424) qz362)) Bool.false Ns576p1337 Ns576p112 1000001392640000 81920000000000000000000 55847541745314919 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3887333743424 16000000 17 7774667486848 4194304000000 165663136 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p1341 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1343 := BSN.arctan_dyadic_bound_f 1000 1971632 1 0 33554432 10240000 0 1 1 0 1 1 17018 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1971632) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1971632) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p1344 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1971632))) 884279719003555 562949953421312 1 2000000000000000 17018 33554432 1 10240000 29661923417976570118144 883994204341667 562949953421312 195312501 2000000000000000 qz17 (Ns576p1343 rfl) rfl rfl 

noncomputable abbrev qz508 := (@HMul.hMul Real Real Real qz590 qz595 qz697)

noncomputable abbrev qz195 := qz508

noncomputable abbrev qz509 := qz697

noncomputable abbrev qz196 := qz509

noncomputable def Ns576p1345 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 985816 4000) qz507) qz195 6881925026649921523613 2251799813685248000 6016951738811 2000000000000000000 883994204341667 2251799813685248 195312501 8000000000000000 Ns576p1336 6881041032445579856613 2251799813685248000 6065779864061 2000000000000000000 (Ns576p1342 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz196 1 4 0 1 883994204341667 562949953421312 195312501 2000000000000000 883994204341667 2251799813685248 195312501 8000000000000000 qz369 Ns576p1344 rfl) 

noncomputable def Ns576p1346 := @Ns576p1331 Ns576p1325 Ns576p1326 17493127379626589 2048000000000000000000 (@Ns576p1333 17493127379626589 2048000000000000000000 (Ns576p1335 (Ns576p1345 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 985816 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz698 (Real.log Real.pi) 985816 2000 0 1 38410761 33554432 3 268435456 4733242845747 8388608000 369681 67108864000 (Enclosure.Real.IsNear.const Bool.false 985816 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p1327 Ns576p1328) 

noncomputable def Ns576p1347 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns576p1325 Ns576p1326 17493127379626589 2048000000000000000000 134126553163 67108864 287 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz370 qz192 (Enclosure.sfrac Bool.true Ns576p1327 Ns576p1328)) Bool.false Ns576p1325 Ns576p1326 17493127379626589 2048000000000000000000 Ns576p1329 (Ns576p1346 rfl rfl)) 

noncomputable def Ns576p1348 := nat_lit 5691249190336346766442496 

noncomputable def Ns576p1349 := nat_lit 25650205080446912145049994380259026541057100283558912880786410714078220160205207234832460801 

noncomputable def Ns576p1350 := nat_lit 5133330660362904937396483134791632965849700352038159351603073932373040875403608499582161387520 

noncomputable def Ns576p1351 := nat_lit 1830722030905550881819226491973102359358523291526395444291142567333662583763711316945921 

noncomputable def Ns576p1352 := nat_lit 76946953797278925333386344687793133418452583804093685851470649857099993155448094281863490561 

noncomputable def Ns576p1353 := nat_lit 230999879716330722182841741065623483463236515841717170822138326956786839393162382481197262438400 

noncomputable def Ns576p1354 := BSN.cos_dyadic_bound_f 80877515391 137438953472 3 2 67108864 20500001 Ns576p1349 Ns576p1350 Ns576p1351 Ns576p1352 Ns576p1353 Ns576p1351 55820866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 80877515391) qz443 0 2 Ns576p1349 Ns576p1350 Ns576p1351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 80877515391) qz444 0 2 Ns576p1352 Ns576p1353 Ns576p1351 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1355 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz188) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 134126553163) qz384) Bool.false 134126553163 67108864 287 33554432 Bool.false 55820866 67108864 1 10240000 (Ns576p1347 rfl) (Enclosure.sfrac_false_div 134126553163 67108864) (BSN.cos_reduce0 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 134126553163) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p1348) qz386) 226375608064910080 72057594037927936 Bool.false 55820866 67108864 318 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q0 134126553163 67108864 226375608064910080 72057594037927936 318 Ns576p1348 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 55820866 67108864 Ns576p1348 Ns576p112 80877515391 137438953472 20500001 20480000 (Ns576p1354 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1356 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz188) Bool.false Ns576p1325 Ns576p1326 17493127379626589 2048000000000000000000 1073012425309 536870912 4587 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz188) (@HAdd.hAdd Real Real Real qz370 qz192 (Enclosure.sfrac Bool.true Ns576p1327 Ns576p1328)) Bool.false Ns576p1325 Ns576p1326 17493127379626589 2048000000000000000000 Ns576p1329 (Ns576p1346 rfl rfl)) 

noncomputable def Ns576p1357 := Ns576p1324 77669 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 837 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 289400847 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 582 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 86821835 536870912) qz191 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) Bool.false 27910433 33554432 181423 20971520000 446566928 536870912 4645 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 27910433 33554432 181423 20971520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz188) qz188) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz188)) Bool.false 55820866 67108864 2972434432 343597383680000 27910433 33554432 181423 20971520000 (Ns576p1355 rfl rfl) rfl)) rfl) (Ns576p1356 rfl) RS577to588.d7 

noncomputable def Ns576p1358 := nat_lit 2192559511474040567130200728427925693461663120183224968210079529054897505 

noncomputable def Ns576p1359 := nat_lit 76164051707379719873543323970861919532912658669060069204485774640481 

noncomputable def Ns576p1360 := nat_lit 5742294454919722870556444742405757325482254884746791676628639122937218401 

noncomputable def Ns576p1361 := BSN.sin_dyadic_bound_f 305646027 536870912 3 2 536870912 268435456 Ns576p1358 Ns576p151 Ns576p1359 Ns576p1360 Ns576p154 Ns576p1359 289400847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 305646027) qz375 0 2 Ns576p1358 Ns576p151 Ns576p1359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 305646027) qz376 0 2 Ns576p1360 Ns576p154 Ns576p1359 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1362 := nat_lit 45127467133233247364348918239802337925390717454549032923179878968174370583717878545388407317239027744146295689216 

noncomputable def Ns576p1363 := nat_lit 34915654113725391569330113408102968361384264805725474833457027706443039320676579827756269890351294910631936 

noncomputable def Ns576p1364 := nat_lit 273346706286799534975417955663423652453144001515119973395457993232542029204755297073184848981802059570145867141120 

noncomputable def Ns576p1365 := BSN.cos_dyadic_bound_f 756110058 536870912 4 3 536870912 268435456 Ns576p1362 Ns576p162 Ns576p1363 Ns576p1364 Ns576p165 Ns576p1363 86821835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 756110058) qz377 0 3 Ns576p1362 Ns576p162 Ns576p1363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 756110058) qz378 0 3 Ns576p1364 Ns576p165 Ns576p1363 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1366 := nat_lit 1062065808786151180817445124210755938237097926567902599272300378016973056 

noncomputable def Ns576p1367 := nat_lit 57899917442190565666532713494465011675035023021866561254802562744576 

noncomputable def Ns576p1368 := nat_lit 3186081626523569161321002307205278884687943709657664064694391528925430016 

noncomputable def Ns576p1369 := BSN.cos_dyadic_bound_f 295348482 536870912 3 2 536870912 268435456 Ns576p1366 Ns576p141 Ns576p1367 Ns576p1368 Ns576p144 Ns576p1367 457659297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 295348482) qz377 0 2 Ns576p1366 Ns576p141 Ns576p1367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 295348482) qz378 0 2 Ns576p1368 Ns576p144 Ns576p1367 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1370 := nat_lit 631768657152022099666278111188361011723608022989503134677702793154789376 

noncomputable def Ns576p1371 := nat_lit 20488512344963890523316041017301228116612510755181455452905821700096 

noncomputable def Ns576p1372 := nat_lit 1895264994431376371217787701483048432714590843946999041122202567820967936 

noncomputable def Ns576p1373 := BSN.cos_dyadic_bound_f 259381384 536870912 3 2 536870912 268435456 Ns576p1370 Ns576p141 Ns576p1371 Ns576p1372 Ns576p144 Ns576p1371 475422099 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 259381384) qz377 0 2 Ns576p1370 Ns576p141 Ns576p1371 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 259381384) qz378 0 2 Ns576p1372 Ns576p144 Ns576p1371 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1374 := Ns576p1322 131524 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 402 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 457659297 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 262 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 475422099 536870912) qz191 rfl rfl (Ns576p1357 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p1361 rfl rfl) (Ns576p1365 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p1356 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p1369 rfl rfl) (Ns576p1373 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p1375 := nat_lit 110947691781088861091996077945072612946347657111160045162895725438610155897787396277265833400464751969733798400000 

noncomputable def Ns576p1376 := nat_lit 29619426758723899352528312492461153769043420433945274802171568127364015833589533983821899412241000000000000 

noncomputable def Ns576p1377 := nat_lit 554316513682671077376226672154965901758930391392849898741251464697517080270077920999477210448642543252284992000000 

noncomputable def Ns576p1378 := BSN.sin_dyadic_bound_f 745815470 536870912 4 3 536870912 268435456 Ns576p1375 Ns576p135 Ns576p1376 Ns576p1377 Ns576p138 Ns576p1376 528041943 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 745815470) qz375 0 3 Ns576p1375 Ns576p135 Ns576p1376 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 745815470) qz376 0 3 Ns576p1377 Ns576p138 Ns576p1376 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1379 := nat_lit 199776452312736171076131098335921 

noncomputable def Ns576p1380 := BSN.sin_dyadic_bound_f 118887467 536870912 2 1 536870912 268435456 Ns576p1379 Ns576p300 Ns576p1379 Ns576p1379 Ns576p301 Ns576p1379 117918180 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 118887467) qz375 0 1 Ns576p1379 Ns576p300 Ns576p1379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 118887467) qz376 0 1 Ns576p1379 Ns576p301 Ns576p1379 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1381 := Ns576p1320 177004 BSN.abs_quadSignPos (BSN.cos_quad_nat3 147 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 528041943 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 117918180 536870912) qz191 rfl rfl (Ns576p1374 rfl rfl) (Ns576p1356 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p1378 rfl rfl) (Ns576p1380 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1382 := nat_lit 13390042623852549630523783379059090129903351872079575660502430028274508514364935956453411428155598477387727920081 

noncomputable def Ns576p1383 := nat_lit 916611189863092680859583478039958351332151875541358957109426227324796173276431077912071551130338344066001 

noncomputable def Ns576p1384 := nat_lit 81195255005035583438437374768649697541166021313995720363598238203645559959984050617805868811306801698547945987025 

noncomputable def Ns576p1385 := BSN.cos_dyadic_bound_f 558275749 536870912 4 3 536870912 268435456 Ns576p1382 Ns576p162 Ns576p1383 Ns576p1384 Ns576p165 Ns576p1383 271835296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 558275749) qz377 0 3 Ns576p1382 Ns576p162 Ns576p1383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 558275749) qz378 0 3 Ns576p1384 Ns576p165 Ns576p1383 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1386 := nat_lit 8071136740601636431188224467692203187522570188078552297538438366180212736 

noncomputable def Ns576p1387 := nat_lit 3341428595314931394700040454783684361523893013434862449701777330733056 

noncomputable def Ns576p1388 := nat_lit 24206727364614279430775273322167042193844662778208787167715911543879172096 

noncomputable def Ns576p1389 := BSN.cos_dyadic_bound_f 490333452 536870912 3 2 536870912 268435456 Ns576p1386 Ns576p141 Ns576p1387 Ns576p1388 Ns576p144 Ns576p1387 328094384 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 490333452) qz377 0 2 Ns576p1386 Ns576p141 Ns576p1387 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 490333452) qz378 0 2 Ns576p1388 Ns576p144 Ns576p1387 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1390 := Ns576p1318 216740 BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 271835296 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 328094384 536870912) qz191 rfl rfl (Ns576p1381 rfl) (Ns576p1356 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p1385 rfl rfl) (Ns576p1389 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1391 := nat_lit 17192081478919857943495357841117577491665752862841626315239700667717609058572794829179073747175162467793538017921 

noncomputable def Ns576p1392 := nat_lit 1938954210460015423124643373737147256001962233702545000005114229344541427010719463565368327045370509159041 

noncomputable def Ns576p1393 := nat_lit 104236549991609311914007362884885164454811277611775593066789414040429649252394958140963621380446266539279508466305 

noncomputable def Ns576p1394 := BSN.cos_dyadic_bound_f 594242847 536870912 4 3 536870912 268435456 Ns576p1391 Ns576p162 Ns576p1392 Ns576p1393 Ns576p165 Ns576p1392 240232893 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 594242847) qz377 0 3 Ns576p1391 Ns576p162 Ns576p1392 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 594242847) qz378 0 3 Ns576p1393 Ns576p165 Ns576p1392 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1395 := nat_lit 5177162865668583250731862823051292705659458102310420303989066445667655936 

noncomputable def Ns576p1396 := nat_lit 1375230007412603073832969454515079086384006367751976108458257538048256 

noncomputable def Ns576p1397 := nat_lit 15528738136990924546047922530244847958805606294195756959750282821926871296 

noncomputable def Ns576p1398 := BSN.cos_dyadic_bound_f 438830614 536870912 3 2 536870912 268435456 Ns576p1395 Ns576p141 Ns576p1396 Ns576p1397 Ns576p144 Ns576p1396 367289656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 438830614) qz377 0 2 Ns576p1395 Ns576p141 Ns576p1396 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 438830614) qz378 0 2 Ns576p1397 Ns576p144 Ns576p1396 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1399 := Ns576p1316 252478 BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 240232893 536870912) BSN.abs_quadSignPos qz658 (BSN.sfrac_eq_quadSignPos_mul Bool.false 367289656 536870912) qz191 rfl rfl (Ns576p1390 rfl) (Ns576p1356 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p1394 rfl rfl) (Ns576p1398 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1400 := nat_lit 135023604227388385224072171150625 

noncomputable def Ns576p1401 := BSN.sin_dyadic_bound_f 107795945 536870912 2 1 536870912 268435456 Ns576p1400 Ns576p300 Ns576p1400 Ns576p1400 Ns576p301 Ns576p1400 107073107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 107795945) qz375 0 1 Ns576p1400 Ns576p300 Ns576p1400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 107795945) qz376 0 1 Ns576p1400 Ns576p301 Ns576p1400 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1402 := Ns576p1314 Bool.false 183953052 252478 Bool.true 107795945 28296951008113761 1 Bool.false 107073107 Bool.false Bool.false 214862396 269180 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 107073107 536870912) qz191 rfl (Ns576p1399 rfl) (Ns576p1356 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p1401 rfl rfl) rfl 

noncomputable def Ns576p1403 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) 214862396 536870912 269180 536870912 214862396 536870912 269180 536870912 230706740990050304 53715599 67108864 67295 67108864 (Ns576p1402 rfl rfl rfl rfl) 

noncomputable def Ns576p1404 := @Enclosure.Real.IsNear.mulLit_ff qz695 (Zeta.RiemannSiegel.correction qz190) 2370205 8388608 1 33554432 864364931719653 2251799813685248 2714281517883 281474976710656000 2048722082986580138865 18889465931478580854784 

noncomputable abbrev qz699 := (@HPow.hPow Real Real Real qz7 qz189 qz9)

noncomputable def Ns576p1405 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz699 1 1 0 1 2370205 8388608 1 33554432 2370205 8388608 1 33554432 

noncomputable def Ns576p1406 := @Enclosure.Real.IsNear.sqrt_image qz189 1316151481489 8388608000 123227 8388608000 420298518 420298559 33554432 (@Enclosure.Real.IsNear.of_eq qz189 (@HMul.hMul Real Real Real qz5 qz188 qz3) Bool.false 1316151481489 8388608000 123227 8388608000 (BSN.t_div_two_pi_mk qz188 985816 1000 qz191) (@Enclosure.Real.IsNear.mulLit_ff qz188 qz3 985816 1000 0 1 10680707 67108864 1 67108864 1316151481489 8388608000 123227 8388608000 (Enclosure.Real.IsNear.const Bool.false 985816 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz787 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 985816 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz700 := qz787

noncomputable abbrev qz510 := qz700

noncomputable abbrev qz197 := qz510

noncomputable def Ns576p1407 := @Enclosure.Real.IsNear.sqrt_image qz197 840597077 67108864 41 67108864 118755538 118755545 33554432 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 840597077 67108864 41 67108864 840597077 67108864 41 67108864 (Ns576p1406 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p1408 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz197) 237511083 67108864 7 67108864 9480819 9480821 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz197) Bool.false 237511083 67108864 7 67108864 237511083 67108864 7 67108864 (Ns576p1407 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p1409 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 18961640 67108864 2 67108864 2370205 8388608 1 33554432 (Ns576p1408 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz511 := (@HMul.hMul Real Real Real qz590 qz588 qz694)

noncomputable abbrev qz198 := (Real.cos qz511)

noncomputable abbrev qz701 := (@HMul.hMul Real Real Real qz743 qz786 qz786)

noncomputable abbrev qz512 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz701 qz694) qz605)

noncomputable abbrev qz199 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz512))

noncomputable def Ns576p1410 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz190) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz198) qz199) Bool.false 864364931719653 

noncomputable def Ns576p1411 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz198) qz199 68005457 67108864 273 

noncomputable abbrev qz200 := (@Neg.neg Real Real.instNeg (Real.cos qz511))

noncomputable def Ns576p1412 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz198) (@Neg.neg Real Real.instNeg (@Inv.inv Real Real.instInv qz200)) Bool.true 68005457 67108864 273 67108864 (BSN.inv_eq_neg_inv_neg qz198) 

noncomputable def Ns576p1413 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz200) Bool.false 68005457 67108864 273 67108864 68005457 67108864 

noncomputable def Ns576p1414 := @Enclosure.Real.IsNear.recentre' qz198 Bool.true 66224092 67108864 1354514432 343597383680000 16556023 16777216 82673 20971520000 

noncomputable abbrev qz201 := qz511

noncomputable def Ns576p1415 := @Enclosure.Real.IsNear.cos_image qz201 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13858629) qz640) Bool.false 13858629 4194304 129 33554432 Bool.true 66224092 67108864 1 

noncomputable def Ns576p1416 := nat_lit 8851432736591605965417867 

noncomputable def Ns576p1417 := nat_lit 2305843009213693952000000000000 

noncomputable def Ns576p1418 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz190 884279719003555 140737488355328 1 500000000000000 35290709 67108864 41 67108864 31206858237956229470495 9444732965739290427392 Ns576p1416 

noncomputable def Ns576p1419 := @Enclosure.Real.IsNear.subLit_ff_p qz197 qz1 840597077 67108864 41 67108864 12 1 0 1 35290709 35290709 67108864 41 

noncomputable def Ns576p1420 := @Ns576p1419 67108864 (@Enclosure.Real.IsNear.recentre' qz197 Bool.false 840597077 67108864 41 67108864 840597077 67108864 41 67108864 (Ns576p1406 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p1421 := @Enclosure.Real.IsNear.recentre' qz201 Bool.false 31206858237956229470495 9444732965739290427392 Ns576p1416 Ns576p1417 13858629 4194304 129 33554432 (@Ns576p1418 Ns576p1417 RS577to588.d55 (Ns576p1420 rfl rfl) rfl) 

noncomputable def Ns576p1422 := nat_lit 249181209220397013029923786558013924133441 

noncomputable def Ns576p1423 := BSN.cos_dyadic_bound_f 22342348527 137438953472 2 1 67108864 20500001 Ns576p1422 Ns576p1164 Ns576p1422 Ns576p1422 Ns576p1165 Ns576p1422 66224092 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 22342348527) qz443 0 1 Ns576p1422 Ns576p1164 Ns576p1422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 22342348527) qz444 0 1 Ns576p1422 Ns576p1165 Ns576p1422 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1424 := @Ns576p1415 10240000 (Ns576p1421 rfl) (Enclosure.sfrac_false_div 13858629 4194304) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 13858629) qz640) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 98262687990341171150848) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false 66224092 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 13858629 4194304 226375608064910080 72057594037927936 0 98262687990341171150848 604462909807314587353088 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 66224092 67108864 98262687990341171150848 604462909807314587353088 22342348527 137438953472 20500001 20480000 (Ns576p1423 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1425 := @Enclosure.Real.IsNear.inv_image qz200 16556023 16777216 82673 20971520000 34002592 34002865 33554432 (@Enclosure.Real.IsNear.neg qz198 Bool.true 16556023 16777216 82673 20971520000 (Ns576p1414 (Ns576p1424 rfl rfl) rfl)) 

noncomputable def Ns576p1426 := Ns576p1412 (@Enclosure.Real.IsNear.neg (@Inv.inv Real Real.instInv qz200) Bool.false 68005457 67108864 273 67108864 (@Ns576p1413 273 67108864 (Ns576p1425 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1427 := @Enclosure.Real.IsNear.recentre' qz199 Bool.true 12710229 33554432 

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz355 qz352 qz512)

noncomputable def Ns576p1428 := @Enclosure.Real.IsNear.cos_image qz202 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 131485693)) qz384) Bool.true 131485693 67108864 

noncomputable def Ns576p1429 := nat_lit 1241847265790549268035648218805 

noncomputable def Ns576p1430 := nat_lit 152344579034582263820553748893364173 

noncomputable def Ns576p1431 := @Enclosure.Real.IsNear.recentre' qz202 Bool.true Ns576p1429 Ns576p660 Ns576p1430 

noncomputable abbrev qz203 := qz512

noncomputable def Ns576p1432 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz203 884279719003555 140737488355328 1 500000000000000 1404360225732551 

noncomputable abbrev qz513 := (@HSub.hSub Real Real Real qz594 qz701 qz694)

noncomputable abbrev qz204 := qz513

noncomputable def Ns576p1433 := @Enclosure.Real.IsNear.subLit_tf qz204 qz31 1122885249021895 4503599627370496 5645303243 4503599627370496 1 16 

noncomputable abbrev qz514 := qz701

noncomputable abbrev qz205 := qz514

noncomputable def Ns576p1434 := @Enclosure.Real.IsNear.subLit_ff_n qz205 qz190 1245434141722681 4503599627370496 2893839819 4503599627370496 35290709 67108864 41 67108864 

noncomputable def Ns576p1435 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 35290709 67108864 41 67108864 35290709 67108864 41 67108864 1245434141722681 4503599627370496 

noncomputable def Ns576p1436 := nat_lit 2475576810077854289050554046478861403043297028838523927407247846420737043764800307400470389530090986481 

noncomputable def Ns576p1437 := nat_lit 26701889609139562559881460046095342725188183208900381974161246079007582137923843359598046425046001 

noncomputable def Ns576p1438 := nat_lit 14931303183250825871392118685622766925114999463000247575561079796328074666199848055365108372891939036145 

noncomputable def Ns576p1439 := BSN.cos_dyadic_bound_t 131485693 67108864 4 3 33554432 10240000 Ns576p1436 Ns576p227 Ns576p1437 Ns576p1438 Ns576p230 Ns576p1437 12710229 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 131485693) qz606 0 3 Ns576p1436 Ns576p227 Ns576p1437 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 131485693) (BSN.cosOddQ 67108864) 0 3 Ns576p1438 Ns576p230 Ns576p1437 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1440 := @Ns576p1427 2747154432 343597383680000 12710229 33554432 167673 20971520000 (@Ns576p1428 265 33554432 Bool.true 12710229 33554432 1 10240000 (@Ns576p1431 Ns576p1051 131485693 67108864 265 33554432 (@Ns576p1432 4503599627370496 5645303243 4503599627370496 Ns576p1429 Ns576p660 Ns576p1430 Ns576p1051 RS577to588.d55 (@Ns576p1433 0 1 22469763611720816 1404360225732551 4503599627370496 5645303243 4503599627370496 (@Ns576p1434 75355553464216484577280 1122885249021895 4503599627370496 5645303243 4503599627370496 (@Ns576p1435 2893839819 4503599627370496 (Ns576p1420 rfl rfl) (Ns576p1420 rfl rfl) rfl) (Ns576p1420 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 131485693 67108864) (BSN.cos_neg_of_bound 131485693 67108864 Bool.true 12710229 33554432 1 10240000 (Ns576p1439 rfl rfl)) rfl rfl) 

noncomputable def Ns576p1441 := @Ns576p1404 3230207853890247321 1180591620717411303424000 (Ns576p1405 qz33 (@Enclosure.Real.IsNear.of_eq qz699 (@Inv.inv Real Real.instInv (Real.sqrt qz197)) Bool.false 2370205 8388608 1 33554432 (BSN.rpow_neg_quarter_mk qz189 (BSN.t_div_two_pi_nonneg qz188 985816 1000 qz191)) Ns576p1409) rfl) (@Ns576p1410 2251799813685248 2714281517883 281474976710656000 (BSN.correction_mk qz190 (BSN.cos_two_pi_p_ne_zero_mk qz188 985816 1000 12 qz191 rfl rfl (@BSN.floor_sqrt_eq_dec qz188 985816 1000 12 qz191 rfl rfl rfl))) (@Ns576p1411 67108864 12710229 33554432 167673 20971520000 864364931719653 2251799813685248 2714281517883 281474976710656000 Ns576p1426 (Ns576p1440 rfl) rfl)) 

noncomputable def Ns576p1442 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (hardyZApproximantRS₀ qz188) Bool.false 13070874894537356584079 18889465931478580854784 1187096367712864967321 1180591620717411303424000 (@Eq.refl Real (hardyZApproximantRS₀ qz188)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz188) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (@HMul.hMul Real Real Real qz5 qz695 (Zeta.RiemannSiegel.correction qz190))) Bool.false 13070874894537356584079 18889465931478580854784 1187096367712864967321 1180591620717411303424000 (BSN.hardyZApproximantRS₀_eq qz188 12 (@BSN.floor_sqrt_eq_dec qz188 985816 1000 12 qz191 rfl rfl rfl)) (@Ns576p1313 13070874894537356584079 18889465931478580854784 1187096367712864967321 1180591620717411303424000 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz188) qz188 12)) Bool.false 53715599 67108864 67295 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz188) qz188 12) (Ns576p1403 (Ns576p1402 rfl rfl rfl rfl) rfl rfl)) (Ns576p1441 rfl) rfl rfl)) 

theorem RS577to588.d68 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz188) Bool.false 13070874894537356584079 18889465931478580854784 1187096367712864967321 1180591620717411303424000 := Ns576p1442 

noncomputable def Ns576p1443 := nat_lit 11805916207174113034240000 

noncomputable def Ns576p1444 := nat_lit 309562322374509894081965981696 

noncomputable abbrev qz788 := (Enclosure.sfrac Bool.false 986438 1000)

noncomputable abbrev qz702 := qz788

noncomputable abbrev qz515 := qz702

noncomputable abbrev qz206 := qz515

noncomputable abbrev qz789 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 986438 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz703 := qz789

noncomputable abbrev qz516 := qz703

noncomputable abbrev qz207 := qz516

noncomputable abbrev qz790 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 986438 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz704 := qz790

noncomputable abbrev qz517 := qz704

noncomputable abbrev qz208 := qz517

noncomputable abbrev qz705 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz207 qz9))

noncomputable def Ns576p1445 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HMul.hMul Real Real Real qz5 qz705 (Zeta.RiemannSiegel.correction qz208)) 50983001 134217728 134673 134217728 512614155232908496875 4722366482869645213696 31767150561720213103 Ns576p1443 Ns576p1444 

noncomputable def Ns576p1446 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.sin BSN.quadSignPos 11 12 986438 1000 287 536870912 268435456 9007199254740992 Bool.false 1073856594626 4590 1334074092 54 154981288 8 

noncomputable def Ns576p1447 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 986438 1000 172 232 536870912 268435456 9007199254740992 Bool.false 1073856594626 4590 

noncomputable def Ns576p1448 := Ns576p1447 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 345155528 216874 Bool.true 518984305 Bool.true 395399354 28296951008113761 1 Bool.false 304959895 Bool.false Bool.false 397730956 Bool.false Bool.true 128798348 

noncomputable def Ns576p1449 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 986438 1000 32 106 536870912 268435456 9007199254740992 Bool.false 1073856594626 4590 

noncomputable def Ns576p1450 := Ns576p1449 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 346628119 177113 Bool.true 408502055 Bool.true 379891474 28296951008113761 1 Bool.false 388812420 Bool.false Bool.false 407980089 Bool.true Bool.true 345155528 

noncomputable def Ns576p1451 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 986438 1000 148 51 536870912 268435456 9007199254740992 Bool.false 1073856594626 4590 

noncomputable def Ns576p1452 := Ns576p1451 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 669284755 131605 Bool.false 148341053 Bool.false 313251803 28296951008113761 1 Bool.false 516507147 Bool.false Bool.false 295777732 Bool.false Bool.true 346628119 

noncomputable def Ns576p1453 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.cos BSN.quadSignNeg BSN.quadSignNeg 3 4 5 986438 1000 402 262 536870912 268435456 9007199254740992 Bool.false 1073856594626 4590 

noncomputable def Ns576p1454 := Ns576p1453 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 468718342 77715 Bool.false 676587392 Bool.false 566105142 28296951008113761 1 Bool.false 164060385 Bool.true Bool.false 265055045 Bool.true Bool.true 669284755 

noncomputable def Ns576p1455 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz206) qz206 Real.cos Real.sin BSN.quadSignNeg BSN.quadSignPos 1 2 3 986438 1000 838 583 536870912 268435456 9007199254740992 Bool.false 1073856594626 4590 

noncomputable def Ns576p1456 := Ns576p1455 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 298717664 4645 Bool.false 75035289 Bool.false 390100847 28296951008113761 1 Bool.false 531635821 Bool.true Bool.false 356668434 Bool.false Bool.true 468718342 

noncomputable def Ns576p1457 := nat_lit 2334252424719382894291949156460913059636674980407345540673 

noncomputable def Ns576p1458 := nat_lit 1167001473351299566881176238767847366727284679507968000 

noncomputable def Ns576p1459 := nat_lit 448322453158867261132499257840640000 

noncomputable def Ns576p1460 := nat_lit 2653454142435520149959248189515727441920 

noncomputable abbrev qz791 := (@Eq.refl Real (Enclosure.sfrac Bool.false 986438 1000))

noncomputable abbrev qz706 := qz791

noncomputable abbrev qz518 := qz706

noncomputable abbrev qz209 := qz518

noncomputable def Ns576p1461 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz206 986438 1000 3892240711376 16000000 1972876 4000 2000 Ns576p1459 Ns576p1460 qz209 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p1462 := nat_lit 47805489658252961675099118724319499461359103598742436672983040 

noncomputable abbrev qz707 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1972876))))

noncomputable abbrev qz519 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 986438 4000) (Real.log (Enclosure.sfrac Bool.false 3892240711376 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz707))

noncomputable abbrev qz708 := (Enclosure.sfrac Bool.false 986438 2000)

noncomputable abbrev qz210 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz519 qz708) (@HMul.hMul Real Real Real qz355 qz708 (Real.log Real.pi)))

noncomputable def Ns576p1463 := @Enclosure.Real.IsNear.addLit_ft_p qz210 (Enclosure.sfrac Bool.true Ns576p1459 Ns576p1460) 18016325562914572819637 9007199254740992000 70016532440552533 8192000000000000000000 Ns576p1459 Ns576p1460 0 1 Ns576p1462 

noncomputable def Ns576p1464 := nat_lit 604527570990678755485557981184000 

noncomputable abbrev qz211 := (@HSub.hSub Real Real Real qz359 qz519 qz708)

noncomputable def Ns576p1465 := @Enclosure.Real.IsNear.subLit_ff_p qz211 (@HMul.hMul Real Real Real qz5 qz708 (Real.log Real.pi)) 23101813031496797609141 9007199254740992000 24278305024267 8000000000000000000 18944917129659 33554432000 1479657 268435456000 Ns576p1464 18016325562914572819637 9007199254740992000 

noncomputable def Ns576p1466 := nat_lit 46203626062993595218282000 

noncomputable abbrev qz212 := qz519

noncomputable def Ns576p1467 := @Enclosure.Real.IsNear.subLit_ff_p qz212 qz708 27544334840720894942389 9007199254740992000 24278305024267 8000000000000000000 986438 2000 0 1 Ns576p1466 23101813031496797609141 9007199254740992000 24278305024267 8000000000000000000 

noncomputable def Ns576p1468 := nat_lit 62024328062419396377398507790739177472 

noncomputable def Ns576p1469 := nat_lit 119943883182653294969356288 

noncomputable def Ns576p1470 := nat_lit 154959484024956346710149047096676934456717592090943096207369476365867118161596646815609297949785524052711617644670006877374334490720074947830310600532124590643939687616533035699562086400 

noncomputable def Ns576p1471 := nat_lit 4907166204733807293086007356148392353473616855396079377265182124259003754451151607117644748658346506957834148272421995057536362683589841175340984027454196821381297315074106671853731840 

noncomputable def Ns576p1472 := nat_lit 487495563150841030803360421024235900597567748581433723635654535360385872932207642066106551597763163647813080034924160451381853176671056165274474243600196278620224254025410805760 

noncomputable def Ns576p1473 := BSN.log_dyadic_bound 1795088711376 5989392711376 8 7 Ns576p1470 268435456 81920000 Ns576p1471 Ns576p1472 166001768 7784481422752 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1795088711376) (BSN.artanhQ 5989392711376) 0 7 Ns576p1471 Ns576p1470 Ns576p1472 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz520 := (Real.log (Enclosure.sfrac Bool.false 3892240711376 16000000))

noncomputable def Ns576p1474 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 986438 4000) qz520 986438 4000 0 1 55853223047523431 4503599627370496 48828193 4000000000000000 27547870818276459114389 9007199254740992000 24082992523267 8000000000000000000 (Enclosure.Real.IsNear.const Bool.false 986438 4000) (BSN.isNear_log_sfrac 3892240711376 16000000 55853223047523431 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3892240711376) qz362)) Bool.false Ns576p1469 Ns576p112 1000001392640000 81920000000000000000000 55853223047523431 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3892240711376 16000000 17 7784481422752 4194304000000 166001768 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p1473 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1475 := BSN.arctan_dyadic_bound_f 1000 1972876 1 0 33554432 10240000 0 1 1 0 1 1 17007 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1972876) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1972876) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p1476 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1972876))) 884279719003555 562949953421312 1 2000000000000000 17007 33554432 1 10240000 29661929610426057752576 883994388891043 562949953421312 195312501 2000000000000000 qz17 (Ns576p1475 rfl) rfl rfl 

noncomputable abbrev qz521 := (@HMul.hMul Real Real Real qz590 qz595 qz707)

noncomputable abbrev qz213 := qz521

noncomputable abbrev qz522 := qz707

noncomputable abbrev qz214 := qz522

noncomputable def Ns576p1477 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 986438 4000) qz520) qz213 27547870818276459114389 9007199254740992000 24082992523267 8000000000000000000 883994388891043 2251799813685248 195312501 8000000000000000 Ns576p1468 27544334840720894942389 9007199254740992000 24278305024267 8000000000000000000 (Ns576p1474 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz214 1 4 0 1 883994388891043 562949953421312 195312501 2000000000000000 883994388891043 2251799813685248 195312501 8000000000000000 qz369 Ns576p1476 rfl) 

noncomputable def Ns576p1478 := @Ns576p1463 Ns576p1457 Ns576p1458 70016532440552533 8192000000000000000000 (@Ns576p1465 70016532440552533 8192000000000000000000 (Ns576p1467 (Ns576p1477 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 986438 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz708 (Real.log Real.pi) 986438 2000 0 1 38410761 33554432 3 268435456 18944917129659 33554432000 1479657 268435456000 (Enclosure.Real.IsNear.const Bool.false 986438 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p1459 Ns576p1460) 

noncomputable def Ns576p1479 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns576p1457 Ns576p1458 70016532440552533 8192000000000000000000 16779009291 8388608 287 33554432 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz370 qz210 (Enclosure.sfrac Bool.true Ns576p1459 Ns576p1460)) Bool.false Ns576p1457 Ns576p1458 70016532440552533 8192000000000000000000 Ns576p1461 (Ns576p1478 rfl rfl)) 

noncomputable def Ns576p1480 := nat_lit 46670431355587268549649511709185823670813134515553652438137896442698973506996445957022795585 

noncomputable def Ns576p1481 := nat_lit 1870710237398467577154454708893462382545177518582625291109898309548387887489888978716481 

noncomputable def Ns576p1482 := nat_lit 122229053352820391539671423454529424960653136300943765468461265133615185604601422448141780801 

noncomputable def Ns576p1483 := BSN.sin_dyadic_bound_f 81096258039 137438953472 3 2 67108864 20500001 Ns576p1480 Ns576p126 Ns576p1481 Ns576p1482 Ns576p129 Ns576p1481 37339708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 81096258039) qz371 0 2 Ns576p1480 Ns576p126 Ns576p1481 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 81096258039) qz372 0 2 Ns576p1482 Ns576p129 Ns576p1481 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1484 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz206) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16779009291) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 16779009291 8388608 287 33554432 Bool.true 37339708 67108864 1 10240000 (Ns576p1479 rfl) (Enclosure.sfrac_false_div 16779009291 8388608) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 16779009291) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 713330229468676627628032) (@Nat.cast Real Real.instNatCast Ns576p64)) 226375608064910080 72057594037927936 Bool.false 37339708 67108864 318 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 16779009291 8388608 226375608064910080 72057594037927936 318 713330229468676627628032 Ns576p64 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37339708 67108864 713330229468676627628032 Ns576p64 81096258039 137438953472 20500001 20480000 (Ns576p1483 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1485 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz206) Bool.false Ns576p1457 Ns576p1458 70016532440552533 8192000000000000000000 1073856594626 536870912 4590 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz206) (@HAdd.hAdd Real Real Real qz370 qz210 (Enclosure.sfrac Bool.true Ns576p1459 Ns576p1460)) Bool.false Ns576p1457 Ns576p1458 70016532440552533 8192000000000000000000 Ns576p1461 (Ns576p1478 rfl rfl)) 

noncomputable def Ns576p1486 := Ns576p1456 77715 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 838 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 531635821 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 583 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 356668434 536870912) qz209 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) Bool.true 9334927 16777216 181423 20971520000 298717664 536870912 4645 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 9334927 16777216 181423 20971520000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz206) qz206) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz206)) Bool.true 37339708 67108864 2972434432 343597383680000 9334927 16777216 181423 20971520000 (Ns576p1484 rfl rfl) rfl)) rfl) (Ns576p1485 rfl) RS577to588.d7 

noncomputable def Ns576p1487 := nat_lit 31700217230016645208536285417441 

noncomputable def Ns576p1488 := BSN.cos_dyadic_bound_f 75035289 536870912 2 1 536870912 268435456 Ns576p1487 Ns576p318 Ns576p1487 Ns576p1487 Ns576p319 Ns576p1487 531635821 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 75035289) qz377 0 1 Ns576p1487 Ns576p318 Ns576p1487 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 75035289) qz378 0 1 Ns576p1487 Ns576p319 Ns576p1487 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1489 := nat_lit 5818471202874873188335060952579333530829683683272758442893014189870063745 

noncomputable def Ns576p1490 := nat_lit 536309075401956291289476608499629569165945125953842249711537507704961 

noncomputable def Ns576p1491 := nat_lit 15237984840454969468786881437484493180489569545034251605839313722266263681 

noncomputable def Ns576p1492 := BSN.sin_dyadic_bound_f 390100847 536870912 3 2 536870912 268435456 Ns576p1489 Ns576p151 Ns576p1490 Ns576p1491 Ns576p154 Ns576p1490 356668434 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 390100847) qz375 0 2 Ns576p1489 Ns576p151 Ns576p1490 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 390100847) qz376 0 2 Ns576p1491 Ns576p154 Ns576p1490 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1493 := nat_lit 28908931052025513381527263486017154319418731934829254764428803719343784698634593559840372216457452011306316988416 

noncomputable def Ns576p1494 := nat_lit 9202097002110711862553906742221859888165948979410000793470761355877374208697304657619084872691887307227136 

noncomputable def Ns576p1495 := nat_lit 175205516248343734117005084334394695146359831404734103822680022466790590358508458889836217235990910728968622571520 

noncomputable def Ns576p1496 := BSN.cos_dyadic_bound_f 676587392 536870912 4 3 536870912 268435456 Ns576p1493 Ns576p162 Ns576p1494 Ns576p1495 Ns576p165 Ns576p1494 164060385 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 676587392) qz377 0 3 Ns576p1493 Ns576p162 Ns576p1494 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 676587392) qz378 0 3 Ns576p1495 Ns576p165 Ns576p1494 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1497 := nat_lit 14157697016286830014062329652274220475410630600686335978609168591707158827236745456101566227762427813289475772416 

noncomputable def Ns576p1498 := nat_lit 1083341040139346661134235003689672949026756658512670717333256327797053967361402046754126250820240851931136 

noncomputable def Ns576p1499 := nat_lit 85847918276515573952869755060651583514994919399656253344058540650407597436423280614124221848136311520684415979520 

noncomputable def Ns576p1500 := BSN.cos_dyadic_bound_f 566105142 536870912 4 3 536870912 268435456 Ns576p1497 Ns576p162 Ns576p1498 Ns576p1499 Ns576p165 Ns576p1498 265055045 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 566105142) qz377 0 3 Ns576p1497 Ns576p162 Ns576p1498 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 566105142) qz378 0 3 Ns576p1499 Ns576p165 Ns576p1498 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1501 := Ns576p1454 131605 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 402 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 164060385 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 262 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 265055045 536870912) qz209 rfl rfl (Ns576p1486 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p1488 rfl rfl) (Ns576p1492 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p1485 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p1496 rfl rfl) (Ns576p1500 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p1502 := nat_lit 484223017911223784354534234118481 

noncomputable def Ns576p1503 := BSN.cos_dyadic_bound_f 148341053 536870912 2 1 536870912 268435456 Ns576p1502 Ns576p318 Ns576p1502 Ns576p1502 Ns576p319 Ns576p1502 516507147 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 148341053) qz377 0 1 Ns576p1502 Ns576p318 Ns576p1502 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 148341053) qz378 0 1 Ns576p1502 Ns576p319 Ns576p1502 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1504 := nat_lit 2419091227250620288356585147445828752650860580392446402212398703078494945 

noncomputable def Ns576p1505 := nat_lit 92714708012520950462703903679858386252682410485114366245143044379361 

noncomputable def Ns576p1506 := nat_lit 6335565009462461435585545294133117438603082891410859915868075895514682081 

noncomputable def Ns576p1507 := BSN.sin_dyadic_bound_f 313251803 536870912 3 2 536870912 268435456 Ns576p1504 Ns576p151 Ns576p1505 Ns576p1506 Ns576p154 Ns576p1505 295777732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 313251803) qz375 0 2 Ns576p1504 Ns576p151 Ns576p1505 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 313251803) qz376 0 2 Ns576p1506 Ns576p154 Ns576p1505 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1508 := Ns576p1452 177113 BSN.abs_quadSignPos (BSN.cos_quad_nat0 148 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 516507147 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 295777732 536870912) qz209 rfl rfl (Ns576p1501 rfl rfl) (Ns576p1485 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p1503 rfl rfl) (Ns576p1507 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1509 := nat_lit 3887338892083975644784340059405837720263863850556028342007240441072690625 

noncomputable def Ns576p1510 := nat_lit 775450294049913046618152539225279251937589927587865118670385187890625 

noncomputable def Ns576p1511 := nat_lit 11660465775663827108259783873139062602287716371812909295784380552842290625 

noncomputable def Ns576p1512 := BSN.cos_dyadic_bound_f 408502055 536870912 3 2 536870912 268435456 Ns576p1509 Ns576p141 Ns576p1510 Ns576p1511 Ns576p144 Ns576p1510 388812420 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 408502055) qz377 0 2 Ns576p1509 Ns576p141 Ns576p1510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 408502055) qz378 0 2 Ns576p1511 Ns576p144 Ns576p1510 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1513 := nat_lit 2907312860582444007354694274541294209756807018608164968034868512511181056 

noncomputable def Ns576p1514 := nat_lit 433786840990926098699787961534563561902860991695234412423653467832576 

noncomputable def Ns576p1515 := nat_lit 8721071008065350169866683247700813502146615333841104435279758230597878016 

noncomputable def Ns576p1516 := BSN.cos_dyadic_bound_f 379891474 536870912 3 2 536870912 268435456 Ns576p1513 Ns576p141 Ns576p1514 Ns576p1515 Ns576p144 Ns576p1514 407980089 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 379891474) qz377 0 2 Ns576p1513 Ns576p141 Ns576p1514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 379891474) qz378 0 2 Ns576p1515 Ns576p144 Ns576p1514 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1517 := Ns576p1450 216874 BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 388812420 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 407980089 536870912) qz209 rfl rfl (Ns576p1508 rfl) (Ns576p1485 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p1512 rfl rfl) (Ns576p1516 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1518 := nat_lit 9998326465743366976153292031575938123498196328590101231883155554844681249426905124233627772090470756355801890625 

noncomputable def Ns576p1519 := nat_lit 381812981885376646043365493466567140427689372790305397829126585212606671377920960311500513431621337890625 

noncomputable def Ns576p1520 := nat_lit 60635503769154622960136992299985514319180255644217476170479497554896060500099638923199757684050085301397619490625 

noncomputable def Ns576p1521 := BSN.cos_dyadic_bound_f 518984305 536870912 4 3 536870912 268435456 Ns576p1518 Ns576p162 Ns576p1519 Ns576p1520 Ns576p165 Ns576p1519 304959895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 518984305) qz377 0 3 Ns576p1518 Ns576p162 Ns576p1519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 518984305) qz378 0 3 Ns576p1520 Ns576p165 Ns576p1519 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1522 := nat_lit 3411997080151354836611843770941949775421682149058366633839502174414479616 

noncomputable def Ns576p1523 := nat_lit 597430848081937462708364685942018236913340501165414740707822883348736 

noncomputable def Ns576p1524 := nat_lit 10234796378757900634910114583453965289791219766172769072037090877476741376 

noncomputable def Ns576p1525 := BSN.cos_dyadic_bound_f 395399354 536870912 3 2 536870912 268435456 Ns576p1522 Ns576p141 Ns576p1523 Ns576p1524 Ns576p144 Ns576p1523 397730956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 395399354) qz377 0 2 Ns576p1522 Ns576p141 Ns576p1523 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 395399354) qz378 0 2 Ns576p1524 Ns576p144 Ns576p1523 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1526 := Ns576p1448 252634 BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 304959895 536870912) BSN.abs_quadSignPos qz658 (BSN.sfrac_eq_quadSignPos_mul Bool.false 397730956 536870912) qz209 rfl rfl (Ns576p1517 rfl) (Ns576p1485 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p1521 rfl rfl) (Ns576p1525 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1527 := nat_lit 76168027727165887284392846000161 

noncomputable def Ns576p1528 := BSN.sin_dyadic_bound_f 93420713 536870912 2 1 536870912 268435456 Ns576p1527 Ns576p300 Ns576p1527 Ns576p1527 Ns576p301 Ns576p1527 92949973 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 93420713) qz375 0 1 Ns576p1527 Ns576p300 Ns576p1527 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 93420713) qz376 0 1 Ns576p1527 Ns576p301 Ns576p1527 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1529 := Ns576p1446 Bool.true 128798348 252634 Bool.true 93420713 28296951008113761 1 Bool.false 92949973 Bool.false Bool.true 101966002 269346 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 92949973 536870912) qz209 rfl (Ns576p1526 rfl) (Ns576p1485 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p1528 rfl rfl) rfl 

noncomputable def Ns576p1530 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) 101966002 536870912 269346 536870912 101966002 536870912 269346 536870912 109485160973467648 50983001 134217728 134673 134217728 (Ns576p1529 rfl rfl rfl rfl) 

noncomputable def Ns576p1531 := @Enclosure.Real.IsNear.mulLit_ff qz705 (Zeta.RiemannSiegel.correction qz208) 9479325 33554432 1 33554432 54077073550375 140737488355328 6673883328381 703687441776640000 512614155232908496875 4722366482869645213696 

noncomputable abbrev qz709 := (@HPow.hPow Real Real Real qz7 qz207 qz9)

noncomputable def Ns576p1532 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz709 1 1 0 1 9479325 33554432 1 33554432 9479325 33554432 1 33554432 

noncomputable def Ns576p1533 := @Enclosure.Real.IsNear.sqrt_image qz207 5267927625833 33554432000 493219 33554432000 420431091 420431131 33554432 (@Enclosure.Real.IsNear.of_eq qz207 (@HMul.hMul Real Real Real qz5 qz206 qz3) Bool.false 5267927625833 33554432000 493219 33554432000 (BSN.t_div_two_pi_mk qz206 986438 1000 qz209) (@Enclosure.Real.IsNear.mulLit_ff qz206 qz3 986438 1000 0 1 10680707 67108864 1 67108864 5267927625833 33554432000 493219 33554432000 (Enclosure.Real.IsNear.const Bool.false 986438 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz792 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 986438 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz710 := qz792

noncomputable abbrev qz523 := qz710

noncomputable abbrev qz215 := qz523

noncomputable def Ns576p1534 := @Enclosure.Real.IsNear.sqrt_image qz215 420431111 33554432 5 8388608 118774266 118774273 33554432 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 840862222 67108864 40 67108864 420431111 33554432 5 8388608 (Ns576p1533 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p1535 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz215) 237548539 67108864 7 67108864 9479324 9479326 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz215) Bool.false 237548539 67108864 7 67108864 237548539 67108864 7 67108864 (Ns576p1534 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p1536 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 18958650 67108864 2 67108864 9479325 33554432 1 33554432 (Ns576p1535 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz216 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz517))

noncomputable abbrev qz711 := (@HMul.hMul Real Real Real qz743 qz790 qz790)

noncomputable abbrev qz524 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz711 qz704) qz605)

noncomputable abbrev qz217 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz524))

noncomputable def Ns576p1537 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz208) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz216) qz217) Bool.false 54077073550375 

noncomputable def Ns576p1538 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz216) qz217 68304575 67108864 269 

noncomputable abbrev qz712 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz216))

noncomputable def Ns576p1539 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz216) (@Neg.neg Real Real.instNeg qz712) Bool.true 68304575 67108864 269 67108864 (BSN.inv_eq_neg_inv_neg qz216) 

noncomputable def Ns576p1540 := @Enclosure.Real.IsNear.recentre' qz712 Bool.false 68304575 67108864 269 67108864 68304575 67108864 

noncomputable def Ns576p1541 := @Enclosure.Real.IsNear.recentre' qz216 Bool.true 65934085 67108864 661897216 171798691840000 65934085 67108864 40399 10485760000 

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz355 qz352 qz517)

noncomputable def Ns576p1542 := @Enclosure.Real.IsNear.cos_image qz218 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 223404019) qz384) Bool.false 223404019 67108864 63 16777216 Bool.true 65934085 67108864 1 

noncomputable def Ns576p1543 := nat_lit 134930377083398034803682531 

noncomputable def Ns576p1544 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz208 884279719003555 140737488355328 1 500000000000000 17777927 33554432 5 8388608 15720660292025713530485 4722366482869645213696 Ns576p1543 

noncomputable def Ns576p1545 := @Enclosure.Real.IsNear.subLit_ff_p qz215 qz1 420431111 33554432 5 8388608 12 1 0 1 17777927 17777927 33554432 5 

noncomputable def Ns576p1546 := @Ns576p1545 8388608 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 840862222 67108864 40 67108864 420431111 33554432 5 8388608 (Ns576p1533 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p1547 := @Enclosure.Real.IsNear.recentre' qz218 Bool.false 15720660292025713530485 4722366482869645213696 Ns576p1543 Ns576p202 223404019 67108864 63 16777216 (@Ns576p1544 Ns576p202 RS577to588.d55 (Ns576p1546 rfl rfl) rfl) 

noncomputable def Ns576p1548 := nat_lit 1812292425996371207651328 

noncomputable def Ns576p1549 := nat_lit 439940454901642633030005802773582586374721 

noncomputable def Ns576p1550 := BSN.cos_dyadic_bound_f 25754224367 137438953472 2 1 67108864 20500001 Ns576p1549 Ns576p1164 Ns576p1549 Ns576p1549 Ns576p1165 Ns576p1549 65934085 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 25754224367) qz443 0 1 Ns576p1549 Ns576p1164 Ns576p1549 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 25754224367) qz444 0 1 Ns576p1549 Ns576p1165 Ns576p1549 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1551 := @Ns576p1542 10240000 (Ns576p1547 rfl) (Enclosure.sfrac_false_div 223404019 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 223404019) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p1548) qz386) 226375608064910080 72057594037927936 Bool.false 65934085 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 223404019 67108864 226375608064910080 72057594037927936 0 Ns576p1548 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 65934085 67108864 Ns576p1548 Ns576p112 25754224367 137438953472 20500001 20480000 (Ns576p1550 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1552 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz216) 65934085 67108864 40399 10485760000 34152153 34152422 33554432 (@Enclosure.Real.IsNear.neg qz216 Bool.true 65934085 67108864 40399 10485760000 (Ns576p1541 (Ns576p1551 rfl rfl) rfl)) 

noncomputable def Ns576p1553 := Ns576p1539 (@Enclosure.Real.IsNear.neg qz712 Bool.false 68304575 67108864 269 67108864 (@Ns576p1540 269 67108864 (Ns576p1552 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1554 := @Enclosure.Real.IsNear.recentre' qz217 Bool.true 12667280 33554432 

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz355 qz352 qz524)

noncomputable def Ns576p1555 := @Enclosure.Real.IsNear.cos_image qz219 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65696453)) qz373) Bool.true 65696453 33554432 

noncomputable def Ns576p1556 := nat_lit 310242729028502898524231850445 

noncomputable def Ns576p1557 := nat_lit 4662539823521986921613490326170131 

noncomputable def Ns576p1558 := @Enclosure.Real.IsNear.recentre' qz219 Bool.true Ns576p1556 Ns576p218 Ns576p1557 

noncomputable abbrev qz220 := qz524

noncomputable def Ns576p1559 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz220 884279719003555 140737488355328 1 500000000000000 350842298382799 

noncomputable abbrev qz525 := (@HSub.hSub Real Real Real qz594 qz711 qz704)

noncomputable abbrev qz221 := qz525

noncomputable def Ns576p1560 := @Enclosure.Real.IsNear.subLit_tf qz221 qz31 280473554205135 1125899906842624 172775765 140737488355328 1 16 

noncomputable abbrev qz526 := qz711

noncomputable abbrev qz222 := qz526

noncomputable def Ns576p1561 := @Enclosure.Real.IsNear.subLit_ff_n qz222 qz208 316054688417329 1125899906842624 88889685 140737488355328 17777927 33554432 5 8388608 

noncomputable def Ns576p1562 := @Enclosure.Real.IsNear.mulLit_ff qz208 qz208 17777927 33554432 5 8388608 17777927 33554432 5 8388608 316054688417329 1125899906842624 

noncomputable def Ns576p1563 := nat_lit 602669837253447622432158464505044696288439377409697426855392280644882596153612975441577087608170321 

noncomputable def Ns576p1564 := nat_lit 6464025600225003587298195192957750463658134962765895947991556354965069555115860988440796604241 

noncomputable def Ns576p1565 := nat_lit 3635028871913716625938701718861100041992005333299302972701673485333350226465701553724725974692669265 

noncomputable def Ns576p1566 := BSN.cos_dyadic_bound_t 65696453 33554432 4 3 33554432 10240000 Ns576p1563 Ns576p367 Ns576p1564 Ns576p1565 Ns576p370 Ns576p1564 12667280 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65696453) (BSN.cosEvenQ 33554432) 0 3 Ns576p1563 Ns576p367 Ns576p1564 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65696453) (BSN.cosOddQ 33554432) 0 3 Ns576p1565 Ns576p370 Ns576p1564 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1567 := @Ns576p1554 5381668864 687194767360000 791705 2097152 328471 41943040000 (@Ns576p1555 519 67108864 Bool.true 12667280 33554432 1 10240000 (@Ns576p1558 Ns576p221 65696453 33554432 519 67108864 (@Ns576p1559 1125899906842624 172775765 140737488355328 Ns576p1556 Ns576p218 Ns576p1557 Ns576p221 RS577to588.d55 (@Ns576p1560 0 1 5613476774124784 350842298382799 1125899906842624 172775765 140737488355328 (@Ns576p1561 9411130802374516408320 280473554205135 1125899906842624 172775765 140737488355328 (@Ns576p1562 88889685 140737488355328 (Ns576p1546 rfl rfl) (Ns576p1546 rfl rfl) rfl) (Ns576p1546 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65696453 33554432) (BSN.cos_neg_of_bound 65696453 33554432 Bool.true 12667280 33554432 1 10240000 (Ns576p1566 rfl rfl)) rfl rfl) 

noncomputable def Ns576p1568 := @Ns576p1531 31767150561720213103 Ns576p1443 (Ns576p1532 qz33 (@Enclosure.Real.IsNear.of_eq qz709 (@Inv.inv Real Real.instInv (Real.sqrt qz215)) Bool.false 9479325 33554432 1 33554432 (BSN.rpow_neg_quarter_mk qz207 (BSN.t_div_two_pi_nonneg qz206 986438 1000 qz209)) Ns576p1536) rfl) (@Ns576p1537 140737488355328 6673883328381 703687441776640000 (BSN.correction_mk qz208 (BSN.cos_two_pi_p_ne_zero_mk qz206 986438 1000 12 qz209 rfl rfl (@BSN.floor_sqrt_eq_dec qz206 986438 1000 12 qz209 rfl rfl rfl))) (@Ns576p1538 67108864 791705 2097152 328471 41943040000 54077073550375 140737488355328 6673883328381 703687441776640000 Ns576p1553 (Ns576p1567 rfl) rfl)) 

noncomputable def Ns576p1569 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (hardyZApproximantRS₀ qz206) Bool.true 2306419032622202441707 4722366482869645213696 11877729506359900053103 Ns576p1443 (@Eq.refl Real (hardyZApproximantRS₀ qz206)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz206) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HMul.hMul Real Real Real qz5 qz705 (Zeta.RiemannSiegel.correction qz208))) Bool.true 2306419032622202441707 4722366482869645213696 11877729506359900053103 Ns576p1443 (BSN.hardyZApproximantRS₀_eq qz206 12 (@BSN.floor_sqrt_eq_dec qz206 986438 1000 12 qz209 rfl rfl rfl)) (@Ns576p1445 2306419032622202441707 4722366482869645213696 11877729506359900053103 Ns576p1443 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz206) qz206 12)) Bool.true 50983001 134217728 134673 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz206) qz206 12) (Ns576p1530 (Ns576p1529 rfl rfl rfl rfl) rfl rfl)) (Ns576p1568 rfl) rfl rfl)) 

theorem RS577to588.d69 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz206) Bool.true 2306419032622202441707 4722366482869645213696 11877729506359900053103 Ns576p1443 := Ns576p1569 

noncomputable def Ns576p1570 := nat_lit 94447329657392904273920000 

noncomputable def Ns576p1571 := nat_lit 96153992763373647767832555945984 

noncomputable abbrev qz793 := (Enclosure.sfrac Bool.false 987447 1000)

noncomputable abbrev qz713 := qz793

noncomputable abbrev qz527 := qz713

noncomputable abbrev qz223 := qz527

noncomputable abbrev qz794 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 987447 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz714 := qz794

noncomputable abbrev qz528 := qz714

noncomputable abbrev qz224 := qz528

noncomputable abbrev qz795 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 987447 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz715 := qz795

noncomputable abbrev qz529 := qz715

noncomputable abbrev qz225 := qz529

noncomputable abbrev qz716 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz224 qz9))

noncomputable def Ns576p1572 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HMul.hMul Real Real Real qz5 qz716 (Zeta.RiemannSiegel.correction qz225)) 650887527 134217728 269621 268435456 16431133214780031148245 151115727451828646838272 256899713853407206267 Ns576p1570 Ns576p1571 

noncomputable def Ns576p1573 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin BSN.quadSignPos 11 12 987447 1000 287 536870912 268435456 9007199254740992 Bool.false 1075226217898 4594 1334074092 54 154981288 8 

noncomputable def Ns576p1574 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 987447 1000 172 232 536870912 268435456 9007199254740992 Bool.false 1075226217898 4594 

noncomputable def Ns576p1575 := Ns576p1574 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.false 1023003105 217096 Bool.true 396677707 Bool.true 324722544 28296951008113761 1 Bool.false 396871171 Bool.false Bool.false 441625425 Bool.false Bool.false 1281659864 

noncomputable def Ns576p1576 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.cos BSN.quadSignPos BSN.quadSignNeg 7 8 9 987447 1000 32 106 536870912 268435456 9007199254740992 Bool.false 1075226217898 4594 

noncomputable def Ns576p1577 := Ns576p1576 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.false 1008738942 177295 Bool.true 165317984 Bool.true 200510784 28296951008113761 1 Bool.false 511618320 Bool.false Bool.false 499860706 Bool.true Bool.false 1023003105 

noncomputable def Ns576p1578 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.cos Real.sin BSN.quadSignPos BSN.quadSignPos 5 6 7 987447 1000 148 51 536870912 268435456 9007199254740992 Bool.false 1075226217898 4594 

noncomputable def Ns576p1579 := Ns576p1578 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.false 707014178 131741 Bool.false 547363300 Bool.false 628770212 28296951008113761 1 Bool.false 281188718 Bool.false Bool.false 494570152 Bool.false Bool.false 1008738942 

noncomputable def Ns576p1580 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.sin BSN.quadSignPos BSN.quadSignPos 3 4 5 987447 1000 403 263 536870912 268435456 9007199254740992 Bool.false 1075226217898 4594 

noncomputable def Ns576p1581 := Ns576p1580 744261104 53 268435448 8 864060384 53 240095976 8 Bool.false 410910966 77797 Bool.false 451936353 Bool.false 220576630 28296951008113761 1 Bool.false 400420544 Bool.false Bool.false 214423142 Bool.false Bool.false 707014178 

noncomputable def Ns576p1582 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz223) qz223 Real.sin Real.cos BSN.quadSignPos BSN.quadSignPos 1 2 3 987447 1000 839 584 536870912 268435456 9007199254740992 Bool.false 1075226217898 4594 

noncomputable def Ns576p1583 := Ns576p1582 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 224176 4653 Bool.false 225863985 Bool.false 321287970 28296951008113761 1 Bool.false 219260003 Bool.false Bool.false 443569386 Bool.false Bool.false 410910966 

noncomputable def Ns576p1584 := nat_lit 33445126226689755244707549627425059283412165261631998915201 

noncomputable def Ns576p1585 := nat_lit 16699476929021928713058087890446187101252693509799936000 

noncomputable def Ns576p1586 := nat_lit 450620030865843087751630628163360000 

noncomputable def Ns576p1587 := nat_lit 2669780705154731464601574782129768051520 

noncomputable abbrev qz796 := (@Eq.refl Real (Enclosure.sfrac Bool.false 987447 1000))

noncomputable abbrev qz717 := qz796

noncomputable abbrev qz530 := qz717

noncomputable abbrev qz226 := qz530

noncomputable def Ns576p1588 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz223 987447 1000 3900207311236 16000000 1974894 4000 2000 Ns576p1586 Ns576p1587 qz226 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p1589 := nat_lit 96321963532866495104757742926984170736227035953500156875778880 

noncomputable abbrev qz718 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1974894))))

noncomputable abbrev qz531 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 987447 4000) (Real.log (Enclosure.sfrac Bool.false 3900207311236 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz718))

noncomputable abbrev qz719 := (Enclosure.sfrac Bool.false 987447 2000)

noncomputable abbrev qz227 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz531 qz719) (@HMul.hMul Real Real Real qz355 qz719 (Real.log Real.pi)))

noncomputable def Ns576p1590 := @Enclosure.Real.IsNear.addLit_ft_p qz227 (Enclosure.sfrac Bool.true Ns576p1586 Ns576p1587) 36078608053665146108769 18014398509481984000 140175891660348129 16384000000000000000000 Ns576p1586 Ns576p1587 0 1 Ns576p1589 

noncomputable def Ns576p1591 := nat_lit 2421194401182718991753508028416000 

noncomputable abbrev qz228 := (@HSub.hSub Real Real Real qz359 qz531 qz719)

noncomputable def Ns576p1592 := @Enclosure.Real.IsNear.subLit_ff_p qz228 (@HMul.hMul Real Real Real qz5 qz719 (Real.log Real.pi)) 46259986598265236781921 18014398509481984000 48605877695271 16000000000000000000 37928590717167 67108864000 2962341 536870912000 Ns576p1591 36078608053665146108769 18014398509481984000 

noncomputable def Ns576p1593 := nat_lit 18503994639306094712768400 

noncomputable abbrev qz229 := qz531

noncomputable def Ns576p1594 := @Enclosure.Real.IsNear.subLit_ff_p qz229 qz719 11030823696152293021869 3602879701896396800 48605877695271 16000000000000000000 987447 2000 0 1 Ns576p1593 46259986598265236781921 18014398509481984000 48605877695271 16000000000000000000 

noncomputable def Ns576p1595 := nat_lit 24839206743790552122306785599146688512 

noncomputable def Ns576p1596 := nat_lit 119963658272444296703508480 

noncomputable def Ns576p1597 := nat_lit 157870167369618885905140841686826571635308545748473634966546931565927741401659915793847652586495122208374490423836733763672062522936248467669957741202567060323608395488619870344865382400 

noncomputable def Ns576p1598 := nat_lit 5032244425769158301390642519676317755247003753707222346319096594521933587858886675030936796187381648603778890631253295220018447895059965616648948563791977860739601868610997805582909440 

noncomputable def Ns576p1599 := nat_lit 518674072722410862228606786852600980643249627435627932523503111830463783717754326797851447246904194481167372298027916190210017355887553306435199162402400506494632594946297692160 

noncomputable def Ns576p1600 := BSN.log_dyadic_bound 1803055311236 5997359311236 8 7 Ns576p1597 268435456 81920000 Ns576p1598 Ns576p1599 166550637 7800414622472 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1803055311236) (BSN.artanhQ 5997359311236) 0 7 Ns576p1598 Ns576p1597 Ns576p1599 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz532 := (Real.log (Enclosure.sfrac Bool.false 3900207311236 16000000))

noncomputable def Ns576p1601 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 987447 4000) qz532 987447 4000 0 1 55862431541292135 4503599627370496 48828193 4000000000000000 11032238087630858965869 3602879701896396800 48215252693271 16000000000000000000 (Enclosure.Real.IsNear.const Bool.false 987447 4000) (BSN.isNear_log_sfrac 3900207311236 16000000 55862431541292135 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3900207311236) qz362)) Bool.false Ns576p1596 Ns576p112 1000001392640000 81920000000000000000000 55862431541292135 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3900207311236 16000000 17 7800414622472 4194304000000 166550637 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p1600 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1602 := BSN.arctan_dyadic_bound_f 1000 1974894 1 0 33554432 10240000 0 1 1 0 1 1 16990 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1974894) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1974894) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p1603 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1974894))) 884279719003555 562949953421312 1 2000000000000000 16990 33554432 1 10240000 29661939180575265914880 883994674103715 562949953421312 195312501 2000000000000000 qz17 (Ns576p1602 rfl) rfl rfl 

noncomputable abbrev qz533 := (@HMul.hMul Real Real Real qz590 qz595 qz718)

noncomputable abbrev qz230 := qz533

noncomputable abbrev qz534 := qz718

noncomputable abbrev qz231 := qz534

noncomputable def Ns576p1604 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 987447 4000) qz532) qz230 11032238087630858965869 3602879701896396800 48215252693271 16000000000000000000 883994674103715 2251799813685248 195312501 8000000000000000 Ns576p1595 11030823696152293021869 3602879701896396800 48605877695271 16000000000000000000 (Ns576p1601 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz231 1 4 0 1 883994674103715 562949953421312 195312501 2000000000000000 883994674103715 2251799813685248 195312501 8000000000000000 qz369 Ns576p1603 rfl) 

noncomputable def Ns576p1605 := @Ns576p1590 Ns576p1584 Ns576p1585 140175891660348129 16384000000000000000000 (@Ns576p1592 140175891660348129 16384000000000000000000 (Ns576p1594 (Ns576p1604 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 987447 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz719 (Real.log Real.pi) 987447 2000 0 1 38410761 33554432 3 268435456 37928590717167 67108864000 2962341 536870912000 (Enclosure.Real.IsNear.const Bool.false 987447 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p1586 Ns576p1587) 

noncomputable def Ns576p1606 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns576p1584 Ns576p1585 140175891660348129 16384000000000000000000 134403277237 67108864 575 67108864 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz370 qz227 (Enclosure.sfrac Bool.true Ns576p1586 Ns576p1587)) Bool.false Ns576p1584 Ns576p1585 140175891660348129 16384000000000000000000 Ns576p1588 (Ns576p1605 rfl rfl)) 

noncomputable def Ns576p1607 := nat_lit 15187771370872697241206784 

noncomputable def Ns576p1608 := nat_lit 5533903079192358141622839292507771317770755590482412886446067020627258591588780761661595368609127142030521517551787793190155923129015691890881 

noncomputable def Ns576p1609 := nat_lit 21759806992472160846509436431027924547665573599712653161483140986990306751823661669370177199848368120331884066839754328502985489716814125465600 

noncomputable def Ns576p1610 := nat_lit 10218120122149025826191663171532610406447798351605728956034077846884863780827881367102249218202819431901830376496219630616915623053611201 

noncomputable def Ns576p1611 := nat_lit 33491564742061251339957444976634341134608649105117983512489021956324128714666430854647131801283439381543952407255410113012842360723397397696705 

noncomputable def Ns576p1612 := nat_lit 1980142436314966637032358715223541133837567197573851437694965829816117914415953211912686125186201498950201450082417643893771679564230085417369600 

noncomputable def Ns576p1613 := BSN.cos_dyadic_bound_f 215831212399 137438953472 4 3 67108864 20500001 Ns576p1608 Ns576p1609 Ns576p1610 Ns576p1611 Ns576p1612 Ns576p1610 28022 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 215831212399) qz443 0 3 Ns576p1608 Ns576p1609 Ns576p1610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 215831212399) qz444 0 3 Ns576p1611 Ns576p1612 Ns576p1610 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1614 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz223) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 134403277237) qz384) Bool.false 134403277237 67108864 575 67108864 Bool.true 28022 67108864 1 10240000 (Ns576p1606 rfl) (Enclosure.sfrac_false_div 134403277237 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 134403277237) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p1607) qz386) 226375608064910080 72057594037927936 Bool.false 28022 67108864 318 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 134403277237 67108864 226375608064910080 72057594037927936 318 Ns576p1607 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 28022 67108864 Ns576p1607 Ns576p112 215831212399 137438953472 20500001 20480000 (Ns576p1613 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1615 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz223) Bool.false Ns576p1584 Ns576p1585 140175891660348129 16384000000000000000000 1075226217898 536870912 4594 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz223) (@HAdd.hAdd Real Real Real qz370 qz227 (Enclosure.sfrac Bool.true Ns576p1586 Ns576p1587)) Bool.false Ns576p1584 Ns576p1585 140175891660348129 16384000000000000000000 Ns576p1588 (Ns576p1605 rfl rfl)) 

noncomputable def Ns576p1616 := Ns576p1583 77797 BSN.abs_quadSignPos (BSN.cos_quad_nat3 839 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 219260003 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 584 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 443569386 536870912) qz226 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) Bool.true 14011 33554432 363471 41943040000 224176 536870912 4653 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.true 14011 33554432 363471 41943040000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz223) qz223) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz223)) Bool.true 28022 67108864 5955108864 687194767360000 14011 33554432 363471 41943040000 (Ns576p1614 rfl rfl) rfl)) rfl) (Ns576p1615 rfl) RS577to588.d7 

noncomputable def Ns576p1617 := nat_lit 653813265500964122953230342083328938617312596502525579974360580213130625 

noncomputable def Ns576p1618 := nat_lit 6772919133422933748682031988631389625715002788157380740147562890625 

noncomputable def Ns576p1619 := nat_lit 1712357110633451922984772077404546578890710404644957597506888899742090625 

noncomputable def Ns576p1620 := BSN.sin_dyadic_bound_f 225863985 536870912 3 2 536870912 268435456 Ns576p1617 Ns576p151 Ns576p1618 Ns576p1619 Ns576p154 Ns576p1618 219260003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 225863985) qz375 0 2 Ns576p1617 Ns576p151 Ns576p1618 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 225863985) qz376 0 2 Ns576p1619 Ns576p154 Ns576p1618 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1621 := nat_lit 1487304159548081290325147291436114579286771660819662835169828840368800000 

noncomputable def Ns576p1622 := nat_lit 113541784702151595630606596514181592743132705823827374780176100000000 

noncomputable def Ns576p1623 := nat_lit 4461685395074839567784180661115315374674828717047340850759926168906400000 

noncomputable def Ns576p1624 := BSN.cos_dyadic_bound_f 321287970 536870912 3 2 536870912 268435456 Ns576p1621 Ns576p141 Ns576p1622 Ns576p1623 Ns576p144 Ns576p1622 443569386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 321287970) qz377 0 2 Ns576p1621 Ns576p141 Ns576p1622 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 321287970) qz378 0 2 Ns576p1623 Ns576p144 Ns576p1622 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1625 := nat_lit 10481960060243428619676030971279009878783188291702283510554139542903321345 

noncomputable def Ns576p1626 := nat_lit 1740276329871163483499500455986890094681370935135351212357948093756161 

noncomputable def Ns576p1627 := nat_lit 27449934948484426405892510495468666146183628068182428149488452601166426881 

noncomputable def Ns576p1628 := BSN.sin_dyadic_bound_f 451936353 536870912 3 2 536870912 268435456 Ns576p1625 Ns576p151 Ns576p1626 Ns576p1627 Ns576p154 Ns576p1626 400420544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 451936353) qz375 0 2 Ns576p1625 Ns576p151 Ns576p1626 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 451936353) qz376 0 2 Ns576p1627 Ns576p154 Ns576p1626 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1629 := nat_lit 2367216552419953929600512217610000 

noncomputable def Ns576p1630 := BSN.sin_dyadic_bound_f 220576630 536870912 2 1 536870912 268435456 Ns576p1629 Ns576p300 Ns576p1629 Ns576p1629 Ns576p301 Ns576p1629 214423142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 220576630) qz375 0 1 Ns576p1629 Ns576p300 Ns576p1629 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 220576630) qz376 0 1 Ns576p1629 Ns576p301 Ns576p1629 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1631 := Ns576p1581 131741 BSN.abs_quadSignPos (BSN.cos_quad_nat3 403 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 400420544 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 263 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 214423142 536870912) qz226 rfl rfl (Ns576p1616 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p1620 rfl rfl) (Ns576p1624 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p1615 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p1628 rfl rfl) (Ns576p1630 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p1632 := nat_lit 12372762320315657657571802796546560466102042659645593268374172592759424352111178390126140413977041469440000000000 

noncomputable def Ns576p1633 := nat_lit 723282740910806267022511146594039212677914657717385170550987606167436112331999361000000000000000000000000 

noncomputable def Ns576p1634 := nat_lit 75029257807377870132717163795001782504184904466473225827461623527798775231015048946457712603728238247936000000000 

noncomputable def Ns576p1635 := BSN.cos_dyadic_bound_f 547363300 536870912 4 3 536870912 268435456 Ns576p1632 Ns576p162 Ns576p1633 Ns576p1634 Ns576p165 Ns576p1633 281188718 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 547363300) qz377 0 3 Ns576p1632 Ns576p162 Ns576p1633 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 547363300) qz378 0 3 Ns576p1634 Ns576p165 Ns576p1633 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1636 := nat_lit 56013930557121677905907198857163739517998282650938454661235845078729527602073330481501172247356863124523456659456 

noncomputable def Ns576p1637 := nat_lit 3818594174849591937868782453591188899680283950498386814086870226689236572061159603226264760600855058579456 

noncomputable def Ns576p1638 := nat_lit 279961986358927547082403565923918279917784473710083601240860430189108818583508071567051222610106713571432874377216 

noncomputable def Ns576p1639 := BSN.sin_dyadic_bound_f 628770212 536870912 4 3 536870912 268435456 Ns576p1636 Ns576p135 Ns576p1637 Ns576p1638 Ns576p138 Ns576p1637 494570152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 628770212) qz375 0 3 Ns576p1636 Ns576p135 Ns576p1637 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 628770212) qz376 0 3 Ns576p1638 Ns576p138 Ns576p1637 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1640 := Ns576p1579 177295 BSN.abs_quadSignPos (BSN.cos_quad_nat0 148 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 281188718 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat3 51 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 494570152 536870912) qz226 rfl rfl (Ns576p1631 rfl rfl) (Ns576p1615 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p1635 rfl rfl) (Ns576p1639 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1641 := nat_lit 104248905774122838881717107113584546365992838267651032608636918957080576 

noncomputable def Ns576p1642 := nat_lit 557905707645630528110414349059273673041556981056162214172526903296 

noncomputable def Ns576p1643 := nat_lit 312745601510953225384095100512055520550632431688990985501482411817435136 

noncomputable def Ns576p1644 := BSN.cos_dyadic_bound_f 165317984 536870912 3 2 536870912 268435456 Ns576p1641 Ns576p141 Ns576p1642 Ns576p1643 Ns576p144 Ns576p1642 511618320 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 165317984) qz377 0 2 Ns576p1641 Ns576p141 Ns576p1642 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 165317984) qz378 0 2 Ns576p1643 Ns576p144 Ns576p1642 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1645 := nat_lit 225602936812876963654612376232352227726068328652620054414722451086770176 

noncomputable def Ns576p1646 := nat_lit 2612774210652777913670552286403601205956981829136545886089454288896 

noncomputable def Ns576p1647 := nat_lit 676803584890209585408009787592483875975793071994201890152395174351732736 

noncomputable def Ns576p1648 := BSN.cos_dyadic_bound_f 200510784 536870912 3 2 536870912 268435456 Ns576p1645 Ns576p141 Ns576p1646 Ns576p1647 Ns576p144 Ns576p1646 499860706 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 200510784) qz377 0 2 Ns576p1645 Ns576p141 Ns576p1646 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 200510784) qz378 0 2 Ns576p1647 Ns576p144 Ns576p1646 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1649 := Ns576p1577 217096 BSN.abs_quadSignPos (BSN.cos_quad_nat0 32 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 511618320 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 106 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 499860706 536870912) qz226 rfl rfl (Ns576p1640 rfl) (Ns576p1615 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p1644 rfl rfl) (Ns576p1648 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1650 := nat_lit 3456344268757190381523747607788772306819327913831347305801330603052618081 

noncomputable def Ns576p1651 := nat_lit 613059113678104656766909424266941624005294749135591678880314040373601 

noncomputable def Ns576p1652 := nat_lit 10367806688044214935257709004517783037209973151995770734046231181077107041 

noncomputable def Ns576p1653 := BSN.cos_dyadic_bound_f 396677707 536870912 3 2 536870912 268435456 Ns576p1650 Ns576p141 Ns576p1651 Ns576p1652 Ns576p144 Ns576p1651 396871171 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 396677707) qz377 0 2 Ns576p1650 Ns576p141 Ns576p1651 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 396677707) qz378 0 2 Ns576p1652 Ns576p144 Ns576p1651 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1654 := nat_lit 1551933607270153237062940361738981790304273238736218495036368563046711296 

noncomputable def Ns576p1655 := nat_lit 123623070438943116611802501975424488141813020353398674146897969545216 

noncomputable def Ns576p1656 := nat_lit 4655553575669581824955597480212994521936536090167948687760811893201043456 

noncomputable def Ns576p1657 := BSN.cos_dyadic_bound_f 324722544 536870912 3 2 536870912 268435456 Ns576p1654 Ns576p141 Ns576p1655 Ns576p1656 Ns576p144 Ns576p1655 441625425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 324722544) qz377 0 2 Ns576p1654 Ns576p141 Ns576p1655 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 324722544) qz378 0 2 Ns576p1656 Ns576p144 Ns576p1655 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1658 := Ns576p1575 252892 BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 396871171 536870912) BSN.abs_quadSignPos qz658 (BSN.sfrac_eq_quadSignPos_mul Bool.false 441625425 536870912) qz226 rfl rfl (Ns576p1649 rfl) (Ns576p1615 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p1653 rfl rfl) (Ns576p1657 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1659 := nat_lit 23843326050335059385857600000000 

noncomputable def Ns576p1660 := BSN.sin_dyadic_bound_f 69878200 536870912 2 1 536870912 268435456 Ns576p1659 Ns576p300 Ns576p1659 Ns576p1659 Ns576p301 Ns576p1659 69681063 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 69878200) qz375 0 1 Ns576p1659 Ns576p300 Ns576p1659 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 69878200) qz376 0 1 Ns576p1659 Ns576p301 Ns576p1659 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1661 := Ns576p1573 Bool.false 1281659864 252892 Bool.true 69878200 28296951008113761 1 Bool.false 69681063 Bool.false Bool.false 1301775054 269621 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 69681063 536870912) qz226 rfl (Ns576p1658 rfl) (Ns576p1615 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p1660 rfl rfl) rfl 

noncomputable def Ns576p1662 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) 1301775054 536870912 269621 536870912 1301775054 536870912 269621 536870912 1397770320919658496 650887527 134217728 269621 268435456 (Ns576p1661 rfl rfl rfl rfl) 

noncomputable def Ns576p1663 := @Enclosure.Real.IsNear.mulLit_ff qz716 (Zeta.RiemannSiegel.correction qz225) 18953805 67108864 1 67108864 866904202864809 2251799813685248 13525404804007 1407374883553280000 16431133214780031148245 151115727451828646838272 

noncomputable abbrev qz720 := (@HPow.hPow Real Real Real qz7 qz224 qz9)

noncomputable def Ns576p1664 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz720 1 1 0 1 18953805 67108864 1 67108864 18953805 67108864 1 67108864 

noncomputable def Ns576p1665 := @Enclosure.Real.IsNear.sqrt_image qz224 10546632085029 67108864000 987447 67108864000 420646060 420646100 33554432 (@Enclosure.Real.IsNear.of_eq qz224 (@HMul.hMul Real Real Real qz5 qz223 qz3) Bool.false 10546632085029 67108864000 987447 67108864000 (BSN.t_div_two_pi_mk qz223 987447 1000 qz226) (@Enclosure.Real.IsNear.mulLit_ff qz223 qz3 987447 1000 0 1 10680707 67108864 1 67108864 10546632085029 67108864000 987447 67108864000 (Enclosure.Real.IsNear.const Bool.false 987447 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz797 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 987447 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz721 := qz797

noncomputable abbrev qz535 := qz721

noncomputable abbrev qz232 := qz535

noncomputable def Ns576p1666 := @Enclosure.Real.IsNear.sqrt_image qz232 6572595 524288 5 8388608 118804627 118804634 33554432 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 841292160 67108864 40 67108864 6572595 524288 5 8388608 (Ns576p1665 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p1667 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz232) 237609261 67108864 7 67108864 9476902 9476903 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz232) Bool.false 237609261 67108864 7 67108864 237609261 67108864 7 67108864 (Ns576p1666 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p1668 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 18953805 67108864 1 67108864 18953805 67108864 1 67108864 (Ns576p1667 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz233 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz529))

noncomputable abbrev qz722 := (@HMul.hMul Real Real Real qz743 qz795 qz795)

noncomputable abbrev qz536 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz722 qz715) qz605)

noncomputable abbrev qz234 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz536))

noncomputable def Ns576p1669 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz225) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz233) qz234) Bool.false 866904202864809 

noncomputable def Ns576p1670 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz233) qz234 68886011 67108864 273 

noncomputable abbrev qz723 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz233))

noncomputable def Ns576p1671 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz233) (@Neg.neg Real Real.instNeg qz723) Bool.true 68886011 67108864 273 67108864 (BSN.inv_eq_neg_inv_neg qz233) 

noncomputable def Ns576p1672 := @Enclosure.Real.IsNear.recentre' qz723 Bool.false 68886011 67108864 273 67108864 68886011 67108864 

noncomputable def Ns576p1673 := @Enclosure.Real.IsNear.recentre' qz233 Bool.true 65377564 67108864 661897216 171798691840000 16344391 16777216 40399 10485760000 

noncomputable abbrev qz235 := (@HMul.hMul Real Real Real qz355 qz352 qz529)

noncomputable def Ns576p1674 := @Enclosure.Real.IsNear.cos_image qz235 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 226105399) qz384) Bool.false 226105399 67108864 63 16777216 Bool.true 65377564 67108864 1 

noncomputable def Ns576p1675 := nat_lit 134930377083859677216009443 

noncomputable def Ns576p1676 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz225 884279719003555 140737488355328 1 500000000000000 281139 524288 5 8388608 248605515920940449145 73786976294838206464 Ns576p1675 

noncomputable def Ns576p1677 := @Enclosure.Real.IsNear.subLit_ff_p qz232 qz1 6572595 524288 5 8388608 12 1 0 1 281139 281139 524288 5 

noncomputable def Ns576p1678 := @Ns576p1677 8388608 (@Enclosure.Real.IsNear.recentre' qz232 Bool.false 841292160 67108864 40 67108864 6572595 524288 5 8388608 (Ns576p1665 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p1679 := @Enclosure.Real.IsNear.recentre' qz235 Bool.false 248605515920940449145 73786976294838206464 Ns576p1675 Ns576p202 226105399 67108864 63 16777216 (@Ns576p1676 Ns576p202 RS577to588.d55 (Ns576p1678 rfl rfl) rfl) 

noncomputable def Ns576p1680 := nat_lit 2201602312760726743154688 

noncomputable def Ns576p1681 := nat_lit 958156144316842742119562541026302158465601 

noncomputable def Ns576p1682 := BSN.cos_dyadic_bound_f 31286650607 137438953472 2 1 67108864 20500001 Ns576p1681 Ns576p1164 Ns576p1681 Ns576p1681 Ns576p1165 Ns576p1681 65377564 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 31286650607) qz443 0 1 Ns576p1681 Ns576p1164 Ns576p1681 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 31286650607) qz444 0 1 Ns576p1681 Ns576p1165 Ns576p1681 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1683 := @Ns576p1674 10240000 (Ns576p1679 rfl) (Enclosure.sfrac_false_div 226105399 67108864) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 226105399) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p1680) qz386) 226375608064910080 72057594037927936 Bool.false 65377564 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 226105399 67108864 226375608064910080 72057594037927936 0 Ns576p1680 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 65377564 67108864 Ns576p1680 Ns576p112 31286650607 137438953472 20500001 20480000 (Ns576p1682 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1684 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz233) 16344391 16777216 40399 10485760000 34442869 34443142 33554432 (@Enclosure.Real.IsNear.neg qz233 Bool.true 16344391 16777216 40399 10485760000 (Ns576p1673 (Ns576p1683 rfl rfl) rfl)) 

noncomputable def Ns576p1685 := Ns576p1671 (@Enclosure.Real.IsNear.neg qz723 Bool.false 68886011 67108864 273 67108864 (@Ns576p1672 273 67108864 (Ns576p1684 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1686 := @Enclosure.Real.IsNear.recentre' qz234 Bool.true 12584619 33554432 

noncomputable abbrev qz236 := (@HMul.hMul Real Real Real qz355 qz352 qz536)

noncomputable def Ns576p1687 := @Enclosure.Real.IsNear.cos_image qz236 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65607235)) qz373) Bool.true 65607235 33554432 

noncomputable def Ns576p1688 := nat_lit 75639992485206103000106725 

noncomputable def Ns576p1689 := nat_lit 38685626227668133590597632 

noncomputable def Ns576p1690 := nat_lit 93830913434890185572136031721959 

noncomputable def Ns576p1691 := @Enclosure.Real.IsNear.recentre' qz236 Bool.true Ns576p1688 Ns576p1689 Ns576p1690 

noncomputable def Ns576p1692 := nat_lit 12089258196146291747061760000000000000 

noncomputable abbrev qz237 := qz536

noncomputable def Ns576p1693 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz237 884279719003555 140737488355328 1 500000000000000 85538535895 

noncomputable abbrev qz537 := (@HSub.hSub Real Real Real qz594 qz722 qz715)

noncomputable abbrev qz238 := qz537

noncomputable def Ns576p1694 := @Enclosure.Real.IsNear.subLit_tf qz238 qz31 68358666711 274877906944 86925305 70368744177664 1 16 

noncomputable abbrev qz538 := qz722

noncomputable abbrev qz239 := qz538

noncomputable def Ns576p1695 := @Enclosure.Real.IsNear.subLit_ff_n qz239 qz225 79039137321 274877906944 44982265 70368744177664 281139 524288 5 8388608 

noncomputable def Ns576p1696 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz225 281139 524288 5 8388608 281139 524288 5 8388608 79039137321 274877906944 

noncomputable def Ns576p1697 := nat_lit 599374470855643082068497095911576373348429656415347202061723302888843476156739426366840091050640625 

noncomputable def Ns576p1698 := nat_lit 6359468477616707118205689341942210094940950133202978276994962623353861230714077692539306640625 

noncomputable def Ns576p1699 := nat_lit 3615266044314473597941182810937924576298529973110664418713611296805524623450096407369066564420240625 

noncomputable def Ns576p1700 := BSN.cos_dyadic_bound_t 65607235 33554432 4 3 33554432 10240000 Ns576p1697 Ns576p367 Ns576p1698 Ns576p1699 Ns576p370 Ns576p1698 12584619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 65607235) (BSN.cosEvenQ 33554432) 0 3 Ns576p1697 Ns576p367 Ns576p1698 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 65607235) (BSN.cosOddQ 33554432) 0 3 Ns576p1699 Ns576p370 Ns576p1698 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1701 := @Ns576p1686 2706194432 343597383680000 12584619 33554432 165173 20971520000 (@Ns576p1687 261 33554432 Bool.true 12584619 33554432 1 10240000 (@Ns576p1691 Ns576p1692 65607235 33554432 261 33554432 (@Ns576p1693 274877906944 86925305 70368744177664 Ns576p1688 Ns576p1689 Ns576p1690 Ns576p1692 RS577to588.d55 (@Ns576p1694 0 1 1368616574320 85538535895 274877906944 86925305 70368744177664 (@Ns576p1695 35839628652576768 68358666711 274877906944 86925305 70368744177664 (@Ns576p1696 44982265 70368744177664 (Ns576p1678 rfl rfl) (Ns576p1678 rfl rfl) rfl) (Ns576p1678 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 65607235 33554432) (BSN.cos_neg_of_bound 65607235 33554432 Bool.true 12584619 33554432 1 10240000 (Ns576p1700 rfl rfl)) rfl rfl) 

noncomputable def Ns576p1702 := @Ns576p1663 256899713853407206267 Ns576p1570 (Ns576p1664 qz33 (@Enclosure.Real.IsNear.of_eq qz720 (@Inv.inv Real Real.instInv (Real.sqrt qz232)) Bool.false 18953805 67108864 1 67108864 (BSN.rpow_neg_quarter_mk qz224 (BSN.t_div_two_pi_nonneg qz223 987447 1000 qz226)) Ns576p1668) rfl) (@Ns576p1669 2251799813685248 13525404804007 1407374883553280000 (BSN.correction_mk qz225 (BSN.cos_two_pi_p_ne_zero_mk qz223 987447 1000 12 qz226 rfl rfl (@BSN.floor_sqrt_eq_dec qz223 987447 1000 12 qz226 rfl rfl rfl))) (@Ns576p1670 67108864 12584619 33554432 165173 20971520000 866904202864809 2251799813685248 13525404804007 1407374883553280000 Ns576p1685 (Ns576p1701 rfl) rfl)) 

noncomputable def Ns576p1703 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (hardyZApproximantRS₀ qz223) Bool.false 716403072799545882402603 151115727451828646838272 95121355583483133926267 Ns576p1570 (@Eq.refl Real (hardyZApproximantRS₀ qz223)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz223) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HMul.hMul Real Real Real qz5 qz716 (Zeta.RiemannSiegel.correction qz225))) Bool.false 716403072799545882402603 151115727451828646838272 95121355583483133926267 Ns576p1570 (BSN.hardyZApproximantRS₀_eq qz223 12 (@BSN.floor_sqrt_eq_dec qz223 987447 1000 12 qz226 rfl rfl rfl)) (@Ns576p1572 716403072799545882402603 151115727451828646838272 95121355583483133926267 Ns576p1570 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz223) qz223 12)) Bool.false 650887527 134217728 269621 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz223) qz223 12) (Ns576p1662 (Ns576p1661 rfl rfl rfl rfl) rfl rfl)) (Ns576p1702 rfl) rfl rfl)) 

theorem RS577to588.d70 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz223) Bool.false 716403072799545882402603 151115727451828646838272 95121355583483133926267 Ns576p1570 := Ns576p1703 

noncomputable def Ns576p1704 := nat_lit 2951479051793528258560000 

noncomputable def Ns576p1705 := nat_lit 1326281779029828119438842396672 

noncomputable abbrev qz798 := (Enclosure.sfrac Bool.false 989310 1000)

noncomputable abbrev qz724 := qz798

noncomputable abbrev qz539 := qz724

noncomputable abbrev qz240 := qz539

noncomputable abbrev qz799 := (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 989310 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))

noncomputable abbrev qz725 := qz799

noncomputable abbrev qz540 := qz725

noncomputable abbrev qz241 := qz540

noncomputable abbrev qz800 := (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 989310 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi))) (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz726 := qz800

noncomputable abbrev qz541 := qz726

noncomputable abbrev qz242 := qz541

noncomputable abbrev qz727 := (@HMul.hMul Real Real Real qz5 qz6 (@HPow.hPow Real Real Real qz7 qz241 qz9))

noncomputable def Ns576p1706 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HMul.hMul Real Real Real qz5 qz727 (Zeta.RiemannSiegel.correction qz242)) 266197881 134217728 270131 268435456 515563994530631336057 4722366482869645213696 8291866056146120259 Ns576p1704 Ns576p1705 

noncomputable def Ns576p1707 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin BSN.quadSignPos 11 12 989310 1000 287 536870912 268435456 9007199254740992 Bool.false 1077755793978 4603 1334074092 54 154981288 8 

noncomputable def Ns576p1708 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 9 10 11 989310 1000 172 232 536870912 268435456 9007199254740992 Bool.false 1077755793978 4603 

noncomputable def Ns576p1709 := Ns576p1708 1236190956 54 169773496 8 1287360220 54 161872664 8 Bool.true 852599615 217506 Bool.true 170125378 Bool.true 193498554 28296951008113761 1 Bool.false 510140777 Bool.false Bool.false 502376466 Bool.false Bool.true 539806733 

noncomputable def Ns576p1710 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.sin BSN.quadSignPos BSN.quadSignNeg 7 8 9 989310 1000 31 105 536870912 268435456 9007199254740992 Bool.false 1077755793978 4603 

noncomputable def Ns576p1711 := Ns576p1710 1116391676 54 189812536 8 1179625948 54 178956968 8 Bool.true 842771045 177629 Bool.true 558894453 Bool.true 711892701 28296951008113761 1 Bool.false 463277267 Bool.false Bool.false 520865475 Bool.true Bool.true 852599615 

noncomputable def Ns576p1712 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignPos 5 6 7 989310 1000 149 52 536870912 268435456 9007199254740992 Bool.false 1077755793978 4603 

noncomputable def Ns576p1713 := Ns576p1712 961943533 54 219176632 8 1044702541 54 202918136 8 Bool.true 839067961 131989 Bool.false 441523722 Bool.false 368750601 28296951008113761 1 Bool.false 393409570 Bool.true Bool.false 415133454 Bool.false Bool.true 842771045 

noncomputable def Ns576p1714 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.cos Real.cos BSN.quadSignPos BSN.quadSignPos 3 4 5 989310 1000 404 264 536870912 268435456 9007199254740992 Bool.false 1077755793978 4603 

noncomputable def Ns576p1715 := Ns576p1714 744261104 53 268435448 8 864060384 53 240095976 8 Bool.true 1088945807 77943 Bool.false 751639140 Bool.false 297093358 28296951008113761 1 Bool.false 91230840 Bool.false Bool.false 456744664 Bool.false Bool.true 839067961 

noncomputable def Ns576p1716 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 qz240) qz240 Real.sin Real.cos BSN.quadSignNeg BSN.quadSignNeg 1 2 3 989310 1000 841 586 536870912 268435456 9007199254740992 Bool.false 1077755793978 4603 

noncomputable def Ns576p1717 := Ns576p1716 372130544 53 379625064 8 589812976 53 309962568 8 Bool.true 536870584 4661 Bool.false 375531149 Bool.false 65412763 28296951008113761 1 Bool.false 345648690 Bool.true Bool.false 532890868 Bool.true Bool.true 1088945807 

noncomputable def Ns576p1718 := nat_lit 3390509647814380462864379869540025196806875509028073 

noncomputable def Ns576p1719 := nat_lit 1688941054120953734239852095789545142029280870400 

noncomputable def Ns576p1720 := nat_lit 454886987173963821122719248000000000 

noncomputable def Ns576p1721 := nat_lit 2700145793548462266670403561993280000000 

noncomputable abbrev qz801 := (@Eq.refl Real (Enclosure.sfrac Bool.false 989310 1000))

noncomputable abbrev qz728 := qz801

noncomputable abbrev qz542 := qz728

noncomputable abbrev qz243 := qz542

noncomputable def Ns576p1722 := BSN.riemannSiegelThetaApproximant_two_zero_mk qz240 989310 1000 3914938104400 16000000 1978620 4000 2000 Ns576p1720 Ns576p1721 qz243 rfl rfl rfl rfl rfl rfl rfl rfl rfl 

noncomputable def Ns576p1723 := nat_lit 9764667785705415733049414024275272566803801466000850240000000 

noncomputable abbrev qz729 := (@HSub.hSub Real Real Real qz747 qz748 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz749 (@Nat.cast Real Real.instNatCast 1978620))))

noncomputable abbrev qz543 := (@HSub.hSub Real Real Real qz594 (@HMul.hMul Real Real Real qz590 (Enclosure.sfrac Bool.false 989310 4000) (Real.log (Enclosure.sfrac Bool.false 3914938104400 16000000))) (@HMul.hMul Real Real Real qz590 qz595 qz729))

noncomputable abbrev qz730 := (Enclosure.sfrac Bool.false 989310 2000)

noncomputable abbrev qz244 := (@HSub.hSub Real Real Real qz359 (@HSub.hSub Real Real Real qz359 qz543 qz730) (@HMul.hMul Real Real Real qz355 qz730 (Real.log Real.pi)))

noncomputable def Ns576p1724 := @Enclosure.Real.IsNear.addLit_ft_p qz244 (Enclosure.sfrac Bool.true Ns576p1720 Ns576p1721) 3616348653649729544933 1801439850948198400 14043960453421317 1638400000000000000000 Ns576p1720 Ns576p1721 0 1 Ns576p1723 

noncomputable def Ns576p1725 := nat_lit 24268904997436280366769058611200 

noncomputable abbrev qz245 := (@HSub.hSub Real Real Real qz359 qz543 qz730)

noncomputable def Ns576p1726 := @Enclosure.Real.IsNear.subLit_ff_p qz245 (@HMul.hMul Real Real Real qz5 qz730 (Real.log Real.pi)) 4636407412039629529829 1801439850948198400 4869684461883 1600000000000000000 3800014996491 6710886400 296793 53687091200 Ns576p1725 3616348653649729544933 1801439850948198400 

noncomputable def Ns576p1727 := nat_lit 9272814824079259059658000 

noncomputable abbrev qz246 := qz543

noncomputable def Ns576p1728 := @Enclosure.Real.IsNear.subLit_ff_p qz246 qz730 5527498641510410609381 1801439850948198400 4869684461883 1600000000000000000 989310 2000 0 1 Ns576p1727 4636407412039629529829 1801439850948198400 4869684461883 1600000000000000000 

noncomputable def Ns576p1729 := nat_lit 12446820411098604036855077695010111488 

noncomputable def Ns576p1730 := nat_lit 120000117649616434309890048 

noncomputable def Ns576p1731 := nat_lit 163386374702442098362435750522268736938762586768296488598036361764104726359531739630602265405160010467911721859741484251984710352692226295618565863473414144000000000000000000000000000000 

noncomputable def Ns576p1732 := nat_lit 5271150987195718441375643563177276698099974550421508719610028240643085862863019736197837032238561723259152426075651237640336359488975766377962890756253286400000000000000000000000000000 

noncomputable def Ns576p1733 := nat_lit 581255071847069284639927401867794212228513321584917017427504812387905959511094902138684853250839146313281840250397496603727855138717248395715123609600000000000000000000000000000 

noncomputable def Ns576p1734 := BSN.log_dyadic_bound 1817786104400 6012090104400 8 7 Ns576p1731 268435456 81920000 Ns576p1732 Ns576p1733 167562588 7829876208800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 1817786104400) (BSN.artanhQ 6012090104400) 0 7 Ns576p1732 Ns576p1731 Ns576p1733 rfl rfl rfl rfl) rfl rfl rfl 

noncomputable abbrev qz544 := (Real.log (Enclosure.sfrac Bool.false 3914938104400 16000000))

noncomputable def Ns576p1735 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 989310 4000) qz544 989310 4000 0 1 55879409261800551 4503599627370496 48828193 4000000000000000 5528205837679190310981 1801439850948198400 4830621961683 1600000000000000000 (Enclosure.Real.IsNear.const Bool.false 989310 4000) (BSN.isNear_log_sfrac 3914938104400 16000000 55879409261800551 4503599627370496 48828193 4000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 3914938104400) qz362)) Bool.false Ns576p1730 Ns576p112 1000001392640000 81920000000000000000000 55879409261800551 4503599627370496 48828193 4000000000000000 (BSN.log_rat_reduce_isNear 3914938104400 16000000 17 7829876208800 4194304000000 167562588 268435456 24973259072661432 36028797018963968 81920000 1000000000000000 rfl rfl rfl rfl (Ns576p1734 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1736 := BSN.arctan_dyadic_bound_f 1000 1978620 1 0 33554432 10240000 0 1 1 0 1 1 16958 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1978620) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1978620) 0 0 rfl) rfl rfl rfl 

noncomputable def Ns576p1737 := @Enclosure.Real.IsNear.subLit_ff_p qz15 (Real.arctan (@HDiv.hDiv Real Real Real RSCompact.c0 qz16 (@Nat.cast Real Real.instNatCast 1978620))) 884279719003555 562949953421312 1 2000000000000000 16958 33554432 1 10240000 29661957194973775396864 883995210974627 562949953421312 195312501 2000000000000000 qz17 (Ns576p1736 rfl) rfl rfl 

noncomputable abbrev qz545 := (@HMul.hMul Real Real Real qz590 qz595 qz729)

noncomputable abbrev qz247 := qz545

noncomputable abbrev qz546 := qz729

noncomputable abbrev qz248 := qz546

noncomputable def Ns576p1738 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz5 (Enclosure.sfrac Bool.false 989310 4000) qz544) qz247 5528205837679190310981 1801439850948198400 4830621961683 1600000000000000000 883995210974627 2251799813685248 195312501 8000000000000000 Ns576p1729 5527498641510410609381 1801439850948198400 4869684461883 1600000000000000000 (Ns576p1735 rfl) (@Enclosure.Real.IsNear.mulLit_ff qz19 qz248 1 4 0 1 883995210974627 562949953421312 195312501 2000000000000000 883995210974627 2251799813685248 195312501 8000000000000000 qz369 Ns576p1737 rfl) 

noncomputable def Ns576p1739 := @Ns576p1724 Ns576p1718 Ns576p1719 14043960453421317 1638400000000000000000 (@Ns576p1726 14043960453421317 1638400000000000000000 (Ns576p1728 (Ns576p1738 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 989310 2000) rfl rfl) (@Enclosure.Real.IsNear.mulLit_ff qz730 (Real.log Real.pi) 989310 2000 0 1 38410761 33554432 3 268435456 3800014996491 6710886400 296793 53687091200 (Enclosure.Real.IsNear.const Bool.false 989310 2000) RS577to588.d5 rfl) rfl rfl) (Enclosure.Real.IsNear.const Bool.true Ns576p1720 Ns576p1721) 

noncomputable def Ns576p1740 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns576p1718 Ns576p1719 14043960453421317 1638400000000000000000 134719474247 67108864 9 1048576 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz370 qz244 (Enclosure.sfrac Bool.true Ns576p1720 Ns576p1721)) Bool.false Ns576p1718 Ns576p1719 14043960453421317 1638400000000000000000 Ns576p1722 (Ns576p1739 rfl rfl)) 

noncomputable def Ns576p1741 := nat_lit 15181133252409915965702144 

noncomputable def Ns576p1742 := nat_lit 14339918260521337984093928449857706428895337992422979424938158871635764834021570167557937606506062736501816445937758535114688232828479129849856 

noncomputable def Ns576p1743 := nat_lit 10164656365699597378961300447295050203504093923589197284025089530082683711182599015255368255118032261703295183531424451438851439590445056 

noncomputable def Ns576p1744 := nat_lit 71610745523513071506346624427588820179552354608965471550338322744172239125901496004769153515947327402754260778178470402720756959774568699990016 

noncomputable def Ns576p1745 := BSN.sin_dyadic_bound_f 215736879062 137438953472 4 3 67108864 20500001 Ns576p1742 Ns576p274 Ns576p1743 Ns576p1744 Ns576p277 Ns576p1743 67108823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 215736879062) qz371 0 3 Ns576p1742 Ns576p274 Ns576p1743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 215736879062) qz372 0 3 Ns576p1744 Ns576p277 Ns576p1743 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1746 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 qz240) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 134719474247) qz384) Bool.false 134719474247 67108864 9 1048576 Bool.true 67108823 67108864 1 10240000 (Ns576p1740 rfl) (Enclosure.sfrac_false_div 134719474247 67108864) (BSN.cos_reduce1 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 134719474247) qz384) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast Ns576p1741) qz386) 226375608064910080 72057594037927936 Bool.false 67108823 67108864 319 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q1 134719474247 67108864 226375608064910080 72057594037927936 319 Ns576p1741 Ns576p112 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 67108823 67108864 Ns576p1741 Ns576p112 215736879062 137438953472 20500001 20480000 (Ns576p1745 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1747 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 qz240) Bool.false Ns576p1718 Ns576p1719 14043960453421317 1638400000000000000000 1077755793978 536870912 4603 536870912 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 qz240) (@HAdd.hAdd Real Real Real qz370 qz244 (Enclosure.sfrac Bool.true Ns576p1720 Ns576p1721)) Bool.false Ns576p1718 Ns576p1719 14043960453421317 1638400000000000000000 Ns576p1722 (Ns576p1739 rfl rfl)) 

noncomputable def Ns576p1748 := Ns576p1717 77943 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 841 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 345648690 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat2 586 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 532890868 536870912) qz243 rfl rfl (@Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) Bool.true 67108823 67108864 5689 655360000 536870584 536870912 4661 536870912 (@Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 1) (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 67108823 67108864 5689 655360000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 qz240) qz240) (@Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 qz240)) Bool.true 67108823 67108864 93208576 10737418240000 67108823 67108864 5689 655360000 (Ns576p1746 rfl rfl) rfl)) rfl) (Ns576p1747 rfl) RS577to588.d7 

noncomputable def Ns576p1749 := nat_lit 4996656871497898017469303988834759733343519748661515198735588366980191265 

noncomputable def Ns576p1750 := nat_lit 395519343655538078730350125812384062971783063115838823953353733280801 

noncomputable def Ns576p1751 := nat_lit 13085841917842862031720708927696864965512025978677971305259187912237093921 

noncomputable def Ns576p1752 := BSN.sin_dyadic_bound_f 375531149 536870912 3 2 536870912 268435456 Ns576p1749 Ns576p151 Ns576p1750 Ns576p1751 Ns576p154 Ns576p1750 345648690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 375531149) qz375 0 2 Ns576p1749 Ns576p151 Ns576p1750 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 375531149) qz376 0 2 Ns576p1751 Ns576p154 Ns576p1750 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1753 := nat_lit 18308382431720168996522829400561 

noncomputable def Ns576p1754 := BSN.cos_dyadic_bound_f 65412763 536870912 2 1 536870912 268435456 Ns576p1753 Ns576p318 Ns576p1753 Ns576p1753 Ns576p319 Ns576p1753 532890868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 65412763) qz377 0 1 Ns576p1753 Ns576p318 Ns576p1753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 65412763) qz378 0 1 Ns576p1753 Ns576p319 Ns576p1753 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1755 := nat_lit 44067117396726192950717375625617367509894714257391797400550718402658018659628478498911774832387022263681024000000 

noncomputable def Ns576p1756 := nat_lit 32517162675193515486563588403474155876430677988003049797208742373283756149400823292661302890496000000000000 

noncomputable def Ns576p1757 := nat_lit 266933688903289231457691591662807896218289778076590023471142289530517723086089545715405721562465223449614745600000 

noncomputable def Ns576p1758 := BSN.cos_dyadic_bound_f 751639140 536870912 4 3 536870912 268435456 Ns576p1755 Ns576p162 Ns576p1756 Ns576p1757 Ns576p165 Ns576p1756 91230840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 751639140) qz377 0 3 Ns576p1755 Ns576p162 Ns576p1756 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 751639140) qz378 0 3 Ns576p1757 Ns576p165 Ns576p1756 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1759 := nat_lit 1087388636629828421824439336815762267705446906626085739109745766352240896 

noncomputable def Ns576p1760 := nat_lit 60693689768978717044842173287675160599683840095612298163682115010816 

noncomputable def Ns576p1761 := nat_lit 3262044522509947308039228326100711452795141352198065992732909934826701056 

noncomputable def Ns576p1762 := BSN.cos_dyadic_bound_f 297093358 536870912 3 2 536870912 268435456 Ns576p1759 Ns576p141 Ns576p1760 Ns576p1761 Ns576p144 Ns576p1760 456744664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 297093358) qz377 0 2 Ns576p1759 Ns576p141 Ns576p1760 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 297093358) qz378 0 2 Ns576p1761 Ns576p144 Ns576p1760 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1763 := Ns576p1715 131989 BSN.abs_quadSignPos (BSN.cos_quad_nat0 404 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 91230840 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 264 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 456744664 536870912) qz243 rfl rfl (Ns576p1748 RS577to588.d9 RS577to588.d11 RS577to588.d13 RS577to588.d17 (Ns576p1752 rfl rfl) (Ns576p1754 rfl rfl) rfl rfl rfl rfl rfl rfl) (Ns576p1747 rfl) RS577to588.d19 RS577to588.d21 RS577to588.d23 RS577to588.d25 RS577to588.d17 (Ns576p1758 rfl rfl) (Ns576p1762 rfl rfl) rfl rfl rfl rfl 

noncomputable def Ns576p1764 := nat_lit 9548675693908033684944478035551888961267990939121018416120901294780965120 

noncomputable def Ns576p1765 := nat_lit 1444216615052449609770531802479979522650829573250481365550548300718336 

noncomputable def Ns576p1766 := nat_lit 25006098085715717589772099708289027312665208259341214120010516789082317056 

noncomputable def Ns576p1767 := BSN.sin_dyadic_bound_f 441523722 536870912 3 2 536870912 268435456 Ns576p1764 Ns576p151 Ns576p1765 Ns576p1766 Ns576p154 Ns576p1765 393409570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 441523722) qz375 0 2 Ns576p1764 Ns576p151 Ns576p1765 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 441523722) qz376 0 2 Ns576p1766 Ns576p154 Ns576p1765 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1768 := nat_lit 2580936125098684801997569597477345579276800154381365329886234663882217281 

noncomputable def Ns576p1769 := nat_lit 341870710451752393848001957447939533269432052073751563689787056084801 

noncomputable def Ns576p1770 := nat_lit 7742124633875150901205012788517140858763861599039948486531324417534482241 

noncomputable def Ns576p1771 := BSN.cos_dyadic_bound_f 368750601 536870912 3 2 536870912 268435456 Ns576p1768 Ns576p141 Ns576p1769 Ns576p1770 Ns576p144 Ns576p1769 415133454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 368750601) qz377 0 2 Ns576p1768 Ns576p141 Ns576p1769 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 368750601) qz378 0 2 Ns576p1770 Ns576p144 Ns576p1769 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1772 := Ns576p1713 177629 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 149 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 393409570 536870912) BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 415133454 536870912) qz243 rfl rfl (Ns576p1763 rfl rfl) (Ns576p1747 rfl) RS577to588.d27 RS577to588.d29 RS577to588.d31 RS577to588.d33 RS577to588.d17 (Ns576p1767 rfl rfl) (Ns576p1771 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1773 := nat_lit 24521617846456492199896923128951652923949121752754499937816940980158306145 

noncomputable def Ns576p1774 := nat_lit 9520031695120747223215010272911949204633394286808093113390457284433761 

noncomputable def Ns576p1775 := nat_lit 64207871451308236456606736273479138311630674333130762924479832302906480481 

noncomputable def Ns576p1776 := BSN.sin_dyadic_bound_f 558894453 536870912 3 2 536870912 268435456 Ns576p1773 Ns576p151 Ns576p1774 Ns576p1775 Ns576p154 Ns576p1774 463277267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 558894453) qz375 0 2 Ns576p1773 Ns576p151 Ns576p1774 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 558894453) qz376 0 2 Ns576p1775 Ns576p154 Ns576p1774 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1777 := nat_lit 92078890217254039950254546696265056319233208133795700746523157993940547312888989916817065781125532704756333682801 

noncomputable def Ns576p1778 := nat_lit 16942382482510021626678617170475240186391509613168820324204636387413279613314201042490319399852730979852401 

noncomputable def Ns576p1779 := nat_lit 460103713903658283849249731793617307536474162419095783072330705872656010719603171337818829392088182464449121230961 

noncomputable def Ns576p1780 := BSN.sin_dyadic_bound_f 711892701 536870912 4 3 536870912 268435456 Ns576p1777 Ns576p135 Ns576p1778 Ns576p1779 Ns576p138 Ns576p1778 520865475 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 711892701) qz375 0 3 Ns576p1777 Ns576p135 Ns576p1778 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 711892701) qz376 0 3 Ns576p1779 Ns576p138 Ns576p1778 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1781 := Ns576p1711 217506 BSN.abs_quadSignPos (BSN.cos_quad_nat3 31 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 463277267 536870912) BSN.abs_quadSignNeg (BSN.cos_quad_nat1 105 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 520865475 536870912) qz243 rfl rfl (Ns576p1772 rfl) (Ns576p1747 rfl) RS577to588.d35 RS577to588.d37 RS577to588.d39 RS577to588.d41 RS577to588.d17 (Ns576p1776 rfl rfl) (Ns576p1780 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1782 := nat_lit 116914344213836433841756716993751391483629737721740329620032721884610816 

noncomputable def Ns576p1783 := nat_lit 701702179307938310210004270569177311052926405512751253387444551936 

noncomputable def Ns576p1784 := nat_lit 350741629237150685648649730972713036096267107312409963357591390764728576 

noncomputable def Ns576p1785 := BSN.cos_dyadic_bound_f 170125378 536870912 3 2 536870912 268435456 Ns576p1782 Ns576p141 Ns576p1783 Ns576p1784 Ns576p144 Ns576p1783 510140777 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 170125378) qz377 0 2 Ns576p1782 Ns576p141 Ns576p1783 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 170125378) qz378 0 2 Ns576p1784 Ns576p144 Ns576p1783 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1786 := nat_lit 195660895379468245356408659239693736407782441673440582107129819712758016 

noncomputable def Ns576p1787 := nat_lit 1965268039122422265278663628768346050372811829747973184946321531136 

noncomputable def Ns576p1788 := nat_lit 586978755602326491224695420391823672531246579396662250375019566495211776 

noncomputable def Ns576p1789 := BSN.cos_dyadic_bound_f 193498554 536870912 3 2 536870912 268435456 Ns576p1786 Ns576p141 Ns576p1787 Ns576p1788 Ns576p144 Ns576p1787 502376466 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 193498554) qz377 0 2 Ns576p1786 Ns576p141 Ns576p1787 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 193498554) qz378 0 2 Ns576p1788 Ns576p144 Ns576p1787 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1790 := Ns576p1709 253370 BSN.abs_quadSignPos (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 510140777 536870912) BSN.abs_quadSignPos qz658 (BSN.sfrac_eq_quadSignPos_mul Bool.false 502376466 536870912) qz243 rfl rfl (Ns576p1781 rfl) (Ns576p1747 rfl) RS577to588.d43 RS577to588.d45 RS577to588.d47 RS577to588.d49 RS577to588.d17 (Ns576p1785 rfl rfl) (Ns576p1789 rfl rfl) rfl rfl rfl rfl rfl 

noncomputable def Ns576p1791 := nat_lit 435036519528101219471086037281 

noncomputable def Ns576p1792 := BSN.sin_dyadic_bound_f 25682153 536870912 2 1 536870912 268435456 Ns576p1791 Ns576p300 Ns576p1791 Ns576p1791 Ns576p301 Ns576p1791 25672359 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 25682153) qz375 0 1 Ns576p1791 Ns576p300 Ns576p1791 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 25682153) qz376 0 1 Ns576p1791 Ns576p301 Ns576p1791 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1793 := Ns576p1707 Bool.true 539806733 253370 Bool.true 25682153 28296951008113761 1 Bool.false 25672359 Bool.false Bool.true 532395762 270131 BSN.abs_quadSignPos qz379 (BSN.sfrac_eq_quadSignPos_mul Bool.false 25672359 536870912) qz243 rfl (Ns576p1790 rfl) (Ns576p1747 rfl) RS577to588.d51 RS577to588.d53 RS577to588.d17 (Ns576p1792 rfl rfl) rfl 

noncomputable def Ns576p1794 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) 532395762 536870912 270131 536870912 532395762 536870912 270131 536870912 571655596579749888 266197881 134217728 270131 268435456 (Ns576p1793 rfl rfl rfl rfl) 

noncomputable def Ns576p1795 := @Enclosure.Real.IsNear.mulLit_ff qz727 (Zeta.RiemannSiegel.correction qz242) 4736219 16777216 1 33554432 108855607084603 281474976710656 1743552780637 175921860444160000 515563994530631336057 4722366482869645213696 

noncomputable abbrev qz731 := (@HPow.hPow Real Real Real qz7 qz241 qz9)

noncomputable def Ns576p1796 := @Enclosure.Real.IsNear.mulLit_ff qz6 qz731 1 1 0 1 4736219 16777216 1 33554432 4736219 16777216 1 33554432 

noncomputable def Ns576p1797 := @Enclosure.Real.IsNear.sqrt_image qz241 1056653024217 6710886400 98931 6710886400 421042686 421042726 33554432 (@Enclosure.Real.IsNear.of_eq qz241 (@HMul.hMul Real Real Real qz5 qz240 qz3) Bool.false 1056653024217 6710886400 98931 6710886400 (BSN.t_div_two_pi_mk qz240 989310 1000 qz243) (@Enclosure.Real.IsNear.mulLit_ff qz240 qz3 989310 1000 0 1 10680707 67108864 1 67108864 1056653024217 6710886400 98931 6710886400 (Enclosure.Real.IsNear.const Bool.false 989310 1000) RS577to588.d56 rfl)) 

noncomputable abbrev qz802 := (Real.sqrt (@HDiv.hDiv Real Real Real RSCompact.c0 (Enclosure.sfrac Bool.false 989310 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)))

noncomputable abbrev qz732 := qz802

noncomputable abbrev qz547 := qz732

noncomputable abbrev qz249 := qz547

noncomputable def Ns576p1798 := @Enclosure.Real.IsNear.sqrt_image qz249 210521353 16777216 5 8388608 118860625 118860631 33554432 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 842085412 67108864 40 67108864 210521353 16777216 5 8388608 (Ns576p1797 rfl rfl rfl rfl rfl rfl) rfl) rfl 

noncomputable def Ns576p1799 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz249) 29715157 8388608 3 33554432 9472437 9472439 33554432 (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz249) Bool.false 237721256 67108864 6 67108864 29715157 8388608 3 33554432 (Ns576p1798 rfl rfl rfl rfl rfl) rfl) 

noncomputable def Ns576p1800 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 18944876 67108864 2 67108864 4736219 16777216 1 33554432 (Ns576p1799 rfl rfl rfl rfl rfl rfl) rfl 

noncomputable abbrev qz250 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz541))

noncomputable abbrev qz733 := (@HMul.hMul Real Real Real qz743 qz800 qz800)

noncomputable abbrev qz548 := (@HSub.hSub Real Real Real qz594 (@HSub.hSub Real Real Real qz594 qz733 qz726) qz605)

noncomputable abbrev qz251 := (Real.cos (@HMul.hMul Real Real Real qz355 qz352 qz548))

noncomputable def Ns576p1801 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction qz242) (@HMul.hMul Real Real Real qz5 (@Inv.inv Real Real.instInv qz250) qz251) Bool.false 108855607084603 

noncomputable def Ns576p1802 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv qz250) qz251 70287967 67108864 285 

noncomputable abbrev qz734 := (@Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg qz250))

noncomputable def Ns576p1803 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv qz250) (@Neg.neg Real Real.instNeg qz734) Bool.true 70287967 67108864 285 67108864 (BSN.inv_eq_neg_inv_neg qz250) 

noncomputable def Ns576p1804 := @Enclosure.Real.IsNear.recentre' qz734 Bool.false 70287967 67108864 285 67108864 70287967 67108864 

noncomputable def Ns576p1805 := @Enclosure.Real.IsNear.recentre' qz250 Bool.true 64073551 67108864 2657828864 687194767360000 64073551 67108864 162221 41943040000 

noncomputable abbrev qz252 := (@HMul.hMul Real Real Real qz355 qz352 qz541)

noncomputable def Ns576p1806 := @Enclosure.Real.IsNear.cos_image qz252 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 57772387) qz629) Bool.false 57772387 16777216 253 67108864 Bool.true 64073551 67108864 1 

noncomputable def Ns576p1807 := nat_lit 134930377084711425065381091 

noncomputable def Ns576p1808 := @Enclosure.Real.IsNear.mulLit_ff qz2 qz242 884279719003555 140737488355328 1 500000000000000 9194761 16777216 5 8388608 8130740673384846375355 2361183241434822606848 Ns576p1807 

noncomputable def Ns576p1809 := @Enclosure.Real.IsNear.subLit_ff_p qz249 qz1 210521353 16777216 5 8388608 12 1 0 1 9194761 9194761 16777216 5 

noncomputable def Ns576p1810 := @Ns576p1809 8388608 (@Enclosure.Real.IsNear.recentre' qz249 Bool.false 842085412 67108864 40 67108864 210521353 16777216 5 8388608 (Ns576p1797 rfl rfl rfl rfl rfl rfl) rfl) qz385 

noncomputable def Ns576p1811 := @Enclosure.Real.IsNear.recentre' qz252 Bool.false 8130740673384846375355 2361183241434822606848 Ns576p1807 Ns576p202 57772387 16777216 253 67108864 (@Ns576p1808 Ns576p202 RS577to588.d55 (Ns576p1810 rfl rfl) rfl) 

noncomputable def Ns576p1812 := nat_lit 2964483729632873471823497401869596925610561 

noncomputable def Ns576p1813 := BSN.cos_dyadic_bound_f 41494187759 137438953472 2 1 67108864 20500001 Ns576p1812 Ns576p1164 Ns576p1812 Ns576p1812 Ns576p1165 Ns576p1812 64073551 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 41494187759) qz443 0 1 Ns576p1812 Ns576p1164 Ns576p1812 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 41494187759) qz444 0 1 Ns576p1812 Ns576p1165 Ns576p1812 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1814 := @Ns576p1806 10240000 (Ns576p1811 rfl) (Enclosure.sfrac_false_div 57772387 16777216) (BSN.cos_reduce2 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 57772387) qz629) (@HDiv.hDiv Real Real Real RSCompact.c0 (@Nat.cast Real Real.instNatCast 729973470823453927931904) (@Nat.cast Real Real.instNatCast Ns576p513)) 226375608064910080 72057594037927936 Bool.false 64073551 67108864 0 1000000000000000 20480000 10240000 (BSN.sin_reduce_arg_pos_rat_q2 57772387 16777216 226375608064910080 72057594037927936 0 729973470823453927931904 Ns576p513 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 64073551 67108864 729973470823453927931904 Ns576p513 41494187759 137438953472 20500001 20480000 (Ns576p1813 rfl rfl) rfl) rfl rfl rfl rfl) 

noncomputable def Ns576p1815 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg qz250) 64073551 67108864 162221 41943040000 35143841 35144126 33554432 (@Enclosure.Real.IsNear.neg qz250 Bool.true 64073551 67108864 162221 41943040000 (Ns576p1805 (Ns576p1814 rfl rfl) rfl)) 

noncomputable def Ns576p1816 := Ns576p1803 (@Enclosure.Real.IsNear.neg qz734 Bool.false 70287967 67108864 285 67108864 (@Ns576p1804 285 67108864 (Ns576p1815 rfl rfl rfl rfl rfl rfl) rfl)) 

noncomputable def Ns576p1817 := @Enclosure.Real.IsNear.recentre' qz251 Bool.true 12389672 33554432 

noncomputable abbrev qz253 := (@HMul.hMul Real Real Real qz355 qz352 qz548)

noncomputable def Ns576p1818 := @Enclosure.Real.IsNear.cos_image qz253 (@HDiv.hDiv Real Real Real RSCompact.c0 (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 130794403)) qz384) Bool.true 130794403 67108864 

noncomputable def Ns576p1819 := nat_lit 77207388604624737543534295405 

noncomputable def Ns576p1820 := nat_lit 1186265641867310607743383563738549 

noncomputable def Ns576p1821 := @Enclosure.Real.IsNear.recentre' qz253 Bool.true Ns576p1819 Ns576p524 Ns576p1820 

noncomputable abbrev qz254 := qz548

noncomputable def Ns576p1822 := @Enclosure.Real.IsNear.mulLit_ft qz2 qz254 884279719003555 140737488355328 1 500000000000000 87311047562671 

noncomputable abbrev qz549 := (@HSub.hSub Real Real Real qz594 qz733 qz726)

noncomputable abbrev qz255 := qz549

noncomputable def Ns576p1823 := @Enclosure.Real.IsNear.subLit_tf qz255 qz31 69718861518255 281474976710656 43958435 35184372088832 1 16 

noncomputable abbrev qz550 := qz733

noncomputable abbrev qz256 := qz550

noncomputable def Ns576p1824 := @Enclosure.Real.IsNear.subLit_ff_n qz256 qz242 84543629847121 281474976710656 22986915 35184372088832 9194761 16777216 5 8388608 

noncomputable def Ns576p1825 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 9194761 16777216 5 8388608 9194761 16777216 5 8388608 84543629847121 281474976710656 

noncomputable def Ns576p1826 := nat_lit 2423483421533933358279486614552213050628102545363025509491928323754474833605362673318796739423222942321 

noncomputable def Ns576p1827 := nat_lit 25065127543065666453578869068732411836337124756472886947747685219870128502410527109193426485693041 

noncomputable def Ns576p1828 := nat_lit 14618873374174761139429387527019300572517325464247860809655973615508853838317746392391351642860801280625 

noncomputable def Ns576p1829 := BSN.cos_dyadic_bound_t 130794403 67108864 4 3 33554432 10240000 Ns576p1826 Ns576p227 Ns576p1827 Ns576p1828 Ns576p230 Ns576p1827 12389672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 130794403) qz606 0 3 Ns576p1826 Ns576p227 Ns576p1827 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 130794403) (BSN.cosOddQ 67108864) 0 3 Ns576p1828 Ns576p230 Ns576p1827 rfl rfl rfl rfl) rfl rfl 

noncomputable def Ns576p1830 := @Ns576p1817 342114304 42949672960000 1548709 4194304 20881 2621440000 (@Ns576p1818 33 4194304 Bool.true 12389672 33554432 1 10240000 (@Ns576p1821 Ns576p527 130794403 67108864 33 4194304 (@Ns576p1822 281474976710656 43958435 35184372088832 Ns576p1819 Ns576p524 Ns576p1820 Ns576p527 RS577to588.d55 (@Ns576p1823 0 1 1396976761002736 87311047562671 281474976710656 43958435 35184372088832 (@Ns576p1824 1169688398965852078080 69718861518255 281474976710656 43958435 35184372088832 (@Ns576p1825 22986915 35184372088832 (Ns576p1810 rfl rfl) (Ns576p1810 rfl rfl) rfl) (Ns576p1810 rfl rfl) rfl rfl) qz390 rfl rfl) rfl) rfl) (Enclosure.sfrac_true_div 130794403 67108864) (BSN.cos_neg_of_bound 130794403 67108864 Bool.true 12389672 33554432 1 10240000 (Ns576p1829 rfl rfl)) rfl rfl) 

noncomputable def Ns576p1831 := @Ns576p1795 8291866056146120259 Ns576p1704 (Ns576p1796 qz33 (@Enclosure.Real.IsNear.of_eq qz731 (@Inv.inv Real Real.instInv (Real.sqrt qz249)) Bool.false 4736219 16777216 1 33554432 (BSN.rpow_neg_quarter_mk qz241 (BSN.t_div_two_pi_nonneg qz240 989310 1000 qz243)) Ns576p1800) rfl) (@Ns576p1801 281474976710656 1743552780637 175921860444160000 (BSN.correction_mk qz242 (BSN.cos_two_pi_p_ne_zero_mk qz240 989310 1000 12 qz243 rfl rfl (@BSN.floor_sqrt_eq_dec qz240 989310 1000 12 qz243 rfl rfl rfl))) (@Ns576p1802 67108864 1548709 4194304 20881 2621440000 108855607084603 281474976710656 1743552780637 175921860444160000 Ns576p1816 (Ns576p1830 rfl) rfl)) 

noncomputable def Ns576p1832 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (hardyZApproximantRS₀ qz240) Bool.true 9881569288893253501049 4722366482869645213696 2978413621283732680259 Ns576p1704 (@Eq.refl Real (hardyZApproximantRS₀ qz240)) (@Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ qz240) (@HSub.hSub Real Real Real qz34 (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HMul.hMul Real Real Real qz5 qz727 (Zeta.RiemannSiegel.correction qz242))) Bool.true 9881569288893253501049 4722366482869645213696 2978413621283732680259 Ns576p1704 (BSN.hardyZApproximantRS₀_eq qz240 12 (@BSN.floor_sqrt_eq_dec qz240 989310 1000 12 qz243 rfl rfl rfl)) (@Ns576p1706 9881569288893253501049 4722366482869645213696 2978413621283732680259 Ns576p1704 (@Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (@HAdd.hAdd Real Real Real qz370 (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 qz240) qz240 12)) Bool.true 266197881 134217728 270131 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 qz240) qz240 12) (Ns576p1794 (Ns576p1793 rfl rfl rfl rfl) rfl rfl)) (Ns576p1831 rfl) rfl rfl)) 

theorem RS577to588.d71 : Enclosure.Real.IsNear (hardyZApproximantRS₀ qz240) Bool.true 9881569288893253501049 4722366482869645213696 2978413621283732680259 Ns576p1704 := Ns576p1832 

noncomputable def RS577to588.d72 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J)) 

noncomputable abbrev qz551 := (RS577to588.d3 qz589 qz607 (@Enclosure.dec_le_dec qz589 qz607 974151 1000 975630 1000 (@Eq.refl Real qz589) qz611 rfl rfl rfl))

noncomputable abbrev qz257 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz551)

noncomputable def Ns576p1833 := @Enclosure.Real.IsNear.of_eq qz257 (hardyZApproximantRS₀ qz4) Bool.true 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns576p85 

noncomputable abbrev qz552 := (@Enclosure.dec_le_dec qz589 qz607 974151 1000 975630 1000 (@Eq.refl Real qz589) qz611 rfl rfl rfl)

noncomputable abbrev qz258 := qz552

noncomputable def Ns576p1834 := @Enclosure.Real.IsNear.neg_val qz257 36351216173365039849207 75557863725914323419136 9383457302876000635589 Ns576p85 (Ns576p1833 (RS577to588.d4 qz4 qz35 qz258) RS577to588.d57) rfl 

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz551)

noncomputable def Ns576p1835 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantRS₀ qz35) Bool.false 55270813313427474824165 37778931862957161709568 4698652088383815387969 Ns576p235 

noncomputable def Ns576p1836 := @Enclosure.Real.IsNear.pos_val qz259 55270813313427474824165 37778931862957161709568 4698652088383815387969 Ns576p235 (Ns576p1835 (RS577to588.d58 qz4 qz35 qz258) RS577to588.d59) rfl 

noncomputable def Ns576p1837 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz257 qz4 qz4 974151 1000 974151 1000 

noncomputable def Ns576p1838 := @Enclosure.norm_gt_of_isNear qz257 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 36351216173365039849207 75557863725914323419136 9383457302876000635589 

noncomputable def Ns576p1839 := @Ns576p1838 Ns576p85 440358589 10737418240 1213 10737418240 (Ns576p1833 (RS577to588.d4 qz4 qz35 qz258) RS577to588.d57) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1840 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz259 qz4 qz35 974151 1000 975630 1000 

noncomputable def Ns576p1841 := @Enclosure.norm_gt_of_isNear qz259 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 55270813313427474824165 37778931862957161709568 4698652088383815387969 

noncomputable def Ns576p1842 := @Ns576p1841 Ns576p235 440358589 10737418240 1213 10737418240 (Ns576p1835 (RS577to588.d58 qz4 qz35 qz258) RS577to588.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz260 := qz551

noncomputable def Ns576p1843 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz260 (@BSN.thirtyTwoPi_le_dec qz4 974151 1000 qz11 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz257 qz259 (Ns576p1834 rfl rfl) (Ns576p1836 rfl rfl)) (Ns576p1837 qz11 qz11 rfl rfl rfl rfl (Ns576p1839 rfl)) (Ns576p1840 qz11 qz38 rfl rfl rfl rfl (Ns576p1842 rfl)) 

noncomputable abbrev qz553 := (RS577to588.d3 qz607 qz619 (@Enclosure.dec_le_dec qz607 qz619 975630 1000 976875 1000 qz611 qz623 rfl rfl rfl))

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz553)

noncomputable def Ns576p1844 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantRS₀ qz35) Bool.false 55270813313427474824165 37778931862957161709568 4698652088383815387969 Ns576p235 

noncomputable abbrev qz554 := (@Enclosure.dec_le_dec qz607 qz619 975630 1000 976875 1000 qz611 qz623 rfl rfl rfl)

noncomputable abbrev qz262 := qz554

noncomputable def Ns576p1845 := @Enclosure.Real.IsNear.pos_val qz261 55270813313427474824165 37778931862957161709568 4698652088383815387969 Ns576p235 (Ns576p1844 (RS577to588.d4 qz35 qz62 qz262) RS577to588.d59) rfl 

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz553)

noncomputable def Ns576p1846 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantRS₀ qz62) Bool.true 25918692323025086148841 151115727451828646838272 18818879020405043772507 Ns576p407 

noncomputable def Ns576p1847 := @Enclosure.Real.IsNear.neg_val qz263 25918692323025086148841 151115727451828646838272 18818879020405043772507 Ns576p407 (Ns576p1846 (RS577to588.d58 qz35 qz62 qz262) RS577to588.d61) rfl 

noncomputable def Ns576p1848 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz261 qz4 qz35 974151 1000 975630 1000 

noncomputable def Ns576p1849 := @Enclosure.norm_gt_of_isNear qz261 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 55270813313427474824165 37778931862957161709568 4698652088383815387969 

noncomputable def Ns576p1850 := @Ns576p1849 Ns576p235 440358589 10737418240 1213 10737418240 (Ns576p1844 (RS577to588.d4 qz35 qz62 qz262) RS577to588.d59) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1851 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz263 qz4 qz62 974151 1000 976875 1000 

noncomputable def Ns576p1852 := @Enclosure.norm_gt_of_isNear qz263 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 25918692323025086148841 151115727451828646838272 18818879020405043772507 

noncomputable def Ns576p1853 := @Ns576p1852 Ns576p407 440358589 10737418240 1213 10737418240 (Ns576p1846 (RS577to588.d58 qz35 qz62 qz262) RS577to588.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz264 := qz553

noncomputable def Ns576p1854 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz264 (@BSN.thirtyTwoPi_le_dec qz35 975630 1000 qz38 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz261 qz263 (Ns576p1845 rfl rfl) (Ns576p1847 rfl rfl)) (Ns576p1848 qz11 qz38 rfl rfl rfl rfl (Ns576p1850 rfl)) (Ns576p1851 qz11 qz65 rfl rfl rfl rfl (Ns576p1853 rfl)) 

noncomputable abbrev qz555 := (RS577to588.d3 qz619 qz630 (@Enclosure.dec_le_dec qz619 qz630 976875 1000 978120 1000 qz623 qz634 rfl rfl rfl))

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz555)

noncomputable def Ns576p1855 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantRS₀ qz62) Bool.true 25918692323025086148841 151115727451828646838272 18818879020405043772507 Ns576p407 

noncomputable abbrev qz556 := (@Enclosure.dec_le_dec qz619 qz630 976875 1000 978120 1000 qz623 qz634 rfl rfl rfl)

noncomputable abbrev qz266 := qz556

noncomputable def Ns576p1856 := @Enclosure.Real.IsNear.neg_val qz265 25918692323025086148841 151115727451828646838272 18818879020405043772507 Ns576p407 (Ns576p1855 (RS577to588.d4 qz62 qz80 qz266) RS577to588.d61) rfl 

noncomputable abbrev qz267 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz555)

noncomputable def Ns576p1857 := @Enclosure.Real.IsNear.of_eq qz267 (hardyZApproximantRS₀ qz80) Bool.false 96764181858336812538967 18889465931478580854784 1884334343736672412261 Ns576p539 

noncomputable def Ns576p1858 := @Enclosure.Real.IsNear.pos_val qz267 96764181858336812538967 18889465931478580854784 1884334343736672412261 Ns576p539 (Ns576p1857 (RS577to588.d58 qz62 qz80 qz266) RS577to588.d62) rfl 

noncomputable def Ns576p1859 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz265 qz4 qz62 974151 1000 976875 1000 

noncomputable def Ns576p1860 := @Enclosure.norm_gt_of_isNear qz265 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 25918692323025086148841 151115727451828646838272 18818879020405043772507 

noncomputable def Ns576p1861 := @Ns576p1860 Ns576p407 440358589 10737418240 1213 10737418240 (Ns576p1855 (RS577to588.d4 qz62 qz80 qz266) RS577to588.d61) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1862 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz267 qz4 qz80 974151 1000 978120 1000 

noncomputable def Ns576p1863 := @Enclosure.norm_gt_of_isNear qz267 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 96764181858336812538967 18889465931478580854784 1884334343736672412261 

noncomputable def Ns576p1864 := @Ns576p1863 Ns576p539 440358589 10737418240 1213 10737418240 (Ns576p1857 (RS577to588.d58 qz62 qz80 qz266) RS577to588.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz268 := qz555

noncomputable def Ns576p1865 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz268 (@BSN.thirtyTwoPi_le_dec qz62 976875 1000 qz65 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz265 qz267 (Ns576p1856 rfl rfl) (Ns576p1858 rfl rfl)) (Ns576p1859 qz11 qz65 rfl rfl rfl rfl (Ns576p1861 rfl)) (Ns576p1862 qz11 qz83 rfl rfl rfl rfl (Ns576p1864 rfl)) 

noncomputable abbrev qz557 := (RS577to588.d3 qz630 qz641 (@Enclosure.dec_le_dec qz630 qz641 978120 1000 979365 1000 qz634 qz645 rfl rfl rfl))

noncomputable abbrev qz269 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz557)

noncomputable def Ns576p1866 := @Enclosure.Real.IsNear.of_eq qz269 (hardyZApproximantRS₀ qz80) Bool.false 96764181858336812538967 18889465931478580854784 1884334343736672412261 Ns576p539 

noncomputable abbrev qz558 := (@Enclosure.dec_le_dec qz630 qz641 978120 1000 979365 1000 qz634 qz645 rfl rfl rfl)

noncomputable abbrev qz270 := qz558

noncomputable def Ns576p1867 := @Enclosure.Real.IsNear.pos_val qz269 96764181858336812538967 18889465931478580854784 1884334343736672412261 Ns576p539 (Ns576p1866 (RS577to588.d4 qz80 qz98 qz270) RS577to588.d62) rfl 

noncomputable abbrev qz271 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz557)

noncomputable def Ns576p1868 := @Enclosure.Real.IsNear.of_eq qz271 (hardyZApproximantRS₀ qz98) Bool.true 88668148093711940251019 18889465931478580854784 2358344169359756984347 Ns576p675 

noncomputable def Ns576p1869 := @Enclosure.Real.IsNear.neg_val qz271 88668148093711940251019 18889465931478580854784 2358344169359756984347 Ns576p675 (Ns576p1868 (RS577to588.d58 qz80 qz98 qz270) RS577to588.d63) rfl 

noncomputable def Ns576p1870 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz269 qz4 qz80 974151 1000 978120 1000 

noncomputable def Ns576p1871 := @Enclosure.norm_gt_of_isNear qz269 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 96764181858336812538967 18889465931478580854784 1884334343736672412261 

noncomputable def Ns576p1872 := @Ns576p1871 Ns576p539 440358589 10737418240 1213 10737418240 (Ns576p1866 (RS577to588.d4 qz80 qz98 qz270) RS577to588.d62) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1873 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz271 qz4 qz98 974151 1000 979365 1000 

noncomputable def Ns576p1874 := @Enclosure.norm_gt_of_isNear qz271 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 88668148093711940251019 18889465931478580854784 2358344169359756984347 

noncomputable def Ns576p1875 := @Ns576p1874 Ns576p675 440358589 10737418240 1213 10737418240 (Ns576p1868 (RS577to588.d58 qz80 qz98 qz270) RS577to588.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz272 := qz557

noncomputable def Ns576p1876 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz272 (@BSN.thirtyTwoPi_le_dec qz80 978120 1000 qz83 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz269 qz271 (Ns576p1867 rfl rfl) (Ns576p1869 rfl rfl)) (Ns576p1870 qz11 qz83 rfl rfl rfl rfl (Ns576p1872 rfl)) (Ns576p1873 qz11 qz101 rfl rfl rfl rfl (Ns576p1875 rfl)) 

noncomputable abbrev qz559 := (RS577to588.d3 qz641 qz651 (@Enclosure.dec_le_dec qz641 qz651 979365 1000 980609 1000 qz645 qz655 rfl rfl rfl))

noncomputable abbrev qz273 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz559)

noncomputable def Ns576p1877 := @Enclosure.Real.IsNear.of_eq qz273 (hardyZApproximantRS₀ qz98) Bool.true 88668148093711940251019 18889465931478580854784 2358344169359756984347 Ns576p675 

noncomputable abbrev qz560 := (@Enclosure.dec_le_dec qz641 qz651 979365 1000 980609 1000 qz645 qz655 rfl rfl rfl)

noncomputable abbrev qz274 := qz560

noncomputable def Ns576p1878 := @Enclosure.Real.IsNear.neg_val qz273 88668148093711940251019 18889465931478580854784 2358344169359756984347 Ns576p675 (Ns576p1877 (RS577to588.d4 qz98 qz116 qz274) RS577to588.d63) rfl 

noncomputable abbrev qz275 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz559)

noncomputable def Ns576p1879 := @Enclosure.Real.IsNear.of_eq qz275 (hardyZApproximantRS₀ qz116) Bool.false 8639906495997731194617 75557863725914323419136 47227162783865831128697 Ns576p803 

noncomputable def Ns576p1880 := @Enclosure.Real.IsNear.pos_val qz275 8639906495997731194617 75557863725914323419136 47227162783865831128697 Ns576p803 (Ns576p1879 (RS577to588.d58 qz98 qz116 qz274) RS577to588.d64) rfl 

noncomputable def Ns576p1881 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz273 qz4 qz98 974151 1000 979365 1000 

noncomputable def Ns576p1882 := @Enclosure.norm_gt_of_isNear qz273 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 88668148093711940251019 18889465931478580854784 2358344169359756984347 

noncomputable def Ns576p1883 := @Ns576p1882 Ns576p675 440358589 10737418240 1213 10737418240 (Ns576p1877 (RS577to588.d4 qz98 qz116 qz274) RS577to588.d63) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1884 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz275 qz4 qz116 974151 1000 980609 1000 

noncomputable def Ns576p1885 := @Enclosure.norm_gt_of_isNear qz275 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 8639906495997731194617 75557863725914323419136 47227162783865831128697 

noncomputable def Ns576p1886 := @Ns576p1885 Ns576p803 440358589 10737418240 1213 10737418240 (Ns576p1879 (RS577to588.d58 qz98 qz116 qz274) RS577to588.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz276 := qz559

noncomputable def Ns576p1887 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz276 (@BSN.thirtyTwoPi_le_dec qz98 979365 1000 qz101 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz273 qz275 (Ns576p1878 rfl rfl) (Ns576p1880 rfl rfl)) (Ns576p1881 qz11 qz101 rfl rfl rfl rfl (Ns576p1883 rfl)) (Ns576p1884 qz11 qz119 rfl rfl rfl rfl (Ns576p1886 rfl)) 

noncomputable abbrev qz561 := (RS577to588.d3 qz651 qz662 (@Enclosure.dec_le_dec qz651 qz662 980609 1000 981853 1000 qz655 qz666 rfl rfl rfl))

noncomputable abbrev qz277 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz561)

noncomputable def Ns576p1888 := @Enclosure.Real.IsNear.of_eq qz277 (hardyZApproximantRS₀ qz116) Bool.false 8639906495997731194617 75557863725914323419136 47227162783865831128697 Ns576p803 

noncomputable abbrev qz562 := (@Enclosure.dec_le_dec qz651 qz662 980609 1000 981853 1000 qz655 qz666 rfl rfl rfl)

noncomputable abbrev qz278 := qz562

noncomputable def Ns576p1889 := @Enclosure.Real.IsNear.pos_val qz277 8639906495997731194617 75557863725914323419136 47227162783865831128697 Ns576p803 (Ns576p1888 (RS577to588.d4 qz116 qz134 qz278) RS577to588.d64) rfl 

noncomputable abbrev qz279 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz561)

noncomputable def Ns576p1890 := @Enclosure.Real.IsNear.of_eq qz279 (hardyZApproximantRS₀ qz134) Bool.true 10439777067335109867773 9444732965739290427392 5911150100596671347187 Ns576p933 

noncomputable def Ns576p1891 := @Enclosure.Real.IsNear.neg_val qz279 10439777067335109867773 9444732965739290427392 5911150100596671347187 Ns576p933 (Ns576p1890 (RS577to588.d58 qz116 qz134 qz278) RS577to588.d65) rfl 

noncomputable def Ns576p1892 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz277 qz4 qz116 974151 1000 980609 1000 

noncomputable def Ns576p1893 := @Enclosure.norm_gt_of_isNear qz277 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 8639906495997731194617 75557863725914323419136 47227162783865831128697 

noncomputable def Ns576p1894 := @Ns576p1893 Ns576p803 440358589 10737418240 1213 10737418240 (Ns576p1888 (RS577to588.d4 qz116 qz134 qz278) RS577to588.d64) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1895 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz279 qz4 qz134 974151 1000 981853 1000 

noncomputable def Ns576p1896 := @Enclosure.norm_gt_of_isNear qz279 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 10439777067335109867773 9444732965739290427392 5911150100596671347187 

noncomputable def Ns576p1897 := @Ns576p1896 Ns576p933 440358589 10737418240 1213 10737418240 (Ns576p1890 (RS577to588.d58 qz116 qz134 qz278) RS577to588.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz280 := qz561

noncomputable def Ns576p1898 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz280 (@BSN.thirtyTwoPi_le_dec qz116 980609 1000 qz119 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz277 qz279 (Ns576p1889 rfl rfl) (Ns576p1891 rfl rfl)) (Ns576p1892 qz11 qz119 rfl rfl rfl rfl (Ns576p1894 rfl)) (Ns576p1895 qz11 qz137 rfl rfl rfl rfl (Ns576p1897 rfl)) 

noncomputable abbrev qz563 := (RS577to588.d3 qz662 qz672 (@Enclosure.dec_le_dec qz662 qz672 981853 1000 983097 1000 qz666 qz676 rfl rfl rfl))

noncomputable abbrev qz281 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz563)

noncomputable def Ns576p1899 := @Enclosure.Real.IsNear.of_eq qz281 (hardyZApproximantRS₀ qz134) Bool.true 10439777067335109867773 9444732965739290427392 5911150100596671347187 Ns576p933 

noncomputable abbrev qz564 := (@Enclosure.dec_le_dec qz662 qz672 981853 1000 983097 1000 qz666 qz676 rfl rfl rfl)

noncomputable abbrev qz282 := qz564

noncomputable def Ns576p1900 := @Enclosure.Real.IsNear.neg_val qz281 10439777067335109867773 9444732965739290427392 5911150100596671347187 Ns576p933 (Ns576p1899 (RS577to588.d4 qz134 qz152 qz282) RS577to588.d65) rfl 

noncomputable abbrev qz283 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz563)

noncomputable def Ns576p1901 := @Enclosure.Real.IsNear.of_eq qz283 (hardyZApproximantRS₀ qz152) Bool.false 56126642732835586094123 37778931862957161709568 23673605696505566823547 Ns576p1063 

noncomputable def Ns576p1902 := @Enclosure.Real.IsNear.pos_val qz283 56126642732835586094123 37778931862957161709568 23673605696505566823547 Ns576p1063 (Ns576p1901 (RS577to588.d58 qz134 qz152 qz282) RS577to588.d66) rfl 

noncomputable def Ns576p1903 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz281 qz4 qz134 974151 1000 981853 1000 

noncomputable def Ns576p1904 := @Enclosure.norm_gt_of_isNear qz281 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 10439777067335109867773 9444732965739290427392 5911150100596671347187 

noncomputable def Ns576p1905 := @Ns576p1904 Ns576p933 440358589 10737418240 1213 10737418240 (Ns576p1899 (RS577to588.d4 qz134 qz152 qz282) RS577to588.d65) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1906 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz283 qz4 qz152 974151 1000 983097 1000 

noncomputable def Ns576p1907 := @Enclosure.norm_gt_of_isNear qz283 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 56126642732835586094123 37778931862957161709568 23673605696505566823547 

noncomputable def Ns576p1908 := @Ns576p1907 Ns576p1063 440358589 10737418240 1213 10737418240 (Ns576p1901 (RS577to588.d58 qz134 qz152 qz282) RS577to588.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz284 := qz563

noncomputable def Ns576p1909 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz284 (@BSN.thirtyTwoPi_le_dec qz134 981853 1000 qz137 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz281 qz283 (Ns576p1900 rfl rfl) (Ns576p1902 rfl rfl)) (Ns576p1903 qz11 qz137 rfl rfl rfl rfl (Ns576p1905 rfl)) (Ns576p1906 qz11 qz155 rfl rfl rfl rfl (Ns576p1908 rfl)) 

noncomputable abbrev qz565 := (RS577to588.d3 qz672 qz682 (@Enclosure.dec_le_dec qz672 qz682 983097 1000 984340 1000 qz676 qz686 rfl rfl rfl))

noncomputable abbrev qz285 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz565)

noncomputable def Ns576p1910 := @Enclosure.Real.IsNear.of_eq qz285 (hardyZApproximantRS₀ qz152) Bool.false 56126642732835586094123 37778931862957161709568 23673605696505566823547 Ns576p1063 

noncomputable abbrev qz566 := (@Enclosure.dec_le_dec qz672 qz682 983097 1000 984340 1000 qz676 qz686 rfl rfl rfl)

noncomputable abbrev qz286 := qz566

noncomputable def Ns576p1911 := @Enclosure.Real.IsNear.pos_val qz285 56126642732835586094123 37778931862957161709568 23673605696505566823547 Ns576p1063 (Ns576p1910 (RS577to588.d4 qz152 qz170 qz286) RS577to588.d66) rfl 

noncomputable abbrev qz287 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz565)

noncomputable def Ns576p1912 := @Enclosure.Real.IsNear.of_eq qz287 (hardyZApproximantRS₀ qz170) Bool.true 12523547403967013451183 4722366482869645213696 23705350709767663980013 Ns576p1063 

noncomputable def Ns576p1913 := @Enclosure.Real.IsNear.neg_val qz287 12523547403967013451183 4722366482869645213696 23705350709767663980013 Ns576p1063 (Ns576p1912 (RS577to588.d58 qz152 qz170 qz286) RS577to588.d67) rfl 

noncomputable def Ns576p1914 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz285 qz4 qz152 974151 1000 983097 1000 

noncomputable def Ns576p1915 := @Enclosure.norm_gt_of_isNear qz285 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 56126642732835586094123 37778931862957161709568 23673605696505566823547 

noncomputable def Ns576p1916 := @Ns576p1915 Ns576p1063 440358589 10737418240 1213 10737418240 (Ns576p1910 (RS577to588.d4 qz152 qz170 qz286) RS577to588.d66) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1917 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz287 qz4 qz170 974151 1000 984340 1000 

noncomputable def Ns576p1918 := @Enclosure.norm_gt_of_isNear qz287 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 12523547403967013451183 4722366482869645213696 23705350709767663980013 

noncomputable def Ns576p1919 := @Ns576p1918 Ns576p1063 440358589 10737418240 1213 10737418240 (Ns576p1912 (RS577to588.d58 qz152 qz170 qz286) RS577to588.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz288 := qz565

noncomputable def Ns576p1920 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz288 (@BSN.thirtyTwoPi_le_dec qz152 983097 1000 qz155 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz285 qz287 (Ns576p1911 rfl rfl) (Ns576p1913 rfl rfl)) (Ns576p1914 qz11 qz155 rfl rfl rfl rfl (Ns576p1916 rfl)) (Ns576p1917 qz11 qz173 rfl rfl rfl rfl (Ns576p1919 rfl)) 

noncomputable abbrev qz735 := (@Enclosure.dec_le_dec qz780 qz784 984340 1000 985816 1000 (@Eq.refl Real qz780) (@Eq.refl Real qz784) rfl rfl rfl)

noncomputable abbrev qz567 := (RS577to588.d3 qz682 qz692 qz735)

noncomputable abbrev qz289 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz567)

noncomputable def Ns576p1921 := @Enclosure.Real.IsNear.of_eq qz289 (hardyZApproximantRS₀ qz170) Bool.true 12523547403967013451183 4722366482869645213696 23705350709767663980013 Ns576p1063 

noncomputable abbrev qz568 := qz735

noncomputable abbrev qz290 := qz568

noncomputable def Ns576p1922 := @Enclosure.Real.IsNear.neg_val qz289 12523547403967013451183 4722366482869645213696 23705350709767663980013 Ns576p1063 (Ns576p1921 (RS577to588.d4 qz170 qz188 qz290) RS577to588.d67) rfl 

noncomputable abbrev qz291 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz567)

noncomputable def Ns576p1923 := @Enclosure.Real.IsNear.of_eq qz291 (hardyZApproximantRS₀ qz188) Bool.false 13070874894537356584079 18889465931478580854784 1187096367712864967321 1180591620717411303424000 

noncomputable def Ns576p1924 := @Enclosure.Real.IsNear.pos_val qz291 13070874894537356584079 18889465931478580854784 1187096367712864967321 1180591620717411303424000 (Ns576p1923 (RS577to588.d58 qz170 qz188 qz290) RS577to588.d68) rfl 

noncomputable def Ns576p1925 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz289 qz4 qz170 974151 1000 984340 1000 

noncomputable def Ns576p1926 := @Enclosure.norm_gt_of_isNear qz289 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 12523547403967013451183 4722366482869645213696 23705350709767663980013 

noncomputable def Ns576p1927 := @Ns576p1926 Ns576p1063 440358589 10737418240 1213 10737418240 (Ns576p1921 (RS577to588.d4 qz170 qz188 qz290) RS577to588.d67) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1928 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz291 qz4 qz188 974151 1000 985816 1000 

noncomputable def Ns576p1929 := @Enclosure.norm_gt_of_isNear qz291 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 13070874894537356584079 18889465931478580854784 1187096367712864967321 

noncomputable def Ns576p1930 := @Ns576p1929 1180591620717411303424000 440358589 10737418240 1213 10737418240 (Ns576p1923 (RS577to588.d58 qz170 qz188 qz290) RS577to588.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz292 := qz567

noncomputable def Ns576p1931 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz292 (@BSN.thirtyTwoPi_le_dec qz170 984340 1000 qz173 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz289 qz291 (Ns576p1922 rfl rfl) (Ns576p1924 rfl rfl)) (Ns576p1925 qz11 qz173 rfl rfl rfl rfl (Ns576p1927 rfl)) (Ns576p1928 qz11 qz191 rfl rfl rfl rfl (Ns576p1930 rfl)) 

noncomputable abbrev qz736 := (@Enclosure.dec_le_dec qz784 qz788 985816 1000 986438 1000 (@Eq.refl Real qz784) qz791 rfl rfl rfl)

noncomputable abbrev qz569 := (RS577to588.d3 qz692 qz702 qz736)

noncomputable abbrev qz293 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz569)

noncomputable def Ns576p1932 := @Enclosure.Real.IsNear.of_eq qz293 (hardyZApproximantRS₀ qz188) Bool.false 13070874894537356584079 18889465931478580854784 1187096367712864967321 1180591620717411303424000 

noncomputable abbrev qz570 := qz736

noncomputable abbrev qz294 := qz570

noncomputable def Ns576p1933 := @Enclosure.Real.IsNear.pos_val qz293 13070874894537356584079 18889465931478580854784 1187096367712864967321 1180591620717411303424000 (Ns576p1932 (RS577to588.d4 qz188 qz206 qz294) RS577to588.d68) rfl 

noncomputable abbrev qz295 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz569)

noncomputable def Ns576p1934 := @Enclosure.Real.IsNear.of_eq qz295 (hardyZApproximantRS₀ qz206) Bool.true 2306419032622202441707 4722366482869645213696 11877729506359900053103 Ns576p1443 

noncomputable def Ns576p1935 := @Enclosure.Real.IsNear.neg_val qz295 2306419032622202441707 4722366482869645213696 11877729506359900053103 Ns576p1443 (Ns576p1934 (RS577to588.d58 qz188 qz206 qz294) RS577to588.d69) rfl 

noncomputable def Ns576p1936 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz293 qz4 qz188 974151 1000 985816 1000 

noncomputable def Ns576p1937 := @Enclosure.norm_gt_of_isNear qz293 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 13070874894537356584079 18889465931478580854784 1187096367712864967321 

noncomputable def Ns576p1938 := @Ns576p1937 1180591620717411303424000 440358589 10737418240 1213 10737418240 (Ns576p1932 (RS577to588.d4 qz188 qz206 qz294) RS577to588.d68) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1939 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz295 qz4 qz206 974151 1000 986438 1000 

noncomputable def Ns576p1940 := @Enclosure.norm_gt_of_isNear qz295 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2306419032622202441707 4722366482869645213696 11877729506359900053103 

noncomputable def Ns576p1941 := @Ns576p1940 Ns576p1443 440358589 10737418240 1213 10737418240 (Ns576p1934 (RS577to588.d58 qz188 qz206 qz294) RS577to588.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz296 := qz569

noncomputable def Ns576p1942 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz296 (@BSN.thirtyTwoPi_le_dec qz188 985816 1000 qz191 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz293 qz295 (Ns576p1933 rfl rfl) (Ns576p1935 rfl rfl)) (Ns576p1936 qz11 qz191 rfl rfl rfl rfl (Ns576p1938 rfl)) (Ns576p1939 qz11 qz209 rfl rfl rfl rfl (Ns576p1941 rfl)) 

noncomputable abbrev qz737 := (@Enclosure.dec_le_dec qz788 qz793 986438 1000 987447 1000 qz791 qz796 rfl rfl rfl)

noncomputable abbrev qz571 := (RS577to588.d3 qz702 qz713 qz737)

noncomputable abbrev qz297 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz571)

noncomputable def Ns576p1943 := @Enclosure.Real.IsNear.of_eq qz297 (hardyZApproximantRS₀ qz206) Bool.true 2306419032622202441707 4722366482869645213696 11877729506359900053103 Ns576p1443 

noncomputable abbrev qz572 := qz737

noncomputable abbrev qz298 := qz572

noncomputable def Ns576p1944 := @Enclosure.Real.IsNear.neg_val qz297 2306419032622202441707 4722366482869645213696 11877729506359900053103 Ns576p1443 (Ns576p1943 (RS577to588.d4 qz206 qz223 qz298) RS577to588.d69) rfl 

noncomputable abbrev qz299 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz571)

noncomputable def Ns576p1945 := @Enclosure.Real.IsNear.of_eq qz299 (hardyZApproximantRS₀ qz223) Bool.false 716403072799545882402603 151115727451828646838272 95121355583483133926267 Ns576p1570 

noncomputable def Ns576p1946 := @Enclosure.Real.IsNear.pos_val qz299 716403072799545882402603 151115727451828646838272 95121355583483133926267 Ns576p1570 (Ns576p1945 (RS577to588.d58 qz206 qz223 qz298) RS577to588.d70) rfl 

noncomputable def Ns576p1947 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz297 qz4 qz206 974151 1000 986438 1000 

noncomputable def Ns576p1948 := @Enclosure.norm_gt_of_isNear qz297 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 2306419032622202441707 4722366482869645213696 11877729506359900053103 

noncomputable def Ns576p1949 := @Ns576p1948 Ns576p1443 440358589 10737418240 1213 10737418240 (Ns576p1943 (RS577to588.d4 qz206 qz223 qz298) RS577to588.d69) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1950 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz299 qz4 qz223 974151 1000 987447 1000 

noncomputable def Ns576p1951 := @Enclosure.norm_gt_of_isNear qz299 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 716403072799545882402603 151115727451828646838272 95121355583483133926267 

noncomputable def Ns576p1952 := @Ns576p1951 Ns576p1570 440358589 10737418240 1213 10737418240 (Ns576p1945 (RS577to588.d58 qz206 qz223 qz298) RS577to588.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz300 := qz571

noncomputable def Ns576p1953 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz300 (@BSN.thirtyTwoPi_le_dec qz206 986438 1000 qz209 rfl rfl) (BSN.mul_neg_of_neg_pos_r qz297 qz299 (Ns576p1944 rfl rfl) (Ns576p1946 rfl rfl)) (Ns576p1947 qz11 qz209 rfl rfl rfl rfl (Ns576p1949 rfl)) (Ns576p1950 qz11 qz226 rfl rfl rfl rfl (Ns576p1952 rfl)) 

noncomputable abbrev qz803 := (@Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 987447 1000) (Enclosure.sfrac Bool.false 989310 1000) 987447 1000 989310 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 987447 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 989310 1000)) rfl rfl rfl)

noncomputable abbrev qz738 := qz803

noncomputable abbrev qz573 := (RS577to588.d3 qz713 qz724 qz738)

noncomputable abbrev qz301 := (Zeta.Certificates.ZIntervalRS.fstVal₀ qz573)

noncomputable def Ns576p1954 := @Enclosure.Real.IsNear.of_eq qz301 (hardyZApproximantRS₀ qz223) Bool.false 716403072799545882402603 151115727451828646838272 95121355583483133926267 Ns576p1570 

noncomputable abbrev qz574 := qz738

noncomputable abbrev qz302 := qz574

noncomputable def Ns576p1955 := @Enclosure.Real.IsNear.pos_val qz301 716403072799545882402603 151115727451828646838272 95121355583483133926267 Ns576p1570 (Ns576p1954 (RS577to588.d4 qz223 qz240 qz302) RS577to588.d70) rfl 

noncomputable abbrev qz303 := (Zeta.Certificates.ZIntervalRS.sndVal₀ qz573)

noncomputable def Ns576p1956 := @Enclosure.Real.IsNear.of_eq qz303 (hardyZApproximantRS₀ qz240) Bool.true 9881569288893253501049 4722366482869645213696 2978413621283732680259 Ns576p1704 

noncomputable def Ns576p1957 := @Enclosure.Real.IsNear.neg_val qz303 9881569288893253501049 4722366482869645213696 2978413621283732680259 Ns576p1704 (Ns576p1956 (RS577to588.d58 qz223 qz240 qz302) RS577to588.d71) rfl 

noncomputable def Ns576p1958 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz301 qz4 qz223 974151 1000 987447 1000 

noncomputable def Ns576p1959 := @Enclosure.norm_gt_of_isNear qz301 (hardyZErrorBoundRS₀ qz4) Bool.false Bool.false 716403072799545882402603 151115727451828646838272 95121355583483133926267 

noncomputable def Ns576p1960 := @Ns576p1959 Ns576p1570 440358589 10737418240 1213 10737418240 (Ns576p1954 (RS577to588.d4 qz223 qz240 qz302) RS577to588.d70) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable def Ns576p1961 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le qz303 qz4 qz240 974151 1000 989310 1000 

noncomputable def Ns576p1962 := @Enclosure.norm_gt_of_isNear qz303 (hardyZErrorBoundRS₀ qz4) Bool.true Bool.false 9881569288893253501049 4722366482869645213696 2978413621283732680259 

noncomputable def Ns576p1963 := @Ns576p1962 Ns576p1704 440358589 10737418240 1213 10737418240 (Ns576p1956 (RS577to588.d58 qz223 qz240 qz302) RS577to588.d71) (@Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ qz4) (hardyZErrorBoundRS₀ qz4) Bool.false 440358589 10737418240 1213 10737418240 (@Eq.refl Real (hardyZErrorBoundRS₀ qz4)) RS577to588.d60) rfl rfl rfl rfl 

noncomputable abbrev qz304 := qz573

noncomputable def Ns576p1964 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk qz304 (@BSN.thirtyTwoPi_le_dec qz223 987447 1000 qz226 rfl rfl) (BSN.mul_neg_of_pos_neg_r qz301 qz303 (Ns576p1955 rfl rfl) (Ns576p1957 rfl rfl)) (Ns576p1958 qz11 qz226 rfl rfl rfl rfl (Ns576p1960 rfl)) (Ns576p1961 qz11 qz243 rfl rfl rfl rfl (Ns576p1963 rfl)) 

noncomputable def Ns576p1965 := @List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz300 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz300) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz300) Ns576p1953)) (@List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz304 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz304) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz304) Ns576p1964)) (@List.nil RS577to588.d0)) 

noncomputable def Ns576p1966 := @List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz292 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz292) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz292) Ns576p1931)) (@List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz296 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz296) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz296) Ns576p1942)) Ns576p1965) 

noncomputable def Ns576p1967 := @List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz284 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz284) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz284) Ns576p1909)) (@List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz288 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz288) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz288) Ns576p1920)) Ns576p1966) 

noncomputable def Ns576p1968 := @List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz276 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz276) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz276) Ns576p1887)) (@List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz280 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz280) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz280) Ns576p1898)) Ns576p1967) 

noncomputable def Ns576p1969 := @List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz268 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz268) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz268) Ns576p1865)) (@List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz272 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz272) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz272) Ns576p1876)) Ns576p1968) 

noncomputable def Ns576p1970 := @List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz260 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz260) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz260) Ns576p1843)) (@List.cons RS577to588.d0 (@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified qz264 (@Or.inr (Zeta.Certificates.ZIntervalRS.Certificate qz264) (Zeta.Certificates.ZIntervalRS.Certificate₀ qz264) Ns576p1854)) Ns576p1969) 

noncomputable abbrev qz575 := (RS577to588.d2 qz682 qz692 qz735)

noncomputable abbrev qz739 := (RS577to588.d2 qz788 qz793 (@Enclosure.dec_le_dec qz788 qz793 986438 1000 987447 1000 qz791 qz796 rfl rfl rfl))

noncomputable abbrev qz740 := (@List.cons RS577to588.d1 (RS577to588.d2 qz793 qz798 qz803) (@List.nil RS577to588.d1))

noncomputable abbrev qz576 := (@List.cons RS577to588.d1 (RS577to588.d2 qz692 qz702 qz736) (@List.cons RS577to588.d1 qz739 qz740))

noncomputable abbrev qz305 := (@List.cons RS577to588.d1 (RS577to588.d2 qz476 qz489 qz566) (@List.cons RS577to588.d1 qz575 qz576))

noncomputable def Ns576p1971 := @List.cons RS577to588.d1 (RS577to588.d2 qz116 qz134 qz278) (@List.cons RS577to588.d1 (RS577to588.d2 qz134 qz152 qz282) qz305) 

noncomputable abbrev qz306 := (RS577to588.d2 qz435 qz450 qz560)

noncomputable def Ns576p1972 := @List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 qz306 (RS577to588.d2 qz116 qz134 qz278) (@List.cons RS577to588.d1 (RS577to588.d2 qz134 qz152 qz282) qz305) 

noncomputable def Ns576p1973 := @List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 (RS577to588.d2 qz116 qz134 qz278) (RS577to588.d2 qz134 qz152 qz282) qz305 (@Enclosure.dec_le_dec qz134 qz134 981853 1000 981853 1000 qz137 qz137 rfl rfl rfl) 

noncomputable abbrev qz307 := (RS577to588.d2 qz476 qz489 qz566)

noncomputable abbrev qz308 := qz575

noncomputable abbrev qz309 := qz576

noncomputable abbrev qz577 := (RS577to588.d2 qz692 qz702 qz736)

noncomputable abbrev qz310 := qz577

noncomputable abbrev qz578 := (@List.cons RS577to588.d1 qz739 qz740)

noncomputable abbrev qz311 := qz578

noncomputable abbrev qz579 := qz739

noncomputable abbrev qz312 := qz579

noncomputable abbrev qz580 := qz740

noncomputable abbrev qz313 := qz580

noncomputable abbrev qz741 := (RS577to588.d2 qz793 qz798 qz803)

noncomputable abbrev qz581 := qz741

noncomputable abbrev qz314 := qz581

noncomputable def Ns576p1974 := @List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 qz307 qz308 qz309 (@Enclosure.dec_le_dec qz170 qz170 984340 1000 984340 1000 qz173 qz173 rfl rfl rfl) (@List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 qz308 qz310 qz311 (@Enclosure.dec_le_dec qz188 qz188 985816 1000 985816 1000 qz191 qz191 rfl rfl rfl) (@List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 qz310 qz312 qz313 (@Enclosure.dec_le_dec qz206 qz206 986438 1000 986438 1000 qz209 qz209 rfl rfl rfl) (@List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 qz312 qz314 (@List.nil RS577to588.d1) (@Enclosure.dec_le_dec qz223 qz223 987447 1000 987447 1000 qz226 qz226 rfl rfl rfl) (@List.IsChain.singleton RS577to588.d1 RS577to588.d72 qz314)))) 

noncomputable abbrev qz315 := (@List.cons RS577to588.d1 qz575 qz576)

noncomputable def Ns576p1975 := @List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 (RS577to588.d2 qz134 qz152 qz282) qz307 qz315 (@Enclosure.dec_le_dec qz152 qz152 983097 1000 983097 1000 qz155 qz155 rfl rfl rfl) Ns576p1974 

noncomputable def Ns576p1976 := @List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 (RS577to588.d2 qz4 qz35 qz258) (RS577to588.d2 qz35 qz62 qz262) (@List.cons RS577to588.d1 (RS577to588.d2 qz62 qz80 qz266) (@List.cons RS577to588.d1 (RS577to588.d2 qz80 qz98 qz270) (@List.cons RS577to588.d1 qz306 Ns576p1971))) (@Enclosure.dec_le_dec qz35 qz35 975630 1000 975630 1000 qz38 qz38 rfl rfl rfl) (@List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 (RS577to588.d2 qz35 qz62 qz262) (RS577to588.d2 qz62 qz80 qz266) (@List.cons RS577to588.d1 (RS577to588.d2 qz80 qz98 qz270) (@List.cons RS577to588.d1 qz306 Ns576p1971)) (@Enclosure.dec_le_dec qz62 qz62 976875 1000 976875 1000 qz65 qz65 rfl rfl rfl) (@List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 (RS577to588.d2 qz62 qz80 qz266) (RS577to588.d2 qz80 qz98 qz270) (@List.cons RS577to588.d1 qz306 Ns576p1971) (@Enclosure.dec_le_dec qz80 qz80 978120 1000 978120 1000 qz83 qz83 rfl rfl rfl) (@List.IsChain.cons_cons RS577to588.d1 RS577to588.d72 (RS577to588.d2 qz80 qz98 qz270) qz306 Ns576p1971 (@Enclosure.dec_le_dec qz98 qz98 979365 1000 979365 1000 qz101 qz101 rfl rfl rfl) (Ns576p1972 (@Enclosure.dec_le_dec qz116 qz116 980609 1000 980609 1000 qz119 qz119 rfl rfl rfl) (Ns576p1973 Ns576p1975))))) 

noncomputable abbrev qz582 := (@NonemptyInterval Real Real.instLE)

noncomputable abbrev qz583 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns576p1970 Ns576p1976)

noncomputable abbrev qz584 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedRS Ns576p1970 Ns576p1976))

theorem RS577to588.d73 : Zeta.Certificates.BatchSpec 12 974151 1000 989310 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz582 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 12) (And (@Eq (Option Real) (@Option.map qz582 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz582 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz582 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz582 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz240)))) qz583 (@And.intro (@Eq Nat (@List.length qz582 qz584) 12) (And (@Eq (Option Real) (@Option.map qz582 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz582 qz584)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz582 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz582 qz584)) (@Option.some Real qz240))) (@Eq.refl Nat 12) (@And.intro (@Eq (Option Real) (@Option.map qz582 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz582 qz584)) (@Option.some Real qz4)) (@Eq (Option Real) (@Option.map qz582 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz582 qz584)) (@Option.some Real qz240)) (@Eq.refl (Option Real) (@Option.some Real qz4)) (@Eq.refl (Option Real) (@Option.some Real qz240))))

theorem solution : Zeta.Certificates.BatchSpec 12 974151 1000 989310 1000 := RS577to588.d73
#print axioms solution
#check solution
