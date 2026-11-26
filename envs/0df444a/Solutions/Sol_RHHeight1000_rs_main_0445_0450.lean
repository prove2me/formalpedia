-- Prove2me | solution 1 for RHHeight1000.rs_main_0445_0450
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:34:40.591353+00:00
-- url     : https://prove2.me/submissions/1210e80e-06de-4fa5-8c7e-15e1aabceaee

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

noncomputable def hp2101 := nat_lit 1181671153346359170692730265957638242378174781758650

noncomputable def hp2102 := nat_lit 5986310706507378352962293074805895248510699696029696

noncomputable def hp2103 := Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1) (@Nat.cast Real Real.instNatCast 5))) Bool.false hp2101 hp2102

noncomputable def hp2104 := nat_lit 2000000000000000000000000000000000000000000000000000

noncomputable def hp2105 := nat_lit 1499028120395240233173640088155429295548437777754679499662777369540625

noncomputable def hp2106 := nat_lit 4680297997409431328241185462095581837349556053595733828842639923095703125

noncomputable def hp2107 := nat_lit 13442882392639581675476766202062253719655739830178303899086159055189875

noncomputable def hp2108 := nat_lit 19584239746202378791298717228947477708711488730841665528714656829833984375

noncomputable def hp2109 := BSN.arctan_dyadic_bound_f 1 5 18 17 hp2102 hp2104 hp2105 hp2106 200200021673987500790625 hp2107 hp2108

noncomputable def hp2110 := nat_lit 2442358029135994033939875

noncomputable def hp2111 := nat_lit 37260822860694382775919147000

noncomputable def hp2112 := nat_lit 116336546489037573337554931640625

noncomputable def hp2113 := nat_lit 57493278893883548332405996866302358825

noncomputable def hp2114 := nat_lit 40230676762013536063022911548614501953125

noncomputable def hp2115 := @BSN.binarySplit_rec (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 17 8 hp2111 hp2112 151412625 hp2113 hp2114

noncomputable def hp2116 := @BSN.binarySplit_of_base8 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 0 8 hp2111 hp2112 151412625 rfl rfl rfl

noncomputable def hp2117 := @BSN.binarySplit_of_base9 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 5) 8 17 hp2113 hp2114 1322214852783825 rfl rfl rfl

noncomputable def hp2118 := @hp2115 1322214852783825 hp2105 hp2106 200200021673987500790625 rfl rfl rfl rfl rfl (hp2116 rfl) (hp2117 rfl)

noncomputable def hp2119 := nat_lit 236310350532676991248348623960

noncomputable def hp2120 := nat_lit 344268321641720831394195556640625

noncomputable def hp2121 := nat_lit 81801971833623620377505564448994707675

noncomputable def hp2122 := nat_lit 56886557708273976459167897701263427734375

noncomputable def hp2123 := @BSN.binarySplit_rec (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 17 8 hp2119 hp2120 1267389585 hp2121 hp2122

noncomputable def hp2124 := @BSN.binarySplit_of_base8 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 0 8 hp2119 hp2120 1267389585 rfl rfl rfl

noncomputable def hp2125 := @BSN.binarySplit_of_base9 (BSN.arctanOddP 1) (BSN.arctanOddQ 5) 8 17 hp2121 hp2122 1927077560082675 rfl rfl rfl

noncomputable def hp2126 := @hp2123 1927077560082675 hp2107 hp2108 hp2110 rfl rfl rfl rfl rfl (hp2124 rfl) (hp2125 rfl)

noncomputable def hp2127 := hp2109 hp2110 hp2101 rfl rfl rfl rfl rfl rfl rfl hp2118 hp2126

theorem hd100 : hp2103 1 hp2104 := hp2127 rfl rfl rfl rfl

noncomputable def hp2128 := nat_lit 25047178968060507272880539293402373975644382030403

noncomputable def hp2129 := Enclosure.Real.IsNear (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1) (@Nat.cast Real Real.instNatCast 239))) Bool.false hp2128 hp2102

noncomputable def hp2130 := nat_lit 4733915408010924740926662591654183582145509

noncomputable def hp2131 := nat_lit 77229300481955664312677298336960122659119574530232845

noncomputable def hp2132 := nat_lit 24516194103503660983641551147684725335332607

noncomputable def hp2133 := nat_lit 186647183216068817672719845704257068688983305564016735

noncomputable def hp2134 := BSN.arctan_dyadic_bound_f 1 239 6 5 hp2102 hp2104 hp2130 hp2131 9945 hp2132 hp2133

noncomputable def hp2135 := @BSN.binarySplit_of_base5 (BSN.arctanEvenP 1) (BSN.arctanEvenQ 239) 0 5 hp2130 hp2131 9945 rfl rfl rfl

noncomputable def hp2136 := @BSN.binarySplit_of_base5 (BSN.arctanOddP 1) (BSN.arctanOddQ 239) 0 5 hp2132 hp2133 65835 rfl rfl rfl

noncomputable def hp2137 := hp2134 65835 hp2128 rfl rfl rfl rfl rfl rfl rfl (hp2135 rfl) (hp2136 rfl)

theorem hd101 : hp2129 1 hp2104 := hp2137 rfl rfl rfl rfl

noncomputable def hp2138 := nat_lit 18806549737669504701992162098148602382148218980016788

noncomputable def hp2139 := nat_lit 100000000000000000000000000000000000000000000000000

noncomputable def hp2140 := BSN.pi_combine hp2101 hp2128 hp2102 hp2104 hp2139 hp2138 rfl rfl rfl rfl hd100

theorem hd102 : Enclosure.Real.IsNear Real.pi Bool.false hp2138 hp2102 1 hp2139 := hp2140 hd101

noncomputable def hd316 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def hp614126 := nat_lit 100000000000000000000000000000000000000000000000000

noncomputable def hp615317 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936

noncomputable def hp617687 := nat_lit 9671406556917033397649408

noncomputable def hp619230 := nat_lit 2417851639229258349412352

noncomputable def hp619237 := nat_lit 4835703278458516698824704

noncomputable def hp621626 := @BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl

noncomputable def hp627574 := nat_lit 633825300114114700748351602688

noncomputable def hd4339 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => hd316 a b h

theorem hd4340 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 a b h)) (hardyZApproximantRS₀ a) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 a b h))

noncomputable def hp630458 := nat_lit 26986075409044028275299783

noncomputable def hp630459 := nat_lit 8589934592000000000000000

noncomputable def hp630460 := nat_lit 26986075409044045455168967

noncomputable def hp630463 := nat_lit 53972150818088056550599566

noncomputable def hp630464 := nat_lit 17179869184000000000000000

noncomputable def hp630466 := nat_lit 18396140817044028275299783

noncomputable def hp630467 := nat_lit 35576010001044028275299783

noncomputable def hp630475 := nat_lit 53972150818088090910337934

noncomputable def hp630477 := nat_lit 18396140817044045455168967

noncomputable def hp630478 := nat_lit 35576010001044045455168967

noncomputable def hp630490 := @BSN.binarySplit_of_base7 (BSN.artanhP 1) (BSN.artanhQ 3) 0 7 385100712855 9695197737225 135135 rfl rfl rfl

noncomputable def hp630514 := nat_lit 18806549737669504701992162098148602382148218980016788

noncomputable def hp630515 := nat_lit 5986310706507378352962293074805895248510699696029696

noncomputable def hp630533 := Enclosure.Real.IsNear (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) Bool.false 884279719003555 140737488355328 1

noncomputable def hp630534 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936

noncomputable def hp630537 := @Enclosure.Real.IsNear.inv_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) 884279719003555 140737488355328 1 500000000000000

noncomputable def hp630689 := nat_lit 1208925819614629174706176

theorem hd4359 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 a b h))

noncomputable def hp631123 := nat_lit 72057594037927936000000000000000

noncomputable def hp631501 := nat_lit 2882303761517117440000000000000

noncomputable def hp634263 := nat_lit 302231454903657293676544000000000000000

noncomputable def hp638793 := nat_lit 15111572745182864683827200000000000000

noncomputable def hp642702 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800

noncomputable def hp642705 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000

noncomputable def hp645312 := nat_lit 57646075230342348800000000000000

noncomputable def hp681368 := @BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl

noncomputable def hp681432 := @BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl

noncomputable def hp681868 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600

noncomputable def hp681871 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600

noncomputable def hp682141 := nat_lit 158456325028528675187087900672

noncomputable def hp707912 := @BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 18) 0 3 14806464 3571283520 960 rfl rfl rfl

noncomputable def hp708767 := nat_lit 1993841993677373809355710590420516864

noncomputable def hp708768 := nat_lit 29907629905160607140335658856307752960

noncomputable def hp708845 := nat_lit 2504505714323359787184324207303086996185458423821189873137376790332288532480

noncomputable def hp708848 := nat_lit 45915938095928262765045943800556594930066737770055147674185241156091956428800

noncomputable def hp708868 := nat_lit 278278412702595531909369356367009666242828713757909985904152976703587614720

noncomputable def hp708870 := nat_lit 12522528571616798935921621036515434980927292119105949365686883951661442662400

noncomputable def hp708890 := nat_lit 9969209968386869046778552952102584320

noncomputable def hp708891 := nat_lit 69784469778708083327449870664718090240

noncomputable def hp716712 := nat_lit 274647376664257459544000446540783031995164976078897331880025758552119769180746491160307949742358795015190845849600

noncomputable def hp716714 := nat_lit 24992911276447428818504040635211255911560012823179657201082344028242898995447930695588023426554650346382366972313600

noncomputable def hp731908 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 749551 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 749551 1000 0

noncomputable def hp737713 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 307286088 268435456 3 268435456 38410761 33554432 3 268435456

noncomputable def hp737714 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 hp630458 hp630459 hp630460 hp630459 614572177 536870912

noncomputable def hp737715 := @hp737714 1 174240000 614572177 536870912 1 174240000 307286088 268435456 3 268435456 BSN.pi_near_15

noncomputable def hp737716 := BSN.logfrac_isNear hp630463 hp630464 1 hp630458 hp630459 614572177 536870912 174240000 rfl rfl rfl

noncomputable def hp737717 := nat_lit 6573389678388862351155759458724141871788046104702795740939545775355827438482086890337971184306503456724674701876007739166027855002689342487126242201873902293161938510715598861337724155978462934346539722102807352693564004597780440630880721700532830491857281958381906437104026277614553345439647264822859384496062743250358046048880947907642984145065307980413206151384068885350206914057384338280179177725692904928360597982006748935836093248417685721122261418062303135764477585928239149568275027355236134745000697766005167655784166499502223346815249842007858448160935771607172549259242715110048115445292136446613946552506617916138661398090061483392335970316672263498462800198746102072055363920390651513279180731193678641632192805423820381724597815072905552156968003637925334143020171520625

noncomputable def hp737718 := nat_lit 702614123509571190207434367497643053726389003684617183996726348470791223755418688598787599501240412886827946200799073391711533512528899996899108221816773619593298708861540359234024488137706935294538610329535191474811214152768697527793266408685885408431698677504366547635987768499962038530066773279961750661013789994039311989768445302208965109624014234440840481147386361324656837522786906307734587964680180646868573806366973424595907336814393861048013934514934272026683624090151873353554279683010347128413433843775162422864773798490322287367830744467164676975854073090397461536167654230134598982106570951920409048997311342333559851528447946435833392322432321465286801524775001800171249769824525762984779161997185015423416919065587459911326773695449510414365759468097615398764501522575

noncomputable def hp737719 := nat_lit 541392566138474909591412279139378993255101875047003589935782329109463644892392322173295519240510467068363239080443023466297029982601757003829684821059136286585994161974307047499333049696728682047261006046816072264069316416942594393775486731411634963656291648112663555457379375292741727868294229136381639619442405391741167595634732196900940186574903289828257139713673376723681752760045249773972946001592268830432998579610986951410273979009689762628244990479410235165324966379611071762421902787196495466840333515349387051622842182127210560393625584510287605139387730811840242457253978115925211125629993337408355023684205061830608267784338105681114876710224147942516826039256450164994945245879666660679160980454641866547806615379410050641833332584350523565507268843323231339375

noncomputable def hp737720 := BSN.log_dyadic_bound hp630466 hp630467 16 15 hp737717 536870912 174240000 hp737718 hp737719 614572177 hp630463

noncomputable def hp737721 := hp737720 hp630464 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp737722 := @BSN.binarySplit_of_base15 (BSN.artanhP hp630466) (BSN.artanhQ hp630467) 0 15 hp737718 hp737717 hp737719 rfl rfl rfl

noncomputable def hp737723 := hp737715 rfl rfl rfl rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac hp630458 hp630459 614572177 536870912 1 174240000 Bool.false (hp737716 (hp737721 (hp737722 rfl) rfl rfl rfl rfl)))

noncomputable def hp737724 := BSN.logfrac_isNear hp630475 hp630464 1 hp630460 hp630459 614572177 536870912 174240000 rfl rfl rfl

noncomputable def hp737725 := nat_lit 6573389678388957581038003304946500209472262679236338533996718496177406624059139082449994147026037314666926693076053053862592074936423388863596813530408382584499373597031431853921413941298322255656576695489433951602693567143885654771592106690789036275646003378131729522606930818530515414843848039000889531334935427389830473690579523667466182538201372727149023132371319359578146651783732835416323469915494090659780509855937937675396353734377829186029766969614606089327824892671842834136516654569045504808111725705550748907924941183733134599012581542910476929082687043869700761244349471219210833189555347464155979117619898077496880661665775336657207488512148128426326823595335945176245554694022845325705851563290369414226074229552025260849280553835909109839168582914725334143020171520625

noncomputable def hp737726 := nat_lit 702614123509582134195699383225799303120857312948289364169564431944606347230839067212220070086773571232938822231607515388838247088164426860334641427891924556959013106220289292017417932077264689683982462259236603120411894481357554273197237433243865910367073588753830073256225145709268648257922640132615276470163987114280905050307903018021985933333474523803420109333064989110261463867307642914581311357336787925252212965840242792007601256472655504246146516404729632839909377990937267835233434162343951883521915890115762575574377037535717851480622294463860980162526686236248764915916362237196611189536095144270945605478817014333998082847306947436470576941659846222535334992451365706225994338058508887942119777908276510373758951874822816373072605980596581754554466975502415398764501522575

noncomputable def hp737727 := nat_lit 541392566138490077533790984620311058177654278555980714203107761719673916425133183846751239616284470803704371181920004286935467360846628369375164068764590875438310007353955324186636582299553928814156491749519256774653872128089233575343481607925575468185460509172779152955629338248076232826253005811067688706928164570779608774451502836676056177667078421728722179008027603013170304530594440809888606240685402729798990208830923560422594844623819537735750113690675240496626214395332044296593456069970973486809806367897564108502902289348063943342100923856630472249952347312756547637419241376870243223562839253667975765230153074010838184467350558565952691487980795548332122966513692688198426849374346091985539852378055886379210372820263137502377721028428076000707268843323231339375

noncomputable def hp737728 := BSN.log_dyadic_bound hp630477 hp630478 16 15 hp737725 536870912 174240000 hp737726 hp737727 614572177 hp630475

noncomputable def hp737729 := hp737728 hp630464 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp737730 := @BSN.binarySplit_of_base15 (BSN.artanhP hp630477) (BSN.artanhQ hp630478) 0 15 hp737726 hp737725 hp737727 rfl rfl rfl

noncomputable def hp737731 := hp737723 (BSN.isNear_log_sfrac hp630460 hp630459 614572177 536870912 1 174240000 Bool.false (hp737724 (hp737729 (hp737730 rfl) rfl rfl rfl rfl)))

noncomputable def hp737732 := hp737713 (hp737731 rfl rfl rfl rfl rfl rfl rfl rfl)

theorem hd4909 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 38410761 33554432 3 268435456 := hp737732 rfl

noncomputable def hp737733 := BSN.logfrac_isNear 4 2 1 2 1 23258159 33554432 10890000 rfl rfl rfl

noncomputable def hp737734 := BSN.log_dyadic_bound 1 3 8 7 9695197737225 33554432 10890000 385100712855 135135 23258159 4

noncomputable def hp737735 := hp737734 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem hd4910 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 2 1)) Bool.false 23258159 33554432 1 10890000 := BSN.isNear_log_sfrac 2 1 23258159 33554432 1 10890000 Bool.false (hp737733 (hp737735 (hp630490 rfl) rfl rfl rfl rfl))

noncomputable def hp737736 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 2 1)) Bool.false 23258159 33554432 1 10890000 372130544

theorem hd4911 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 2 1)) Bool.false 372130544 536870912 50 536870912 := @hp737736 536870912 50 536870912 hd4910 rfl

noncomputable def hp737737 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 47453133 67108864 1 67108864

noncomputable def hp737738 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 47453133 67108864 1 67108864

noncomputable def hp737739 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) 94906265 67108864 1 67108864 23726566 23726567

noncomputable def hp737740 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 2)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2) (@Nat.cast Real Real.instNatCast 1))) Bool.false 94906265 67108864

noncomputable def hp737741 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2) (@Nat.cast Real Real.instNatCast 1))) Bool.false 94906265 67108864

noncomputable def hp737742 := @hp737741 1 67108864 94906265 67108864 1 67108864 (BSN.sqrt_enclosure 2 1 47453132 47453133 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp737743 := @hp737739 33554432 (@hp737740 1 67108864 (BSN.sqrt_natCast_div_one 2) (hp737742 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd4912 : hp737737 := @hp737738 47453133 67108864 1 67108864 hp737743 rfl

noncomputable def hp737744 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 379625064 536870912 8 536870912

theorem hd4913 : hp737744 := @hp737738 379625064 536870912 8 536870912 hd4912 rfl

noncomputable def hp737745 := BSN.logfrac_isNear 3 1 2 3 1 36863311 33554432 10890000 rfl rfl rfl

noncomputable def hp737746 := BSN.log_dyadic_bound 1 2 13 12 132638213186519040000 33554432 10890000 13079757671720842725 316234143225 36863311 3

noncomputable def hp737747 := hp737746 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem hd4914 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 10890000 := BSN.isNear_log_sfrac 3 1 36863311 33554432 1 10890000 Bool.false (hp737745 (hp737747 (hp681368 rfl) rfl rfl rfl rfl))

noncomputable def hp737748 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 36863311 33554432 1 10890000 589812976

theorem hd4915 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 3 1)) Bool.false 589812976 536870912 50 536870912 := @hp737748 536870912 50 536870912 hd4914 rfl

noncomputable def hp737749 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 38745321 67108864 1 67108864

noncomputable def hp737750 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 38745321 67108864 1 67108864

noncomputable def hp737751 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) 116235963 67108864 1 67108864 19372660 19372661

noncomputable def hp737752 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 3)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3) (@Nat.cast Real Real.instNatCast 1))) Bool.false 116235963 67108864

noncomputable def hp737753 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3) (@Nat.cast Real Real.instNatCast 1))) Bool.false 116235963 67108864

noncomputable def hp737754 := @hp737753 1 67108864 116235963 67108864 1 67108864 (BSN.sqrt_enclosure 3 1 58117981 58117982 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp737755 := @hp737751 33554432 (@hp737752 1 67108864 (BSN.sqrt_natCast_div_one 3) (hp737754 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd4916 : hp737749 := @hp737750 38745321 67108864 1 67108864 hp737755 rfl

noncomputable def hp737756 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 309962568 536870912 8 536870912

theorem hd4917 : hp737756 := @hp737750 309962568 536870912 8 536870912 hd4916 rfl

noncomputable def hp737757 := @Enclosure.Real.IsNear.recentre' Real.pi Bool.false hp630514 hp630515 1 hp614126 28296951008113761 9007199254740992 1 9007199254740992 hd102

theorem hd4918 : Enclosure.Real.IsNear Real.pi Bool.false 28296951008113761 9007199254740992 1 9007199254740992 := hp737757 rfl

noncomputable def hp737758 := BSN.logfrac_isNear 8 2 1 4 1 46516319 33554432 10890000 rfl rfl rfl

noncomputable def hp737759 := nat_lit 129013261453190219981479458510875701904296875

noncomputable def hp737760 := nat_lit 20028702544022979302942508184499384445755625

noncomputable def hp737761 := nat_lit 105610919306899072369715234453255625

noncomputable def hp737762 := BSN.log_dyadic_bound 3 5 18 17 hp737759 33554432 10890000 hp737760 hp737761 46516319 8

noncomputable def hp737763 := hp737762 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp737764 := nat_lit 11743816085855617508865225

noncomputable def hp737765 := nat_lit 24536140990734100341796875

noncomputable def hp737766 := @BSN.binarySplit_rec (BSN.artanhP 3) (BSN.artanhQ 5) 0 17 8 816252149187356400 5258090972900390625 87256779635025 hp737764 hp737765

noncomputable def hp737767 := @BSN.binarySplit_of_base8 (BSN.artanhP 3) (BSN.artanhQ 5) 0 8 816252149187356400 5258090972900390625 87256779635025 rfl rfl rfl

noncomputable def hp737768 := @BSN.binarySplit_of_base9 (BSN.artanhP 3) (BSN.artanhQ 5) 8 17 hp737764 hp737765 1210346287688420415225 rfl rfl rfl

noncomputable def hp737769 := @hp737766 1210346287688420415225 hp737760 hp737759 hp737761 rfl rfl rfl rfl rfl (hp737767 rfl) (hp737768 rfl)

theorem hd4919 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 10890000 := BSN.isNear_log_sfrac 4 1 46516319 33554432 1 10890000 Bool.false (hp737758 (hp737763 hp737769 rfl rfl rfl rfl))

noncomputable def hp737770 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 46516319 33554432 1 10890000 744261104

theorem hd4920 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 4 1)) Bool.false 744261104 536870912 50 536870912 := @hp737770 536870912 50 536870912 hd4919 rfl

noncomputable def hp737771 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 33554431 67108864 1 67108864

noncomputable def hp737772 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 33554431 67108864 1 67108864

noncomputable def hp737773 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) 134217729 67108864 1 67108864 16777215 16777216

noncomputable def hp737774 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 4)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 4) (@Nat.cast Real Real.instNatCast 1))) Bool.false 134217729 67108864

noncomputable def hp737775 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 4) (@Nat.cast Real Real.instNatCast 1))) Bool.false 134217729 67108864

noncomputable def hp737776 := @hp737775 1 67108864 134217729 67108864 1 67108864 (BSN.sqrt_enclosure 4 1 67108864 67108865 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp737777 := @hp737773 33554432 (@hp737774 1 67108864 (BSN.sqrt_natCast_div_one 4) (hp737776 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd4921 : hp737771 := @hp737772 33554431 67108864 1 67108864 hp737777 rfl

noncomputable def hp737778 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 268435448 536870912 8 536870912

theorem hd4922 : hp737778 := @hp737772 268435448 536870912 8 536870912 hd4921 rfl

noncomputable def hp737779 := BSN.logfrac_isNear 5 1 2 5 1 54003774 33554432 10890000 rfl rfl rfl

noncomputable def hp737780 := nat_lit 24987371385403367883999025651388344673404853859375

noncomputable def hp737781 := nat_lit 5174345737036840691400486158476888201456094182500

noncomputable def hp737782 := nat_lit 9919565729522841605829928920966758400000

noncomputable def hp737783 := BSN.log_dyadic_bound 2 3 23 22 hp737780 33554432 10890000 hp737781 hp737782 54003774 5

noncomputable def hp737784 := hp737783 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp737785 := nat_lit 1753791174206542693625850900

noncomputable def hp737786 := nat_lit 2517933232285674949199829375

noncomputable def hp737787 := @BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 22 11 2054957030503884950940 9923762498944768499025 57668788341964800 hp737785 hp737786

noncomputable def hp737788 := @BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 0 11 2054957030503884950940 9923762498944768499025 57668788341964800 rfl rfl rfl

noncomputable def hp737789 := @BSN.binarySplit_of_base11 (BSN.artanhP 2) (BSN.artanhQ 3) 11 22 hp737785 hp737786 172009262110757879808000 rfl rfl rfl

noncomputable def hp737790 := @hp737787 172009262110757879808000 hp737781 hp737780 hp737782 rfl rfl rfl rfl rfl (hp737788 rfl) (hp737789 rfl)

theorem hd4923 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 10890000 := BSN.isNear_log_sfrac 5 1 54003774 33554432 1 10890000 Bool.false (hp737779 (hp737784 hp737790 rfl rfl rfl rfl))

noncomputable def hp737791 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 54003774 33554432 1 10890000 864060384

theorem hd4924 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 5 1)) Bool.false 864060384 536870912 50 536870912 := @hp737791 536870912 50 536870912 hd4923 rfl

noncomputable def hp737792 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 30011997 67108864 1 67108864

noncomputable def hp737793 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 30011997 67108864 1 67108864

noncomputable def hp737794 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 5)) 150059981 67108864 1 67108864 15005998 15005999

noncomputable def hp737795 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 5)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 5) (@Nat.cast Real Real.instNatCast 1))) Bool.false 150059981 67108864

noncomputable def hp737796 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 5) (@Nat.cast Real Real.instNatCast 1))) Bool.false 150059981 67108864

noncomputable def hp737797 := @hp737796 1 67108864 150059981 67108864 1 67108864 (BSN.sqrt_enclosure 5 1 75029990 75029991 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp737798 := @hp737794 33554432 (@hp737795 1 67108864 (BSN.sqrt_natCast_div_one 5) (hp737797 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd4925 : hp737792 := @hp737793 30011997 67108864 1 67108864 hp737798 rfl

noncomputable def hp737799 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 240095976 536870912 8 536870912

theorem hd4926 : hp737799 := @hp737793 240095976 536870912 8 536870912 hd4925 rfl

noncomputable def hp737800 := nat_lit 2166104270535356806332416

noncomputable def hp737801 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))) Bool.false hp737800 hp630689

noncomputable def hp737802 := BSN.log_rat_reduce_isNear 6 1 2 12 8 13605151 33554432 24973259072661432 36028797018963968 10890000 1000000000000000

noncomputable def hp737803 := BSN.log_dyadic_bound 2 10 6 5 103950000000000 33554432 10890000 1420244935680 967680 13605151 12

noncomputable def hp737804 := hp737803 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp737805 := @BSN.binarySplit_of_base5 (BSN.artanhP 2) (BSN.artanhQ 10) 0 5 1420244935680 103950000000000 967680 rfl rfl rfl

noncomputable def hp737806 := hp737802 rfl rfl rfl rfl (hp737804 (hp737805 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

theorem hd4927 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 50000001089 544500000000000000 := BSN.isNear_log_sfrac 6 1 4034683612241143 2251799813685248 50000001089 544500000000000000 Bool.false (@hp737801 1000000021780000 10890000000000000000000 4034683612241143 2251799813685248 50000001089 544500000000000000 (hp737806 rfl rfl rfl) rfl)

noncomputable def hp737807 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 4034683612241143 2251799813685248 50000001089 544500000000000000 961943533

theorem hd4928 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 6 1)) Bool.false 961943533 536870912 51 536870912 := @hp737807 536870912 51 536870912 hd4927 rfl

noncomputable def hp737808 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 27397079 67108864 1 67108864

noncomputable def hp737809 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 27397079 67108864 1 67108864

noncomputable def hp737810 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 6)) 164382475 67108864 1 67108864 13698539 13698540

noncomputable def hp737811 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 6)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))) Bool.false 164382475 67108864

noncomputable def hp737812 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 6) (@Nat.cast Real Real.instNatCast 1))) Bool.false 164382475 67108864

noncomputable def hp737813 := @hp737812 1 67108864 164382475 67108864 1 67108864 (BSN.sqrt_enclosure 6 1 82191237 82191238 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp737814 := @hp737810 33554432 (@hp737811 1 67108864 (BSN.sqrt_natCast_div_one 6) (hp737813 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd4929 : hp737808 := @hp737809 27397079 67108864 1 67108864 hp737814 rfl

noncomputable def hp737815 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 219176632 536870912 8 536870912

theorem hd4930 : hp737815 := @hp737809 219176632 536870912 8 536870912 hd4929 rfl

noncomputable def hp737816 := nat_lit 2352460989330532755046400

noncomputable def hp737817 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))) Bool.false hp737816 hp630689

noncomputable def hp737818 := BSN.log_rat_reduce_isNear 7 1 2 14 8 18777589 33554432 24973259072661432 36028797018963968 10890000 1000000000000000

noncomputable def hp737819 := BSN.log_dyadic_bound 3 11 7 6 424111518688192335 33554432 10890000 11010900719820672 5524329195 18777589 14

noncomputable def hp737820 := hp737819 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp737821 := hp737818 rfl rfl rfl rfl (hp737820 (hp681432 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

theorem hd4931 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 50000001089 544500000000000000 := BSN.isNear_log_sfrac 7 1 4381800050531575 2251799813685248 50000001089 544500000000000000 Bool.false (@hp737817 1000000021780000 10890000000000000000000 4381800050531575 2251799813685248 50000001089 544500000000000000 (hp737821 rfl rfl rfl) rfl)

noncomputable def hp737822 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 4381800050531575 2251799813685248 50000001089 544500000000000000 1044702541

theorem hd4932 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 7 1)) Bool.false 1044702541 536870912 51 536870912 := @hp737822 536870912 51 536870912 hd4931 rfl

noncomputable def hp737823 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 25364767 67108864 1 67108864

noncomputable def hp737824 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 25364767 67108864 1 67108864

noncomputable def hp737825 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 7)) 177553365 67108864 1 67108864 12682383 12682384

noncomputable def hp737826 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 7)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))) Bool.false 177553365 67108864

noncomputable def hp737827 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 7) (@Nat.cast Real Real.instNatCast 1))) Bool.false 177553365 67108864

noncomputable def hp737828 := @hp737827 1 67108864 177553365 67108864 1 67108864 (BSN.sqrt_enclosure 7 1 88776682 88776683 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp737829 := @hp737825 33554432 (@hp737826 1 67108864 (BSN.sqrt_natCast_div_one 7) (hp737828 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd4933 : hp737823 := @hp737824 25364767 67108864 1 67108864 hp737829 rfl

noncomputable def hp737830 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 202918136 536870912 8 536870912

theorem hd4934 : hp737830 := @hp737824 202918136 536870912 8 536870912 hd4933 rfl

noncomputable def hp737831 := nat_lit 2513890570116003237199872

noncomputable def hp737832 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1))) Bool.false hp737831 hp630689

noncomputable def hp737833 := BSN.log_rat_reduce_isNear 8 1 3 16 16 0 33554432 24973259072661432 36028797018963968 10890000 1000000000000000

noncomputable def hp737834 := BSN.log_dyadic_bound 0 16 1 0 1 33554432 10890000 0 1 0 16

noncomputable def hp737835 := hp737834 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp737836 := hp737835 (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp737837 := hp737833 rfl rfl rfl rfl hp737836 BSN.log2_near_15 rfl rfl rfl

theorem hd4935 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000003267 1089000000000000000 := BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000003267 1089000000000000000 Bool.false (@hp737832 1000000032670000 10890000000000000000000 9364972152248037 4503599627370496 100000003267 1089000000000000000 (hp737837 rfl) rfl)

noncomputable def hp737838 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 9364972152248037 4503599627370496 100000003267 1089000000000000000 1116391676

theorem hd4936 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 8 1)) Bool.false 1116391676 536870912 51 536870912 := @hp737838 536870912 51 536870912 hd4935 rfl

noncomputable def hp737839 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 23726567 67108864 1 67108864

noncomputable def hp737840 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 23726567 67108864 1 67108864

noncomputable def hp737841 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 8)) 189812531 67108864 1 67108864 11863283 11863284

noncomputable def hp737842 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 8)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1))) Bool.false 189812531 67108864

noncomputable def hp737843 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 8) (@Nat.cast Real Real.instNatCast 1))) Bool.false 189812531 67108864

noncomputable def hp737844 := @hp737843 1 67108864 189812531 67108864 1 67108864 (BSN.sqrt_enclosure 8 1 94906265 94906266 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp737845 := @hp737841 33554432 (@hp737842 1 67108864 (BSN.sqrt_natCast_div_one 8) (hp737844 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd4937 : hp737839 := @hp737840 23726567 67108864 1 67108864 hp737845 rfl

noncomputable def hp737846 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 189812536 536870912 8 536870912

theorem hd4938 : hp737846 := @hp737840 189812536 536870912 8 536870912 hd4937 rfl

noncomputable def hp737847 := nat_lit 2656281492024125531619328

noncomputable def hp737848 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 9) (@Nat.cast Real Real.instNatCast 1))) Bool.false hp737847 hp630689

noncomputable def hp737849 := BSN.log_rat_reduce_isNear 9 1 3 18 16 3952142 33554432 24973259072661432 36028797018963968 10890000 1000000000000000

noncomputable def hp737850 := BSN.log_dyadic_bound 1 17 3 2 1252815 33554432 10890000 1448 3 3952142 18

noncomputable def hp737851 := hp737850 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp737852 := hp737849 rfl rfl rfl rfl (hp737851 (hp621626 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

theorem hd4939 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000003267 1089000000000000000 := BSN.isNear_log_sfrac 9 1 9895419672221413 4503599627370496 100000003267 1089000000000000000 Bool.false (@hp737848 1000000032670000 10890000000000000000000 9895419672221413 4503599627370496 100000003267 1089000000000000000 (hp737852 rfl rfl rfl) rfl)

noncomputable def hp737853 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 9895419672221413 4503599627370496 100000003267 1089000000000000000 1179625948

theorem hd4940 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 9 1)) Bool.false 1179625948 536870912 51 536870912 := @hp737853 536870912 51 536870912 hd4939 rfl

noncomputable def hp737854 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 22369621 67108864 1 67108864

noncomputable def hp737855 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 22369621 67108864 1 67108864

noncomputable def hp737856 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 9)) 201326593 67108864 1 67108864 11184810 11184811

noncomputable def hp737857 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 9)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 9) (@Nat.cast Real Real.instNatCast 1))) Bool.false 201326593 67108864

noncomputable def hp737858 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 9) (@Nat.cast Real Real.instNatCast 1))) Bool.false 201326593 67108864

noncomputable def hp737859 := @hp737858 1 67108864 201326593 67108864 1 67108864 (BSN.sqrt_enclosure 9 1 100663296 100663297 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp737860 := @hp737856 33554432 (@hp737857 1 67108864 (BSN.sqrt_natCast_div_one 9) (hp737859 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd4941 : hp737854 := @hp737855 22369621 67108864 1 67108864 hp737860 rfl

noncomputable def hp737861 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 178956968 536870912 8 536870912

theorem hd4942 : hp737861 := @hp737855 178956968 536870912 8 536870912 hd4941 rfl

noncomputable def hp737862 := nat_lit 2783654566499630094221312

noncomputable def hp737863 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 10) (@Nat.cast Real Real.instNatCast 1))) Bool.false hp737862 hp630689

noncomputable def hp737864 := BSN.log_rat_reduce_isNear 10 1 3 20 16 7487455 33554432 24973259072661432 36028797018963968 10890000 1000000000000000

noncomputable def hp737865 := BSN.log_dyadic_bound 2 18 4 3 3571283520 33554432 10890000 14806464 960 7487455 20

noncomputable def hp737866 := hp737865 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp737867 := hp737864 rfl rfl rfl rfl (hp737866 (hp707912 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

theorem hd4943 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 100000003267 1089000000000000000 := BSN.isNear_log_sfrac 10 1 10369921350850277 4503599627370496 100000003267 1089000000000000000 Bool.false (@hp737863 1000000032670000 10890000000000000000000 10369921350850277 4503599627370496 100000003267 1089000000000000000 (hp737867 rfl rfl rfl) rfl)

noncomputable def hp737868 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 10369921350850277 4503599627370496 100000003267 1089000000000000000 1236190956

theorem hd4944 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 10 1)) Bool.false 1236190956 536870912 51 536870912 := @hp737868 536870912 51 536870912 hd4943 rfl

noncomputable def hp737869 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10))) Bool.false 21221687 67108864 1 67108864

noncomputable def hp737870 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10))) Bool.false 21221687 67108864 1 67108864

noncomputable def hp737871 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) 212216861 67108864 1 67108864 10610843 10610844

noncomputable def hp737872 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 10) (@Nat.cast Real Real.instNatCast 1))) Bool.false 212216861 67108864

noncomputable def hp737873 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 10) (@Nat.cast Real Real.instNatCast 1))) Bool.false 212216861 67108864

noncomputable def hp737874 := @hp737873 1 67108864 212216861 67108864 1 67108864 (BSN.sqrt_enclosure 10 1 106108430 106108431 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp737875 := @hp737871 33554432 (@hp737872 1 67108864 (BSN.sqrt_natCast_div_one 10) (hp737874 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd4945 : hp737869 := @hp737870 21221687 67108864 1 67108864 hp737875 rfl

noncomputable def hp737876 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10))) Bool.false 169773496 536870912 8 536870912

theorem hd4946 : hp737876 := @hp737870 169773496 536870912 8 536870912 hd4945 rfl

theorem hd4947 : Enclosure.Real.IsNear Real.pi Bool.false 226375608064910080 72057594037927936 1 1000000000000000 := BSN.pi_near_15

theorem hd4948 : hp630533 500000000000000 := @hp630534 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) hd4947 rfl

noncomputable def hp737877 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) Bool.false 10680707 67108864

noncomputable def hp737878 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) Bool.false 10680707 67108864

noncomputable def hp737879 := @hp737878 1 67108864 10680707 67108864 1 67108864 (@hp630537 5340353 5340354 33554432 hd4948 rfl rfl rfl rfl rfl rfl)

theorem hd4949 : hp737877 1 67108864 := hp737879 rfl

noncomputable def hp737934 := nat_lit 282877490902138091004622673603363019119652456796264491099280832830873987773707601701812303598028785564314492868916806270538811366318583631052800

noncomputable def hp737937 := nat_lit 9900712181574833185161793576117705669187835987869257188474829149080589572079766059563430625931007494751007250412088219468858397821150427086848000

noncomputable def hp738018 := @hp731908 1 10680707 67108864 1 67108864 8005734612557 67108864000 749551 67108864000 (Enclosure.Real.IsNear.const Bool.false 749551 1000) hd4949

noncomputable def hp738031 := nat_lit 288230376151711744000000000000000

noncomputable def hp738039 := nat_lit 46199975943266144436568348213124696692647303168343434164427665391357367878632476496239452487680

noncomputable def hp738042 := nat_lit 846999558959879314670419717240619439365200558086296293014507198841551744441595402431056628940800

noncomputable def hp738055 := nat_lit 19342813113834066795298816000000000000000

noncomputable def hp738325 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 749551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp738326 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt hp738325) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 749551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp738327 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv hp738326)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp738326 hp738326) hp738326)))

noncomputable def hp738328 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) hp738327 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt hp738325) (Real.sqrt hp738325)) (Real.sqrt hp738325))))

noncomputable def hp738329 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) hp738328 Bool.false 556919581 10737418240 1213 10737418240

noncomputable def hp738330 := @Enclosure.Real.IsNear.addLit_ff hp738327 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt hp738325) (Real.sqrt hp738325)) (Real.sqrt hp738325))))

noncomputable def hp738331 := @hp738330 34043401 2147483648 201 2147483648 24168911 671088640 13 671088640 74748480840531968 556919581 10737418240

noncomputable def hp738332 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv hp738326)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp738326 hp738326) hp738326)))

noncomputable def hp738333 := @hp738332 4255425 268435456 25 268435456 1 2147483648 1 2147483648 9138455871225856 34043401 2147483648

noncomputable def hp738334 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 25 4) (@Inv.inv Real Real.instInv hp738326) 25 4 0 1 170217 67108864

noncomputable def hp738335 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv hp738326) Bool.false 170217 67108864 1 67108864 170217 67108864

noncomputable def hp738336 := @Enclosure.Real.IsNear.mulLit_ff (Real.sqrt hp738325) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 749551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp738337 := @hp738336 110893277 33554432 3 33554432 8005734612557 67108864000 749551 67108864000 887782145978771079289 2251799813685248000 107137372754951

noncomputable def hp738338 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp738325) Bool.false 221786554 67108864 6 67108864 110893277 33554432 3 33554432

noncomputable def hp738339 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 749551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp738340 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 749551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp738341 := @hp738340 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 749551 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8005734612557

noncomputable def hp738342 := @hp738339 8005734612557 67108864000 749551 67108864000 366488644 366488679 33554432 (@hp738341 67108864000 749551 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 749551 1000) 749551 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))) (hp738018 rfl)) rfl

noncomputable def hp738343 := @Enclosure.Real.IsNear.recentre' hp738325 Bool.false 732977323 67108864 35 67108864 732977323 67108864 35 67108864 (hp738342 rfl rfl rfl rfl rfl)

noncomputable def hp738344 := @Enclosure.Real.IsNear.sqrt_image hp738325 732977323 67108864 35 67108864 110893274 110893280 33554432 (hp738343 rfl) rfl rfl

noncomputable def hp738345 := @hp738337 2251799813685248000 (hp738338 (hp738344 rfl rfl rfl rfl) rfl) (@hp738341 67108864000 749551 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 749551 1000) 749551 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))) (hp738018 rfl)) rfl

noncomputable def hp738346 := @Enclosure.Real.IsNear.inv_image hp738326 887782145978771079289 2251799813685248000 107137372754951 2251799813685248000 85108 85109 33554432 hp738345 rfl rfl

noncomputable def hp738347 := @hp738333 201 2147483648 (@hp738334 1 67108864 4255425 268435456 25 268435456 (Enclosure.Real.IsNear.const Bool.false 25 4) (@hp738335 1 67108864 (hp738346 rfl rfl rfl rfl) rfl) rfl)

noncomputable def hp738348 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 32) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp738326 hp738326) hp738326)) 1

noncomputable def hp738349 := @hp738348 32 0 1 1 67108864 1 67108864 1 2147483648 1 2147483648

noncomputable def hp738350 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp738326 hp738326) hp738326)) Bool.false

noncomputable def hp738351 := nat_lit 699711835980150595180245905227984129706310648210081473838614569

noncomputable def hp738352 := nat_lit 11417981541647679048466287755595961091061972992000000000

noncomputable def hp738353 := @Enclosure.Real.IsNear.inv_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp738326 hp738326) hp738326) hp738351 hp738352

noncomputable def hp738354 := nat_lit 253323286052135260388556242243628849887794883965010409431

noncomputable def hp738355 := nat_lit 788157138718672002428299815462553924745521

noncomputable def hp738356 := nat_lit 5070602400912917605986812821504000000

noncomputable def hp738357 := nat_lit 190229304876252481060209414671632079

noncomputable def hp738358 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp738326 hp738326) hp738326 hp738355 hp738356 hp738357

noncomputable def hp738359 := @Enclosure.Real.IsNear.mulLit_ff hp738326 hp738326 887782145978771079289 2251799813685248000 107137372754951 2251799813685248000 887782145978771079289 2251799813685248000 107137372754951 2251799813685248000 hp738355

noncomputable def hp738360 := @hp738358 hp738356 887782145978771079289 2251799813685248000 107137372754951 2251799813685248000 hp738351 hp738352 hp738354 hp738352 (@hp738359 hp738356 hp738357 hp738356 hp738345 hp738345 rfl) hp738345

noncomputable def hp738361 := @hp738353 hp738354 hp738352 0 1 33554432 (hp738360 rfl) rfl rfl rfl rfl rfl

noncomputable def hp738362 := hp738349 (Enclosure.Real.IsNear.const Bool.false 1 32) (@hp738350 1 67108864 1 67108864 1 67108864 1 67108864 (hp738361 rfl) rfl)

noncomputable def hp738363 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 13 10) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt hp738325) (Real.sqrt hp738325)) (Real.sqrt hp738325))) 13

noncomputable def hp738364 := @hp738363 10 0 1 1859147 67108864 1 67108864 24168911 671088640 13 671088640

noncomputable def hp738365 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt hp738325) (Real.sqrt hp738325)) (Real.sqrt hp738325))) Bool.false

noncomputable def hp738366 := nat_lit 1363689989338423267244933

noncomputable def hp738367 := @Enclosure.Real.IsNear.inv_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt hp738325) (Real.sqrt hp738325)) (Real.sqrt hp738325)) hp738366 37778931862957161709568

noncomputable def hp738368 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Real.sqrt hp738325) (Real.sqrt hp738325)) (Real.sqrt hp738325) 12297318883798729 1125899906842624 665359671

noncomputable def hp738369 := @Enclosure.Real.IsNear.mulLit_ff (Real.sqrt hp738325) (Real.sqrt hp738325) 110893277 33554432 3 33554432 110893277 33554432 3 33554432

noncomputable def hp738370 := @hp738369 12297318883798729 1125899906842624 665359671 1125899906842624 (hp738338 (hp738344 rfl rfl rfl rfl) rfl) (hp738338 (hp738344 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp738371 := @hp738368 1125899906842624 110893277 33554432 3 33554432 hp738366 37778931862957161709568 110675872948307067 37778931862957161709568 hp738370 (hp738338 (hp738344 rfl rfl rfl rfl) rfl)

noncomputable def hp738372 := @hp738367 110675872948307067 37778931862957161709568 929573 929574 33554432 (hp738371 rfl) rfl rfl rfl rfl rfl

noncomputable def hp738373 := hp738364 (Enclosure.Real.IsNear.const Bool.false 13 10) (@hp738365 1859147 67108864 1 67108864 1859147 67108864 1 67108864 (hp738372 rfl) rfl)

noncomputable def hp738374 := hp738329 (BSN.hardyZErrorBoundRS₀_mk (Enclosure.sfrac Bool.false 749551 1000) 749551 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000)) rfl rfl) (@hp738331 1213 10737418240 (hp738347 (hp738362 rfl) rfl rfl) (hp738373 rfl) rfl rfl)

theorem hd4952 : Enclosure.Real.IsNear (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) Bool.false 556919581 10737418240 1213 10737418240 := hp738374

noncomputable def hp738659 := nat_lit 17842176000000000000000000

noncomputable def hp739140 := nat_lit 4460544000000000000000000

noncomputable def hp739631 := nat_lit 8921088000000000000000000

noncomputable def hp740070 := nat_lit 2898877505641241362038784

noncomputable def hp740071 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 11) (@Nat.cast Real Real.instNatCast 1))) Bool.false hp740070 hp630689

noncomputable def hp740072 := BSN.log_rat_reduce_isNear 11 1 3 22 16 10685534 33554432 24973259072661432 36028797018963968 10890000 1000000000000000

noncomputable def hp740073 := BSN.log_dyadic_bound 3 19 5 4 16049467073745 33554432 10890000 135406373544 688905 10685534 22

noncomputable def hp740074 := hp740073 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp740075 := @BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 19) 0 4 135406373544 16049467073745 688905 rfl rfl rfl

noncomputable def hp740076 := hp740072 rfl rfl rfl rfl (hp740074 (hp740075 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

theorem hd4960 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 100000003267 1089000000000000000 := BSN.isNear_log_sfrac 11 1 10799160248194789 4503599627370496 100000003267 1089000000000000000 Bool.false (@hp740071 1000000032670000 10890000000000000000000 10799160248194789 4503599627370496 100000003267 1089000000000000000 (hp740076 rfl rfl rfl) rfl)

noncomputable def hp740077 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 10799160248194789 4503599627370496 100000003267 1089000000000000000 1287360220

theorem hd4961 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 11 1)) Bool.false 1287360220 536870912 51 536870912 := @hp740077 536870912 51 536870912 hd4960 rfl

noncomputable def hp740078 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11))) Bool.false 20234083 67108864 1 67108864

noncomputable def hp740079 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11))) Bool.false 20234083 67108864 1 67108864

noncomputable def hp740080 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) 222574921 67108864 1 67108864 10117041 10117042

noncomputable def hp740081 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 11) (@Nat.cast Real Real.instNatCast 1))) Bool.false 222574921 67108864

noncomputable def hp740082 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 11) (@Nat.cast Real Real.instNatCast 1))) Bool.false 222574921 67108864

noncomputable def hp740083 := @hp740082 1 67108864 222574921 67108864 1 67108864 (BSN.sqrt_enclosure 11 1 111287460 111287461 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp740084 := @hp740080 33554432 (@hp740081 1 67108864 (BSN.sqrt_natCast_div_one 11) (hp740083 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd4962 : hp740078 := @hp740079 20234083 67108864 1 67108864 hp740084 rfl

noncomputable def hp740085 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11))) Bool.false 161872664 536870912 8 536870912

theorem hd4963 : hp740085 := @hp740079 161872664 536870912 8 536870912 hd4962 rfl

noncomputable def hp740088 := nat_lit 25713285499225218188574720000

noncomputable def hp740271 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (Enclosure.sfrac Bool.true 1 1) Bool.true 1

noncomputable def hp740893 := nat_lit 2973696000000000000000000

noncomputable def hp741092 := nat_lit 14285158610680676771430400

noncomputable def hp741590 := nat_lit 17142190332816812125716480000

noncomputable def hp742826 := nat_lit 3868562622766813359059763200000000000000

noncomputable def hp744142 := nat_lit 3568435200000000000000000

noncomputable def hp745658 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600

noncomputable def hp745661 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600

noncomputable def hp748549 := nat_lit 285703172213613535428608000

noncomputable def hp749778 := nat_lit 42817430781178796431748579083484854091482398720

noncomputable def hp749779 := nat_lit 299722015468251575022240053584393978640376791040

noncomputable def hp749816 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 806921 1000)) Bool.true 2227330288615246330305 295147905179352825856 209648501612658346520693

noncomputable def hp749817 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 806921 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 806921 1000)) Bool.true 2227330288615246330305 295147905179352825856

noncomputable def hp749818 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 806921 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749819 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp749818 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749820 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 806921 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749821 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp749819 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp749822 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 806921 1000)) hp749821 Bool.true 2227330288615246330305 295147905179352825856

noncomputable def hp749823 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 806921 1000) 806921 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl

noncomputable def hp749824 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp749819 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp749825 := nat_lit 149473605421761314306937323520

noncomputable def hp749826 := @hp749824 515076145 67108864 195809 268435456 37998553854901683775 295147905179352825856 1243646003809667608693 hp748549 hp749825 2227330288615246330305 295147905179352825856

noncomputable def hp749827 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) 11)

noncomputable def hp749828 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) 11) hp749827

noncomputable def hp749829 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) 11)

noncomputable def hp749830 := @hp749829 2060304580 536870912 195809 536870912 2060304580 536870912 195809 536870912 2212235197724753920 515076145 67108864

noncomputable def hp749831 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp749832 := hp749831 BSN.quadSignNeg 9 10 11 806921 1000 192 241 536870912 268435456 9007199254740992

noncomputable def hp749833 := hp749832 Bool.false 834881643587 3677 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp749834 := hp749833 Bool.true 1947713650 168096 Bool.true 710346365 Bool.true 677472071 28296951008113761 1 Bool.false 131613230

noncomputable def hp749835 := hp749834 Bool.false Bool.false 511459015 Bool.true Bool.true 2060304580 195809 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 131613230 536870912) BSN.abs_quadSignNeg

noncomputable def hp749836 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp749837 := hp749836 BSN.quadSignNeg 7 8 9 806921 1000 78 138 536870912 268435456 9007199254740992

noncomputable def hp749838 := hp749837 Bool.false 834881643587 3677 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp749839 := hp749838 Bool.true 1691836034 137283 Bool.true 179685193 Bool.true 605855797 28296951008113761 1 Bool.false 507081160

noncomputable def hp749840 := hp749839 Bool.true Bool.false 229792047 Bool.true Bool.true 1947713650 168096 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 507081160 536870912) BSN.abs_quadSignNeg

noncomputable def hp749841 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp749842 := hp749841 BSN.quadSignNeg 5 6 7 806921 1000 69 9 536870912 268435456 9007199254740992

noncomputable def hp749843 := hp749842 Bool.false 834881643587 3677 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp749844 := hp749843 Bool.true 1353415096 102017 Bool.false 480480894 Bool.true 520941790 28296951008113761 1 Bool.false 418859943

noncomputable def hp749845 := hp749844 Bool.true Bool.false 442957182 Bool.true Bool.true 1691836034 137283 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 418859943 536870912) BSN.abs_quadSignNeg

noncomputable def hp749846 := hp749841 BSN.quadSignPos 3 4 5 806921 1000 277 163 536870912 268435456 9007199254740992

noncomputable def hp749847 := hp749846 Bool.false 834881643587 3677 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp749848 := hp749847 Bool.true 1176038771 60297 Bool.false 723514026 Bool.false 192852854 28296951008113761 1 Bool.false 523559720

noncomputable def hp749849 := hp749848 Bool.true Bool.false 188732022 Bool.false Bool.true 1353415096 102017 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 277 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 523559720 536870912) BSN.abs_quadSignPos

noncomputable def hp749850 := hp749841 BSN.quadSignNeg 1 2 3 806921 1000 633 425 536870912 268435456 9007199254740992

noncomputable def hp749851 := hp749850 Bool.false 834881643587 3677 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp749852 := hp749851 Bool.true 536870904 3730 Bool.false 783388706 Bool.false 540353153 28296951008113761 1 Bool.false 533529870

noncomputable def hp749853 := hp749852 Bool.true Bool.false 453633241 Bool.true Bool.true 1176038771 60297 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 633 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533529870 536870912) BSN.abs_quadSignNeg

noncomputable def hp749854 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) 1) Bool.true

noncomputable def hp749855 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)))

noncomputable def hp749856 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000))) Bool.true 67108863 67108864

noncomputable def hp749857 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 13045025681) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 13045025681 8388608

noncomputable def hp749858 := nat_lit 69599147814788156179343979080175937172645902990547314925879

noncomputable def hp749859 := nat_lit 44755754601576322237217429471712578990817029155454976000

noncomputable def hp749860 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) Bool.false hp749858 hp749859 122174788698792506783

noncomputable def hp749861 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 806921 4000) (Real.log (Enclosure.sfrac Bool.false 2604487000964 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1613842))))))

noncomputable def hp749862 := nat_lit 164208922029867747748287237728480000

noncomputable def hp749863 := nat_lit 795021907890293317628359472445832860480

noncomputable def hp749864 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp749861 (Enclosure.sfrac Bool.false 806921 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 806921 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp749862 hp749863)) Bool.false

noncomputable def hp749865 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 806921 1000) 806921 1000 2604487000964 16000000 1613842

noncomputable def hp749866 := hp749865 4000 2000 hp749862 hp749863 (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl rfl rfl rfl

noncomputable def hp749867 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp749861 (Enclosure.sfrac Bool.false 806921 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 806921 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp749862 hp749863) 28013983058603325151711 18014398509481984000

noncomputable def hp749868 := nat_lit 22271727300732209977390073305656299895246688956975140776281280

noncomputable def hp749869 := @hp749867 122174788698792506783 hp738659 hp749862 hp749863 0 1 hp749868 hp749858 hp749859 122174788698792506783 hp738659

noncomputable def hp749870 := @Enclosure.Real.IsNear.subLit_ff_p (hp749861 (Enclosure.sfrac Bool.false 806921 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 806921 2000) (Real.log Real.pi)) 36333992291085929044447 18014398509481984000 10186527439072973 4356000000000000000000

noncomputable def hp749871 := nat_lit 1879986579178114577553952866304000

noncomputable def hp749872 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 806921 4000) (Real.log (Enclosure.sfrac Bool.false 2604487000964 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1613842))))))

noncomputable def hp749873 := @hp749872 (Enclosure.sfrac Bool.false 806921 2000) 43602090520920785050079 18014398509481984000 10186527439072973 4356000000000000000000 806921 2000 0

noncomputable def hp749874 := nat_lit 72667984582171858088894000

noncomputable def hp749875 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 806921 4000) (Real.log (Enclosure.sfrac Bool.false 2604487000964 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1613842))))) 43609161968152030642079

noncomputable def hp749876 := nat_lit 98183179311296741688861013949223534592

noncomputable def hp749877 := @hp749875 18014398509481984000 10086527438528473 4356000000000000000000 883930903905699 2251799813685248 200000001089 8712000000000000000 hp749876 43602090520920785050079 18014398509481984000 10186527439072973

noncomputable def hp749878 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 806921 4000) (Real.log (Enclosure.sfrac Bool.false 2604487000964 16000000)) 806921 4000 0 1 54043905125968999 4503599627370496

noncomputable def hp749879 := nat_lit 116058402532081805507428352

noncomputable def hp749880 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2604487000964) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp749879 hp617687

noncomputable def hp749881 := BSN.log_rat_reduce_isNear 2604487000964 16000000 17 5208974001928 4194304000000 58158016 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp749882 := nat_lit 225645174648170099964018160656430509311715808065839335612159593060298095600357546071575288675958216785920

noncomputable def hp749883 := nat_lit 881951492301165298896391049917572309663880183399603135386822107793196517684548281593674768507759755264

noncomputable def hp749884 := nat_lit 460837594655423209189461631951630598938872155791679827349069495617876129532621454527212139642880

noncomputable def hp749885 := BSN.log_dyadic_bound 507335000964 4701639000964 5 4 hp749882 268435456 87120000 hp749883 hp749884 58158016 5208974001928

noncomputable def hp749886 := hp749885 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp749887 := @BSN.binarySplit_of_base4 (BSN.artanhP 507335000964) (BSN.artanhQ 4701639000964) 0 4 hp749883 hp749882 hp749884 rfl rfl rfl

noncomputable def hp749888 := hp749881 rfl rfl rfl rfl (hp749886 (hp749887 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp749889 := @hp749878 12500018513 1089000000000000000 43609161968152030642079 18014398509481984000 10086527438528473 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 806921 4000) (BSN.isNear_log_sfrac 2604487000964 16000000 54043905125968999 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp749880 1000001481040000 87120000000000000000000 54043905125968999 4503599627370496 12500018513 1089000000000000000 (hp749888 rfl rfl rfl) rfl)) rfl

noncomputable def hp749890 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1613842)))) 1 4

noncomputable def hp749891 := @hp749890 0 1 883930903905699 562949953421312 200000001089 2178000000000000000 883930903905699 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp749892 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1613842))) 884279719003555 562949953421312 1

noncomputable def hp749893 := @hp749892 2000000000000000 20791 33554432 1 10890000 29659799407802311507968 883930903905699 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp749894 := BSN.arctan_dyadic_bound_f 1000 1613842 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp749895 := hp749894 1 20791 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1613842) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1613842) 0 0 rfl)

noncomputable def hp749896 := hp749891 (hp749893 (hp749895 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp749897 := @hp749870 30994449676881 67108864000 2420763 536870912000 hp749871 28013983058603325151711 18014398509481984000 122174788698792506783 hp738659 (@hp749873 1 hp749874 36333992291085929044447 18014398509481984000 10186527439072973 4356000000000000000000 (@hp749877 4356000000000000000000 hp749889 hp749896 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 806921 2000) rfl rfl)

noncomputable def hp749898 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 806921 2000) (Real.log Real.pi) 806921 2000 0 1 38410761 33554432

noncomputable def hp749899 := hp749897 (@hp749898 3 268435456 30994449676881 67108864000 2420763 536870912000 (Enclosure.Real.IsNear.const Bool.false 806921 2000) hd4909 rfl) rfl

noncomputable def hp749900 := @hp749860 hp738659 13045025681 8388608 115 16777216 (@hp749864 hp749858 hp749859 122174788698792506783 hp738659 (hp749866 rfl rfl rfl rfl rfl) (hp749869 (hp749899 rfl) (Enclosure.Real.IsNear.const Bool.true hp749862 hp749863) rfl rfl)) rfl

noncomputable def hp749901 := nat_lit 1898831258515471306063872

noncomputable def hp749902 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 13045025681) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp749901) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp749903 := BSN.sin_reduce_arg_pos_rat_q1 13045025681 8388608 226375608064910080 72057594037927936 247 hp749901 hp630689 rfl rfl rfl rfl

noncomputable def hp749904 := nat_lit 14375982315516665870570840668181820410424615567227149299368479753113214286430211710840776083258267379891634770991164382278394591720776191317841

noncomputable def hp749905 := nat_lit 10241385332200865500268618588515162672611944757280413643621429016951739273191368190947407992859491340495521474357676537539451817348437841

noncomputable def hp749906 := nat_lit 71790619148815211180635091106189465893756117115938601006515527652085579125732867112164857655672192710118012475725252381990118678202483904485201

noncomputable def hp749907 := BSN.sin_dyadic_bound_f 215872121147 137438953472 4 3 67108864 21801270 hp749904 hp737934 hp749905 hp749906 hp737937

noncomputable def hp749908 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215872121147) (BSN.sinEvenQ 137438953472) 0 3 hp749904 hp737934 hp749905 rfl rfl rfl

noncomputable def hp749909 := hp749907 hp749905 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (hp749908 rfl)

noncomputable def hp749910 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215872121147) (BSN.sinOddQ 137438953472) 0 3 hp749906 hp737937 hp749905 rfl rfl rfl

noncomputable def hp749911 := @BSN.sin_arg_round Bool.false 67108863 67108864 hp749901 hp630689 215872121147 137438953472 21801270 21780000 (hp749909 (hp749910 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749912 := hp749902 67108863 67108864 247 1000000000000000 21780000 10890000 hp749903 BSN.pi_near_15 hp749911 rfl rfl

noncomputable def hp749913 := @hp749857 115 16777216 Bool.true 67108863 67108864 1 10890000 hp749900 (Enclosure.sfrac_false_div 13045025681 8388608) (hp749912 rfl rfl) rfl

noncomputable def hp749914 := @hp749854 67108863 67108864 79320451 11418992640000 536870904 536870912 3730 536870912 (@hp749855 Bool.true 67108863 67108864 79320451 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000)) (@hp749856 1269127216 182703882240000 67108863 67108864 79320451 11418992640000 (hp749913 rfl) rfl))

noncomputable def hp749915 := @hp749860 hp738659 834881643587 536870912 3677 536870912 (@hp749864 hp749858 hp749859 122174788698792506783 hp738659 (hp749866 rfl rfl rfl rfl rfl) (hp749869 (hp749899 rfl) (Enclosure.Real.IsNear.const Bool.true hp749862 hp749863) rfl rfl)) rfl

noncomputable def hp749916 := hp749853 (BSN.cos_quad_nat1 425 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 453633241 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl rfl (hp749914 rfl) hp749915

noncomputable def hp749917 := nat_lit 135088397491684828315723233912199007643953101178125483425560046988632550620931754771434839611955387265866749710336

noncomputable def hp749918 := nat_lit 53422926283709686734846973891896617580886778424739677106960760708354475397382609656847483437777929747828736

noncomputable def hp749919 := nat_lit 674816742905773611449563087946487275861251658212422894124043781506801691406611482572558616279711612586649524637696

noncomputable def hp749920 := BSN.sin_dyadic_bound_f 783388706 536870912 4 3 536870912 268435456 hp749917 hp642702 hp749918 hp749919 hp642705

noncomputable def hp749921 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 783388706) (BSN.sinEvenQ 536870912) 0 3 hp749917 hp642702 hp749918 rfl rfl rfl

noncomputable def hp749922 := hp749920 hp749918 533529870 rfl rfl rfl rfl rfl rfl rfl rfl (hp749921 rfl)

noncomputable def hp749923 := @BSN.binarySplit_of_base3 (BSN.sinOddP 783388706) (BSN.sinOddQ 536870912) 0 3 hp749919 hp642705 hp749918 rfl rfl rfl

noncomputable def hp749924 := nat_lit 21424929278596997801037910003738168635838777382233746511336762049310495745

noncomputable def hp749925 := nat_lit 7268110469376063378362797903753924367952017156242494920864960901288961

noncomputable def hp749926 := nat_lit 56101142598422671090581938813184363882982018449502086347438690668639687681

noncomputable def hp749927 := BSN.sin_dyadic_bound_f 540353153 536870912 3 2 536870912 268435456 hp749924 hp708845 hp749925 hp749926 hp708848

noncomputable def hp749928 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 540353153) (BSN.sinEvenQ 536870912) 0 2 hp749924 hp708845 hp749925 rfl rfl rfl

noncomputable def hp749929 := hp749927 hp749925 453633241 rfl rfl rfl rfl rfl rfl rfl rfl (hp749928 rfl)

noncomputable def hp749930 := @BSN.binarySplit_of_base2 (BSN.sinOddP 540353153) (BSN.sinOddQ 536870912) 0 2 hp749926 hp708848 hp749925 rfl rfl rfl

noncomputable def hp749931 := hp749916 hd4911 hd4913 hd4915 hd4917 hd4918 (hp749922 (hp749923 rfl) rfl rfl rfl rfl) (hp749929 (hp749930 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749932 := hp749849 (BSN.cos_quad_nat3 163 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 188732022 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl rfl (hp749931 rfl rfl rfl rfl rfl) hp749915

noncomputable def hp749933 := nat_lit 98247028582749924006466215468607613835376798240826007076908032869765324256582662156479436151441503408637627928576

noncomputable def hp749934 := nat_lit 20576118714459291042357752372676134494963336380876397326753568155380188364295756239236584877356921776050176

noncomputable def hp749935 := nat_lit 490904189650152167356251043474676390530053908204891612616960078555208428663955812843142752939422183914546322804736

noncomputable def hp749936 := BSN.sin_dyadic_bound_f 723514026 536870912 4 3 536870912 268435456 hp749933 hp642702 hp749934 hp749935 hp642705

noncomputable def hp749937 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 723514026) (BSN.sinEvenQ 536870912) 0 3 hp749933 hp642702 hp749934 rfl rfl rfl

noncomputable def hp749938 := hp749936 hp749934 523559720 rfl rfl rfl rfl rfl rfl rfl rfl (hp749937 rfl)

noncomputable def hp749939 := @BSN.binarySplit_of_base3 (BSN.sinOddP 723514026) (BSN.sinOddQ 536870912) 0 3 hp749935 hp642705 hp749934 rfl rfl rfl

noncomputable def hp749940 := nat_lit 1383261473695457464538566062339856

noncomputable def hp749941 := BSN.sin_dyadic_bound_f 192852854 536870912 2 1 536870912 268435456 hp749940 hp708890 hp749940 hp749940 hp708891

noncomputable def hp749942 := @BSN.binarySplit_of_base (BSN.sinEvenP 192852854) (BSN.sinEvenQ 536870912) 0 1 hp749940 hp708890 hp749940 rfl rfl rfl

noncomputable def hp749943 := hp749941 hp749940 188732022 rfl rfl rfl rfl rfl rfl rfl rfl (hp749942 rfl)

noncomputable def hp749944 := @BSN.binarySplit_of_base (BSN.sinOddP 192852854) (BSN.sinOddQ 536870912) 0 1 hp749940 hp708891 hp749940 rfl rfl rfl

noncomputable def hp749945 := hp749932 hd4920 hd4922 hd4924 hd4926 hd4918 (hp749938 (hp749939 rfl) rfl rfl rfl rfl) (hp749943 (hp749944 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749946 := hp749845 (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 442957182 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl rfl (hp749945 rfl rfl rfl rfl rfl) hp749915

noncomputable def hp749947 := nat_lit 13392384246976550098517659858817175076195148430254278351559932698624917760

noncomputable def hp749948 := nat_lit 2840592809431715225265262607460386014165636195565133160517014277980416

noncomputable def hp749949 := nat_lit 35070693020389979861943441586013856003154834858730290228968510473281863936

noncomputable def hp749950 := BSN.sin_dyadic_bound_f 480480894 536870912 3 2 536870912 268435456 hp749947 hp708845 hp749948 hp749949 hp708848

noncomputable def hp749951 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 480480894) (BSN.sinEvenQ 536870912) 0 2 hp749947 hp708845 hp749948 rfl rfl rfl

noncomputable def hp749952 := hp749950 hp749948 418859943 rfl rfl rfl rfl rfl rfl rfl rfl (hp749951 rfl)

noncomputable def hp749953 := @BSN.binarySplit_of_base2 (BSN.sinOddP 480480894) (BSN.sinOddQ 536870912) 0 2 hp749949 hp708848 hp749948 rfl rfl rfl

noncomputable def hp749954 := nat_lit 18507398325363023946825472059599375719812867737375284918894350485383840000

noncomputable def hp749955 := nat_lit 5423923853000343325859778891349527308970740525714287892668176100000000

noncomputable def hp749956 := nat_lit 48462975927807824066777225275983799079104891446560304035754217081367200000

noncomputable def hp749957 := BSN.sin_dyadic_bound_f 520941790 536870912 3 2 536870912 268435456 hp749954 hp708845 hp749955 hp749956 hp708848

noncomputable def hp749958 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 520941790) (BSN.sinEvenQ 536870912) 0 2 hp749954 hp708845 hp749955 rfl rfl rfl

noncomputable def hp749959 := hp749957 hp749955 442957182 rfl rfl rfl rfl rfl rfl rfl rfl (hp749958 rfl)

noncomputable def hp749960 := @BSN.binarySplit_of_base2 (BSN.sinOddP 520941790) (BSN.sinOddQ 536870912) 0 2 hp749956 hp708848 hp749955 rfl rfl rfl

noncomputable def hp749961 := hp749946 hd4928 hd4930 hd4932 hd4934 hd4918 (hp749952 (hp749953 rfl) rfl rfl rfl rfl) (hp749959 (hp749960 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749962 := hp749840 (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 229792047 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl rfl (hp749961 rfl rfl rfl rfl rfl) hp749915

noncomputable def hp749963 := nat_lit 145492693574259719396177256320171788367339494271855998032160852152156481

noncomputable def hp749964 := nat_lit 1086671616464702201553958042797822284867778513250945755398955336001

noncomputable def hp749965 := nat_lit 436475907379546228784128661044429769457448747258541492204971758545797441

noncomputable def hp749966 := BSN.cos_dyadic_bound_f 179685193 536870912 3 2 536870912 268435456 hp749963 hp708868 hp749964 hp749965 hp708870

noncomputable def hp749967 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 179685193) (BSN.cosEvenQ 536870912) 0 2 hp749963 hp708868 hp749964 rfl rfl rfl

noncomputable def hp749968 := hp749966 hp749964 507081160 rfl rfl rfl rfl rfl rfl rfl rfl (hp749967 rfl)

noncomputable def hp749969 := @BSN.binarySplit_of_base2 (BSN.cosOddP 179685193) (BSN.cosOddQ 536870912) 0 2 hp749965 hp708870 hp749964 rfl rfl rfl

noncomputable def hp749970 := nat_lit 18577227163136544279477192621402528709361486296712812410293736967298862196672913051727347686890518427859935903121

noncomputable def hp749971 := nat_lit 2445857847533899798738518227494023728660334663116923103802659320067479884979382989579672062602643623460241

noncomputable def hp749972 := nat_lit 112629370624801624338430457861349563044490516518250739568116782523645204243531082262886244150665100868163759586705

noncomputable def hp749973 := BSN.cos_dyadic_bound_f 605855797 536870912 4 3 536870912 268435456 hp749970 hp716712 hp749971 hp749972 hp716714

noncomputable def hp749974 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 605855797) (BSN.cosEvenQ 536870912) 0 3 hp749970 hp716712 hp749971 rfl rfl rfl

noncomputable def hp749975 := hp749973 hp749971 229792047 rfl rfl rfl rfl rfl rfl rfl rfl (hp749974 rfl)

noncomputable def hp749976 := @BSN.binarySplit_of_base3 (BSN.cosOddP 605855797) (BSN.cosOddQ 536870912) 0 3 hp749972 hp716714 hp749971 rfl rfl rfl

noncomputable def hp749977 := hp749962 hd4936 hd4938 hd4940 hd4942 hd4918 (hp749968 (hp749969 rfl) rfl rfl rfl rfl) (hp749975 (hp749976 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749978 := hp749835 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 511459015 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl rfl (hp749977 rfl rfl rfl rfl rfl) hp749915

noncomputable def hp749979 := nat_lit 35136388769671398155247964613076755983839139855140004359129794850607983996913784873437112897747667616665470640625

noncomputable def hp749980 := nat_lit 16506004115555970917213245089059420956765162171173058916362608986057544972961782324183344157405351806640625

noncomputable def hp749981 := nat_lit 212901903603418204345061002961726635539784586375997839538460383807507668818292144929844704841933964598028568240625

noncomputable def hp749982 := BSN.cos_dyadic_bound_f 710346365 536870912 4 3 536870912 268435456 hp749979 hp716712 hp749980 hp749981 hp716714

noncomputable def hp749983 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 710346365) (BSN.cosEvenQ 536870912) 0 3 hp749979 hp716712 hp749980 rfl rfl rfl

noncomputable def hp749984 := hp749982 hp749980 131613230 rfl rfl rfl rfl rfl rfl rfl rfl (hp749983 rfl)

noncomputable def hp749985 := @BSN.binarySplit_of_base3 (BSN.cosOddP 710346365) (BSN.cosOddQ 536870912) 0 3 hp749981 hp716714 hp749980 rfl rfl rfl

noncomputable def hp749986 := nat_lit 75507085365257920493276283994539771710979653411954503663825492198346813871008198355672183230811482199502043953441

noncomputable def hp749987 := nat_lit 9347527507697078677068722755597951388049967616588309040759034879892690594979843643176159576975252654078241

noncomputable def hp749988 := nat_lit 377339859084980842669173140218176092798262047261058240810612246867133094211039805480222321294208810695795316570401

noncomputable def hp749989 := BSN.sin_dyadic_bound_f 677472071 536870912 4 3 536870912 268435456 hp749986 hp642702 hp749987 hp749988 hp642705

noncomputable def hp749990 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 677472071) (BSN.sinEvenQ 536870912) 0 3 hp749986 hp642702 hp749987 rfl rfl rfl

noncomputable def hp749991 := hp749989 hp749987 511459015 rfl rfl rfl rfl rfl rfl rfl rfl (hp749990 rfl)

noncomputable def hp749992 := @BSN.binarySplit_of_base3 (BSN.sinOddP 677472071) (BSN.sinOddQ 536870912) 0 3 hp749988 hp642705 hp749987 rfl rfl rfl

noncomputable def hp749993 := hp749978 hd4944 hd4946 hd4961 hd4963 hd4918 (hp749984 (hp749985 rfl) rfl rfl rfl rfl) (hp749991 (hp749992 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749994 := @hp749830 195809 268435456 (hp749993 rfl rfl rfl rfl rfl) (hp749993 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp749995 := @hp749828 Bool.true 515076145 67108864 195809 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 806921 1000)) (Enclosure.sfrac Bool.false 806921 1000) 11) hp749994

noncomputable def hp749996 := @Enclosure.Real.IsNear.mulLit_tf hp749819 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1))) 311485 1048576 1

noncomputable def hp749997 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp749818 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749998 := @hp749997 1 1 0 1 311485 1048576 1 33554432 311485 1048576 1

noncomputable def hp749999 := @Enclosure.Real.IsNear.of_eq (hp749818 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750000 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 806921 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750001 := @hp749999 (@Inv.inv Real Real.instInv (Real.sqrt hp749820)) Bool.false 311485 1048576 1 33554432 (hp750000 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 806921 1000) 806921 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000))))

noncomputable def hp750002 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp749820)) Bool.false 19935040 67108864 2 67108864 311485 1048576

noncomputable def hp750003 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp749820) Bool.false 225913753 67108864 7 67108864 225913753 67108864 7 67108864

noncomputable def hp750004 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 806921 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750005 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 806921 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750006 := @hp750005 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 806921 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8618486773147

noncomputable def hp750007 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 806921 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 806921 1000 0

noncomputable def hp750008 := @hp750007 1 10680707 67108864 1 67108864 8618486773147 67108864000 806921 67108864000 (Enclosure.Real.IsNear.const Bool.false 806921 1000) hd4949

noncomputable def hp750009 := @hp750006 67108864000 806921 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 806921 1000) 806921 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000))) (hp750008 rfl)

noncomputable def hp750010 := @hp750004 8618486773147 67108864000 806921 67108864000 380255441 380255477 33554432 hp750009 rfl rfl rfl

noncomputable def hp750011 := @Enclosure.Real.IsNear.recentre' hp749820 Bool.false 760510918 67108864 36 67108864 380255459 33554432 9 16777216 (hp750010 rfl rfl rfl)

noncomputable def hp750012 := @Enclosure.Real.IsNear.sqrt_image hp749820 380255459 33554432 9 16777216 112956873 112956880 33554432 (hp750011 rfl) rfl rfl

noncomputable def hp750013 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp749820) 225913753 67108864 7 67108864 9967519 9967521 33554432 (hp750003 (hp750012 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp750014 := @hp749998 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp750001 (@hp750002 1 33554432 (hp750013 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp750015 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750016 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp750017 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1))) (hp750015 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750016 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp750018 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 806921 1000) 806921 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl

noncomputable def hp750019 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750020 := @hp750019 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750016 (Enclosure.sfrac Bool.false 1 16)))) 135454265

noncomputable def hp750021 := @hp750020 67108864 955 67108864 900611 4194304 130735277 22837985280000 121991601055915 281474976710656 124399613291783 8514618045497344000

noncomputable def hp750022 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750023 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750024 := @hp750022 (@Neg.neg Real Real.instNeg hp750023) Bool.true 135454265 67108864 955 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750025 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750026 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp750027 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp750028 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 70099657) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp750029 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1))) Bool.false 9865649730964995093385

noncomputable def hp750030 := nat_lit 9714987149172564031702999

noncomputable def hp750031 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp750032 := @Enclosure.Real.IsNear.subLit_ff_p hp749820 (Enclosure.sfrac Bool.false 11 1) 380255459 33554432 9 16777216 11 1 0

noncomputable def hp750033 := @hp750031 500000000000000 11156707 33554432 9 16777216 9865649730964995093385 4722366482869645213696 hp750030 hp631501 hd4948 (@hp750032 1 11156707 11156707 33554432 9 16777216 (hp750011 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750034 := @hp750028 70099657 33554432 57 16777216 Bool.true 33248120 67108864 1 10890000 (@hp750029 4722366482869645213696 hp750030 hp631501 70099657 33554432 57 16777216 (hp750033 rfl) rfl) (Enclosure.sfrac_false_div 70099657 33554432)

noncomputable def hp750035 := nat_lit 2506520305335309743161344

noncomputable def hp750036 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 70099657) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp750035) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp750037 := BSN.sin_reduce_arg_pos_rat_q1 70099657 33554432 226375608064910080 72057594037927936 0 hp750035 hp619237 rfl rfl rfl rfl

noncomputable def hp750038 := nat_lit 25756431319145366825530602625606473877072801

noncomputable def hp750039 := BSN.sin_dyadic_bound_f 71239591799 137438953472 2 1 67108864 21801270 hp750038 hp749778 hp750038 hp750038 hp749779

noncomputable def hp750040 := @BSN.binarySplit_of_base (BSN.sinEvenP 71239591799) (BSN.sinEvenQ 137438953472) 0 1 hp750038 hp749778 hp750038 rfl rfl rfl

noncomputable def hp750041 := hp750039 hp750038 33248120 rfl rfl rfl rfl rfl rfl rfl rfl (hp750040 rfl)

noncomputable def hp750042 := @BSN.binarySplit_of_base (BSN.sinOddP 71239591799) (BSN.sinOddQ 137438953472) 0 1 hp750038 hp749779 hp750038 rfl rfl rfl

noncomputable def hp750043 := @BSN.sin_arg_round Bool.false 33248120 67108864 hp750035 hp619237 71239591799 137438953472 21801270 21780000 (hp750041 (hp750042 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750044 := hp750036 33248120 67108864 0 1000000000000000 21780000 10890000 hp750037 BSN.pi_near_15 hp750043 rfl rfl

noncomputable def hp750045 := @hp750026 4156015 8388608 39844201 11418992640000 (@hp750027 33248120 67108864 637507216 182703882240000 4156015 8388608 39844201 11418992640000 (hp750034 (hp750044 rfl rfl) rfl rfl) rfl)

noncomputable def hp750046 := @hp750025 4156015 8388608 39844201 11418992640000 67726655 67727610 33554432 hp750045 rfl rfl rfl

noncomputable def hp750047 := @Enclosure.Real.IsNear.recentre' hp750023 Bool.false 135454265 67108864 955 67108864 135454265 67108864 955 67108864 (hp750046 rfl rfl rfl)

noncomputable def hp750048 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750016 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp750049 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750016 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 119937223)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp750050 := nat_lit 283193762948535713609954144645

noncomputable def hp750051 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750016 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp750050

noncomputable def hp750052 := nat_lit 1696111189873929081204930746424517

noncomputable def hp750053 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750016 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp750054 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp750055 := @hp750054 (Enclosure.sfrac Bool.false 1 16) 249884855291575 1125899906842624 62851347 70368744177664 1 16 0

noncomputable def hp750056 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)) 124472111083849

noncomputable def hp750057 := @hp750056 1125899906842624 25102611 70368744177664 11156707 33554432 9 16777216 8384744384710993510400 249884855291575 1125899906842624 62851347

noncomputable def hp750058 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)) 11156707 33554432 9

noncomputable def hp750059 := @hp750058 16777216 11156707 33554432 9 16777216 124472111083849 1125899906842624 25102611 70368744177664 (@hp750032 1 11156707 11156707 33554432 9 16777216 (hp750011 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750060 := hp750059 (@hp750032 1 11156707 11156707 33554432 9 16777216 (hp750011 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750061 := @hp750057 70368744177664 (hp750060 rfl) (@hp750032 1 11156707 11156707 33554432 9 16777216 (hp750011 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750062 := @hp750053 500000000000000 320253599469239 1125899906842624 62851347 70368744177664 hp750050 hp682141 hp750052 hp634263 hd4948 (@hp750055 1 5124057591507824 320253599469239 1125899906842624 62851347 70368744177664 (hp750061 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp750063 := @hp750049 119937223 67108864 189 33554432 Bool.true 7204888 33554432 1 10890000 (@hp750051 hp682141 hp750052 hp634263 119937223 67108864 189 33554432 (hp750062 rfl) rfl) (Enclosure.sfrac_true_div 119937223 67108864)

noncomputable def hp750064 := nat_lit 1709276904016656317416672604648143858659941463739374110899231878241627209924147190192651195458647988001

noncomputable def hp750065 := nat_lit 8860288612771240063138508862418432443081155375656295968561657918075903921160344287138149819193121

noncomputable def hp750066 := nat_lit 10327840401796996205146314628768566110723952779082002551225140311359860975820775240890943679217854813985

noncomputable def hp750067 := BSN.cos_dyadic_bound_t 119937223 67108864 4 3 33554432 10890000 hp750064 hp745658 hp750065 hp750066 hp745661

noncomputable def hp750068 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 119937223) (BSN.cosEvenQ 67108864) 0 3 hp750064 hp745658 hp750065 rfl rfl rfl

noncomputable def hp750069 := hp750067 hp750065 7204888 rfl rfl rfl rfl rfl rfl rfl rfl (hp750068 rfl)

noncomputable def hp750070 := @BSN.binarySplit_of_base3 (BSN.cosOddP 119937223) (BSN.cosOddQ 67108864) 0 3 hp750066 hp745661 hp750065 rfl rfl rfl

noncomputable def hp750071 := hp750063 (BSN.cos_neg_of_bound 119937223 67108864 Bool.true 7204888 33554432 1 10890000 (hp750069 (hp750070 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp750072 := hp750021 (hp750024 (@Enclosure.Real.IsNear.neg hp750023 Bool.false 135454265 67108864 955 67108864 (hp750047 rfl))) (@hp750048 7204888 33554432 2091764432 365407764480000 900611 4194304 130735277 22837985280000 (hp750071 rfl) rfl)

noncomputable def hp750073 := @hp749996 33554432 121991601055915 281474976710656 124399613291783 8514618045497344000 37998553854901683775 295147905179352825856 1243646003809667608693 hp748549 (hp750014 rfl) (@hp750017 Bool.false 121991601055915 281474976710656 124399613291783 8514618045497344000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749820 (Enclosure.sfrac Bool.false 11 1)) (hp750018 rfl (hp749823 rfl rfl))) (hp750072 rfl))

noncomputable def hp750074 := @hp749817 209648501612658346520693 hp748549 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 806921 1000))) (@hp749822 209648501612658346520693 hp748549 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 806921 1000) 11 (hp749823 rfl rfl)) (@hp749826 209648501612658346520693 hp748549 hp749995 (hp750073 rfl) rfl rfl))

theorem hd5010 : hp749816 hp748549 := hp750074

noncomputable def hp750075 := nat_lit 18889076023788962225681963

noncomputable def hp750076 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 808215 1000)) Bool.false 199211420697390054079 590295810358705651712 hp750075

noncomputable def hp750077 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 808215 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 808215 1000)) Bool.false 199211420697390054079 590295810358705651712

noncomputable def hp750078 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 808215 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750079 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp750078 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750080 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 808215 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750081 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp750079 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp750082 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 808215 1000)) hp750081 Bool.false 199211420697390054079 590295810358705651712

noncomputable def hp750083 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 808215 1000) 808215 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl

noncomputable def hp750084 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp750079 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp750085 := nat_lit 53475408555311737176561025024

noncomputable def hp750086 := @hp750084 56483987 268435456 49031 67108864 75001819718093208255 590295810358705651712 102465341293849910801963 hp740088 hp750085 199211420697390054079 590295810358705651712

noncomputable def hp750087 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) 11)

noncomputable def hp750088 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) 11) hp750087

noncomputable def hp750089 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) 11)

noncomputable def hp750090 := @hp750089 56483987 536870912 196124 536870912 56483987 536870912 196124 536870912 60649219228172288 56483987 268435456

noncomputable def hp750091 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp750092 := hp750091 BSN.quadSignNeg 9 10 11 808215 1000 192 241 536870912 268435456 9007199254740992

noncomputable def hp750093 := hp750092 Bool.false 836568453677 3683 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp750094 := hp750093 Bool.false 140973635 168367 Bool.true 623167372 Bool.true 656506105 28296951008113761 1 Bool.false 214029643

noncomputable def hp750095 := hp750094 Bool.false Bool.false 504696672 Bool.true Bool.false 56483987 196124 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 214029643 536870912) BSN.abs_quadSignNeg

noncomputable def hp750096 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp750097 := hp750096 BSN.quadSignNeg 7 8 9 808215 1000 77 138 536870912 268435456 9007199254740992

noncomputable def hp750098 := hp750097 Bool.false 836568453677 3683 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp750099 := hp750098 Bool.false 450304348 137505 Bool.true 780800788 Bool.true 445481684 28296951008113761 1 Bool.false 533235405

noncomputable def hp750100 := hp750099 Bool.true Bool.false 362410572 Bool.true Bool.false 140973635 168367 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533235405 536870912) BSN.abs_quadSignNeg

noncomputable def hp750101 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp750102 := hp750101 BSN.quadSignNeg 5 6 7 808215 1000 70 9 536870912 268435456 9007199254740992

noncomputable def hp750103 := hp750102 Bool.false 836568453677 3683 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp750104 := hp750103 Bool.false 735994294 102183 Bool.false 79221196 Bool.true 185976788 28296951008113761 1 Bool.false 531036531

noncomputable def hp750105 := hp750104 Bool.true Bool.false 182279535 Bool.true Bool.false 450304348 137505 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 531036531 536870912) BSN.abs_quadSignNeg

noncomputable def hp750106 := hp750101 BSN.quadSignPos 3 4 5 808215 1000 278 163 536870912 268435456 9007199254740992

noncomputable def hp750107 := hp750106 Bool.false 836568453677 3683 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp750108 := hp750107 Bool.false 614439257 60396 Bool.false 603935391 Bool.false 761568807 28296951008113761 1 Bool.false 231526176

noncomputable def hp750109 := hp750108 Bool.true Bool.false 530659441 Bool.false Bool.false 735994294 102183 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 278 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 231526176 536870912) BSN.abs_quadSignPos

noncomputable def hp750110 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp750111 := hp750110 BSN.quadSignNeg 1 2 3 808215 1000 635 426 536870912 268435456 9007199254740992

noncomputable def hp750112 := hp750111 Bool.false 836568453677 3683 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp750113 := hp750112 Bool.false 536870896 3738 Bool.false 302032159 Bool.false 620630396 28296951008113761 1 Bool.false 286350449

noncomputable def hp750114 := hp750113 Bool.false Bool.false 216353901 Bool.true Bool.false 614439257 60396 BSN.abs_quadSignPos (BSN.cos_quad_nat3 635 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 286350449 536870912) BSN.abs_quadSignNeg

noncomputable def hp750115 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) 1) Bool.false

noncomputable def hp750116 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)))

noncomputable def hp750117 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000))) Bool.false 67108862 67108864

noncomputable def hp750118 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 104571056709) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 104571056709 67108864

noncomputable def hp750119 := nat_lit 100143619053681834790671157819750642437390676687484037

noncomputable def hp750120 := nat_lit 64267539441647269387060083826162821326378840883200

noncomputable def hp750121 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) Bool.false hp750119 hp750120 24474010919480766989

noncomputable def hp750122 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 808215 4000) (Real.log (Enclosure.sfrac Bool.false 2612846944900 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1616430))))))

noncomputable def hp750123 := nat_lit 165529800116039384484990664500000000

noncomputable def hp750124 := nat_lit 802702147771374475265144735663205000000

noncomputable def hp750125 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp750122 (Enclosure.sfrac Bool.false 808215 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 808215 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp750123 hp750124)) Bool.false

noncomputable def hp750126 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 808215 1000) 808215 1000 2612846944900 16000000 1616430

noncomputable def hp750127 := hp750126 4000 2000 hp750123 hp750124 (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl rfl rfl rfl

noncomputable def hp750128 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp750122 (Enclosure.sfrac Bool.false 808215 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 808215 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp750123 hp750124) 5614116601421091272013 3602879701896396800

noncomputable def hp750129 := nat_lit 4506462857415682565580202101888778909682580450936781665000000

noncomputable def hp750130 := @hp750128 24474010919480766989 hp744142 hp750123 hp750124 0 1 hp750129 hp750119 hp750120 24474010919480766989 hp744142

noncomputable def hp750131 := @Enclosure.Real.IsNear.subLit_ff_p (hp750122 (Enclosure.sfrac Bool.false 808215 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 808215 2000) (Real.log Real.pi)) 7280786885582967764301 3602879701896396800 2040540492605759 871200000000000000000

noncomputable def hp750132 := nat_lit 75351397496982044181021484646400

noncomputable def hp750133 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 808215 4000) (Real.log (Enclosure.sfrac Bool.false 2612846944900 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1616430))))))

noncomputable def hp750134 := @hp750133 (Enclosure.sfrac Bool.false 808215 2000) 8736737594717065934157 3602879701896396800 2040540492605759 871200000000000000000 808215 2000 0

noncomputable def hp750135 := nat_lit 14561573771165935528602000

noncomputable def hp750136 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 808215 4000) (Real.log (Enclosure.sfrac Bool.false 2612846944900 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1616430))))) 8738151885049152057357

noncomputable def hp750137 := nat_lit 19673384088000790821748082909890215936

noncomputable def hp750138 := @hp750136 3602879701896396800 673513497498953 290400000000000000000 883931457553827 2251799813685248 200000001089 8712000000000000000 hp750137 8736737594717065934157 3602879701896396800 2040540492605759

noncomputable def hp750139 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 808215 4000) (Real.log (Enclosure.sfrac Bool.false 2612846944900 16000000)) 808215 4000 0 1 54058337726032999 4503599627370496

noncomputable def hp750140 := nat_lit 116089396304717369260900352

noncomputable def hp750141 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2612846944900) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp750140 hp617687

noncomputable def hp750142 := BSN.log_rat_reduce_isNear 2612846944900 16000000 17 5225693889800 4194304000000 59018266 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp750143 := nat_lit 228874963073148746220926274423331995079515945193346921890424077142081090009686736464089450000000000000000

noncomputable def hp750144 := nat_lit 921214063313792019706060247834518752015306217991028603313484554087317902037348779143440000000000000000

noncomputable def hp750145 := nat_lit 525209161505308982576501689592670715732094306658171286467432517796238094743121050000000000000000

noncomputable def hp750146 := BSN.log_dyadic_bound 515694944900 4709998944900 5 4 hp750143 268435456 87120000 hp750144 hp750145 59018266 5225693889800

noncomputable def hp750147 := hp750146 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp750148 := @BSN.binarySplit_of_base4 (BSN.artanhP 515694944900) (BSN.artanhQ 4709998944900) 0 4 hp750144 hp750143 hp750145 rfl rfl rfl

noncomputable def hp750149 := hp750142 rfl rfl rfl rfl (hp750147 (hp750148 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp750150 := @hp750139 12500018513 1089000000000000000 8738151885049152057357 3602879701896396800 673513497498953 290400000000000000000 (Enclosure.Real.IsNear.const Bool.false 808215 4000) (BSN.isNear_log_sfrac 2612846944900 16000000 54058337726032999 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp750141 1000001481040000 87120000000000000000000 54058337726032999 4503599627370496 12500018513 1089000000000000000 (hp750149 rfl rfl rfl) rfl)) rfl

noncomputable def hp750151 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1616430)))) 1 4

noncomputable def hp750152 := @hp750151 0 1 883931457553827 562949953421312 200000001089 2178000000000000000 883931457553827 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp750153 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1616430))) 884279719003555 562949953421312 1

noncomputable def hp750154 := @hp750153 2000000000000000 20758 33554432 1 10890000 29659817985150774411264 883931457553827 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp750155 := BSN.arctan_dyadic_bound_f 1000 1616430 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp750156 := hp750155 1 20758 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1616430) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1616430) 0 0 rfl)

noncomputable def hp750157 := hp750152 (hp750154 (hp750156 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp750158 := @hp750131 6208830640323 13421772800 484929 107374182400 hp750132 5614116601421091272013 3602879701896396800 24474010919480766989 hp744142 (@hp750134 1 hp750135 7280786885582967764301 3602879701896396800 2040540492605759 871200000000000000000 (@hp750138 871200000000000000000 hp750150 hp750157 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 808215 2000) rfl rfl)

noncomputable def hp750159 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 808215 2000) (Real.log Real.pi) 808215 2000 0 1 38410761 33554432

noncomputable def hp750160 := hp750158 (@hp750159 3 268435456 6208830640323 13421772800 484929 107374182400 (Enclosure.Real.IsNear.const Bool.false 808215 2000) hd4909 rfl) rfl

noncomputable def hp750161 := @hp750121 hp744142 104571056709 67108864 461 67108864 (@hp750125 hp750119 hp750120 24474010919480766989 hp744142 (hp750127 rfl rfl rfl rfl rfl) (hp750130 (hp750160 rfl) (Enclosure.Real.IsNear.const Bool.true hp750123 hp750124) rfl rfl)) rfl

noncomputable def hp750162 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 104571056709) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2089519534083521118208) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp750163 := BSN.sin_reduce_arg_pos_rat_q0 104571056709 67108864 226375608064910080 72057594037927936 248 2089519534083521118208 hp617687 rfl rfl rfl rfl

noncomputable def hp750164 := BSN.cos_dyadic_bound_f 29693858 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp750165 := hp750164 1 67108862 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 29693858) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp750166 := hp750165 (@BSN.binarySplit_of_le (BSN.cosOddP 29693858) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp750167 := @BSN.cos_arg_round Bool.false 67108862 67108864 2089519534083521118208 hp617687 29693858 137438953472 21801270 21780000 hp750166 rfl

noncomputable def hp750168 := hp750162 67108862 67108864 248 1000000000000000 21780000 10890000 hp750163 BSN.pi_near_15 hp750167 rfl rfl

noncomputable def hp750169 := @hp750118 461 67108864 Bool.false 67108862 67108864 1 10890000 hp750161 (Enclosure.sfrac_false_div 104571056709 67108864) (hp750168 rfl rfl) rfl

noncomputable def hp750170 := @hp750115 33554431 33554432 317962429 45675970560000 536870896 536870912 3738 536870912 (@hp750116 Bool.false 33554431 33554432 317962429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000)) (@hp750117 5087398864 730815528960000 33554431 33554432 317962429 45675970560000 (hp750169 rfl) rfl))

noncomputable def hp750171 := @hp750121 hp744142 836568453677 536870912 3683 536870912 (@hp750125 hp750119 hp750120 24474010919480766989 hp744142 (hp750127 rfl rfl rfl rfl rfl) (hp750130 (hp750160 rfl) (Enclosure.Real.IsNear.const Bool.true hp750123 hp750124) rfl rfl)) rfl

noncomputable def hp750172 := hp750114 (BSN.cos_quad_nat2 426 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 216353901 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl rfl (hp750170 rfl) hp750171

noncomputable def hp750173 := nat_lit 2090684107321321839996591573404577522052974883451528182999819894621357825

noncomputable def hp750174 := nat_lit 69250911940136393688788596619368320041205108386097744284581065803521

noncomputable def hp750175 := nat_lit 5475489112936511264877481796426985961430105600768996321032591354663683841

noncomputable def hp750176 := BSN.sin_dyadic_bound_f 302032159 536870912 3 2 536870912 268435456 hp750173 hp708845 hp750174 hp750175 hp708848

noncomputable def hp750177 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 302032159) (BSN.sinEvenQ 536870912) 0 2 hp750173 hp708845 hp750174 rfl rfl rfl

noncomputable def hp750178 := hp750176 hp750174 286350449 rfl rfl rfl rfl rfl rfl rfl rfl (hp750177 rfl)

noncomputable def hp750179 := @BSN.binarySplit_of_base2 (BSN.sinOddP 302032159) (BSN.sinOddQ 536870912) 0 2 hp750175 hp708848 hp750174 rfl rfl rfl

noncomputable def hp750180 := nat_lit 20458715989265092245474277288161770717514667074258966412948209428186847999045208833328944572966568968779932368896

noncomputable def hp750181 := nat_lit 3265852012148654659639815174975669227288109746401409201650430172374930783553324942651226347394093092438016

noncomputable def hp750182 := nat_lit 124028328133850851098288485618520572172545566871722370302014576497345254459971841161551225012125370943089284218880

noncomputable def hp750183 := BSN.cos_dyadic_bound_f 620630396 536870912 4 3 536870912 268435456 hp750180 hp716712 hp750181 hp750182 hp716714

noncomputable def hp750184 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 620630396) (BSN.cosEvenQ 536870912) 0 3 hp750180 hp716712 hp750181 rfl rfl rfl

noncomputable def hp750185 := hp750183 hp750181 216353901 rfl rfl rfl rfl rfl rfl rfl rfl (hp750184 rfl)

noncomputable def hp750186 := @BSN.binarySplit_of_base3 (BSN.cosOddP 620630396) (BSN.cosOddQ 536870912) 0 3 hp750182 hp716714 hp750181 rfl rfl rfl

noncomputable def hp750187 := hp750172 hd4911 hd4913 hd4915 hd4917 hd4918 (hp750178 (hp750179 rfl) rfl rfl rfl rfl) (hp750185 (hp750186 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750188 := hp750109 (BSN.cos_quad_nat3 163 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 530659441 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl rfl (hp750187 rfl rfl rfl rfl rfl) hp750171

noncomputable def hp750189 := nat_lit 18342581409421143960943695837767911559477646636460069590716498019129770998690183363624722852111548202123332216961

noncomputable def hp750190 := nat_lit 2354429894717803379534910856885269361598968694533881789781528088303112165783544903424831533264785778993281

noncomputable def hp750191 := nat_lit 111207670739486324266345740023503776417550624880700692911670764524626629275098412942784310215702131848650255558785

noncomputable def hp750192 := BSN.cos_dyadic_bound_f 603935391 536870912 4 3 536870912 268435456 hp750189 hp716712 hp750190 hp750191 hp716714

noncomputable def hp750193 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 603935391) (BSN.cosEvenQ 536870912) 0 3 hp750189 hp716712 hp750190 rfl rfl rfl

noncomputable def hp750194 := hp750192 hp750190 231526176 rfl rfl rfl rfl rfl rfl rfl rfl (hp750193 rfl)

noncomputable def hp750195 := @BSN.binarySplit_of_base3 (BSN.cosOddP 603935391) (BSN.cosOddQ 536870912) 0 3 hp750191 hp716714 hp750190 rfl rfl rfl

noncomputable def hp750196 := nat_lit 120635718672684150961545813150546098772439297050283950497694267929764695691860299855649501376724523926689177930401

noncomputable def hp750197 := nat_lit 38063592068470595197549234743685264410158470670803802508105387552181085926972866454379104409789318167268001

noncomputable def hp750198 := nat_lit 602679836610351226244689692247941661846031758991076717916960840585678646994840783291822929049102586153253925030561

noncomputable def hp750199 := BSN.sin_dyadic_bound_f 761568807 536870912 4 3 536870912 268435456 hp750196 hp642702 hp750197 hp750198 hp642705

noncomputable def hp750200 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 761568807) (BSN.sinEvenQ 536870912) 0 3 hp750196 hp642702 hp750197 rfl rfl rfl

noncomputable def hp750201 := hp750199 hp750197 530659441 rfl rfl rfl rfl rfl rfl rfl rfl (hp750200 rfl)

noncomputable def hp750202 := @BSN.binarySplit_of_base3 (BSN.sinOddP 761568807) (BSN.sinOddQ 536870912) 0 3 hp750198 hp642705 hp750197 rfl rfl rfl

noncomputable def hp750203 := hp750188 hd4920 hd4922 hd4924 hd4926 hd4918 (hp750194 (hp750195 rfl) rfl rfl rfl rfl) (hp750201 (hp750202 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750204 := hp750105 (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 182279535 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl rfl (hp750203 rfl rfl rfl rfl rfl) hp750171

noncomputable def hp750205 := nat_lit 39388149586459489834998097613056

noncomputable def hp750206 := BSN.cos_dyadic_bound_f 79221196 536870912 2 1 536870912 268435456 hp750205 hp708767 hp750205 hp750205 hp708768

noncomputable def hp750207 := @BSN.binarySplit_of_base (BSN.cosEvenP 79221196) (BSN.cosEvenQ 536870912) 0 1 hp750205 hp708767 hp750205 rfl rfl rfl

noncomputable def hp750208 := hp750206 hp750205 531036531 rfl rfl rfl rfl rfl rfl rfl rfl (hp750207 rfl)

noncomputable def hp750209 := @BSN.binarySplit_of_base (BSN.cosOddP 79221196) (BSN.cosOddQ 536870912) 0 1 hp750205 hp708768 hp750205 rfl rfl rfl

noncomputable def hp750210 := nat_lit 1196285864322121861376035631739136

noncomputable def hp750211 := BSN.sin_dyadic_bound_f 185976788 536870912 2 1 536870912 268435456 hp750210 hp708890 hp750210 hp750210 hp708891

noncomputable def hp750212 := @BSN.binarySplit_of_base (BSN.sinEvenP 185976788) (BSN.sinEvenQ 536870912) 0 1 hp750210 hp708890 hp750210 rfl rfl rfl

noncomputable def hp750213 := hp750211 hp750210 182279535 rfl rfl rfl rfl rfl rfl rfl rfl (hp750212 rfl)

noncomputable def hp750214 := @BSN.binarySplit_of_base (BSN.sinOddP 185976788) (BSN.sinOddQ 536870912) 0 1 hp750210 hp708891 hp750210 rfl rfl rfl

noncomputable def hp750215 := hp750204 hd4928 hd4930 hd4932 hd4934 hd4918 (hp750208 (hp750209 rfl) rfl rfl rfl rfl) (hp750213 (hp750214 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750216 := hp750100 (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 362410572 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl rfl (hp750215 rfl rfl rfl rfl rfl) hp750171

noncomputable def hp750217 := nat_lit 133309544573756695559505728448035058664545376925746844773430783744462158212576417556214295553208477748170070163456

noncomputable def hp750218 := nat_lit 51343197944451182719380871342803949659106976446702337128687315152262273596057575881980294150541560518803456

noncomputable def hp750219 := nat_lit 665938815177310042084861312824275788629503812115496484445541506768258993371731107107537140873661620761168724361216

noncomputable def hp750220 := BSN.sin_dyadic_bound_f 780800788 536870912 4 3 536870912 268435456 hp750217 hp642702 hp750218 hp750219 hp642705

noncomputable def hp750221 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 780800788) (BSN.sinEvenQ 536870912) 0 3 hp750217 hp642702 hp750218 rfl rfl rfl

noncomputable def hp750222 := hp750220 hp750218 533235405 rfl rfl rfl rfl rfl rfl rfl rfl (hp750221 rfl)

noncomputable def hp750223 := @BSN.binarySplit_of_base3 (BSN.sinOddP 780800788) (BSN.sinOddQ 536870912) 0 3 hp750219 hp642705 hp750218 rfl rfl rfl

noncomputable def hp750224 := nat_lit 5498328998001781661109173479243258614362825042700325955221024847104638976

noncomputable def hp750225 := nat_lit 1551096513372666802710452947028676039303176400080875681090740588445696

noncomputable def hp750226 := nat_lit 16491884800978599649722099531835718491009868775300816114300893060137025536

noncomputable def hp750227 := BSN.cos_dyadic_bound_f 445481684 536870912 3 2 536870912 268435456 hp750224 hp708868 hp750225 hp750226 hp708870

noncomputable def hp750228 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 445481684) (BSN.cosEvenQ 536870912) 0 2 hp750224 hp708868 hp750225 rfl rfl rfl

noncomputable def hp750229 := hp750227 hp750225 362410572 rfl rfl rfl rfl rfl rfl rfl rfl (hp750228 rfl)

noncomputable def hp750230 := @BSN.binarySplit_of_base2 (BSN.cosOddP 445481684) (BSN.cosOddQ 536870912) 0 2 hp750226 hp708870 hp750225 rfl rfl rfl

noncomputable def hp750231 := hp750216 hd4936 hd4938 hd4940 hd4942 hd4918 (hp750222 (hp750223 rfl) rfl rfl rfl rfl) (hp750229 (hp750230 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750232 := hp750095 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 504696672 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl rfl (hp750231 rfl rfl rfl rfl rfl) hp750171

noncomputable def hp750233 := nat_lit 20795655815321526467343506368536931071108345974911768800072065170235908269545437815084823788005191746922737565696

noncomputable def hp750234 := nat_lit 3429702704741075213408730012859626972997693488086403462920780823815041353416614323619496299689233996578816

noncomputable def hp750235 := nat_lit 126069514091681181855327211143918493589095668747845530626981311032571007472229057023502858707072430479986109972480

noncomputable def hp750236 := BSN.cos_dyadic_bound_f 623167372 536870912 4 3 536870912 268435456 hp750233 hp716712 hp750234 hp750235 hp716714

noncomputable def hp750237 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 623167372) (BSN.cosEvenQ 536870912) 0 3 hp750233 hp716712 hp750234 rfl rfl rfl

noncomputable def hp750238 := hp750236 hp750234 214029643 rfl rfl rfl rfl rfl rfl rfl rfl (hp750237 rfl)

noncomputable def hp750239 := @BSN.binarySplit_of_base3 (BSN.cosOddP 623167372) (BSN.cosOddQ 536870912) 0 3 hp750235 hp716714 hp750234 rfl rfl rfl

noncomputable def hp750240 := nat_lit 66578528407904240324252404945041598595917180808499064327495708613087321453262149224454332105019524731784727790625

noncomputable def hp750241 := nat_lit 6410106255821493958949747851108802021620522358140895689112542270335739883686425934148035603029551025390625

noncomputable def hp750242 := nat_lit 332740564039237452512068563530056039444859127457129411733903315736689369836272037768757039228308418799855537390625

noncomputable def hp750243 := BSN.sin_dyadic_bound_f 656506105 536870912 4 3 536870912 268435456 hp750240 hp642702 hp750241 hp750242 hp642705

noncomputable def hp750244 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 656506105) (BSN.sinEvenQ 536870912) 0 3 hp750240 hp642702 hp750241 rfl rfl rfl

noncomputable def hp750245 := hp750243 hp750241 504696672 rfl rfl rfl rfl rfl rfl rfl rfl (hp750244 rfl)

noncomputable def hp750246 := @BSN.binarySplit_of_base3 (BSN.sinOddP 656506105) (BSN.sinOddQ 536870912) 0 3 hp750242 hp642705 hp750241 rfl rfl rfl

noncomputable def hp750247 := hp750232 hd4944 hd4946 hd4961 hd4963 hd4918 (hp750238 (hp750239 rfl) rfl rfl rfl rfl) (hp750245 (hp750246 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750248 := @hp750090 49031 67108864 (hp750247 rfl rfl rfl rfl rfl) (hp750247 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp750249 := @hp750088 Bool.false 56483987 268435456 49031 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 808215 1000)) (Enclosure.sfrac Bool.false 808215 1000) 11) hp750248

noncomputable def hp750250 := @Enclosure.Real.IsNear.mulLit_tf hp750079 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1))) 1245441 4194304 1

noncomputable def hp750251 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp750078 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750252 := @hp750251 1 1 0 1 1245441 4194304 1 33554432 1245441 4194304 1

noncomputable def hp750253 := @Enclosure.Real.IsNear.of_eq (hp750078 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750254 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 808215 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750255 := @hp750253 (@Inv.inv Real Real.instInv (Real.sqrt hp750080)) Bool.false 1245441 4194304 1 33554432 (hp750254 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 808215 1000) 808215 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000))))

noncomputable def hp750256 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp750080)) Bool.false 19927056 67108864 2 67108864 1245441 4194304

noncomputable def hp750257 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp750080) Bool.false 226004269 67108864 7 67108864 226004269 67108864 7 67108864

noncomputable def hp750258 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 808215 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750259 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 808215 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750260 := @hp750259 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 808215 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 1726461521601

noncomputable def hp750261 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 808215 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 808215 1000 0

noncomputable def hp750262 := @hp750261 1 10680707 67108864 1 67108864 1726461521601 13421772800 161643 13421772800 (Enclosure.Real.IsNear.const Bool.false 808215 1000) hd4949

noncomputable def hp750263 := @hp750260 13421772800 161643 13421772800 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 808215 1000) 808215 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000))) (hp750262 rfl)

noncomputable def hp750264 := @hp750258 1726461521601 13421772800 161643 13421772800 380560213 380560249 33554432 hp750263 rfl rfl rfl

noncomputable def hp750265 := @Enclosure.Real.IsNear.recentre' hp750080 Bool.false 761120462 67108864 36 67108864 380560231 33554432 9 16777216 (hp750264 rfl rfl rfl)

noncomputable def hp750266 := @Enclosure.Real.IsNear.sqrt_image hp750080 380560231 33554432 9 16777216 113002131 113002138 33554432 (hp750265 rfl) rfl rfl

noncomputable def hp750267 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp750080) 226004269 67108864 7 67108864 9963527 9963529 33554432 (hp750257 (hp750266 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp750268 := @hp750252 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp750255 (@hp750256 1 33554432 (hp750267 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp750269 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750270 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp750271 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1))) (hp750269 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750270 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp750272 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 808215 1000) 808215 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl

noncomputable def hp750273 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750274 := @hp750273 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750270 (Enclosure.sfrac Bool.false 1 16)))) 61661065

noncomputable def hp750275 := @hp750274 33554432 99 8388608 976647 4194304 132096527 22837985280000 60221094149055 140737488355328 10251130642185947 766315624094760960000

noncomputable def hp750276 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750277 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750278 := @hp750276 (@Neg.neg Real Real.instNeg hp750277) Bool.true 61661065 33554432 99 8388608 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750279 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750280 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp750281 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp750282 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 18003649) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false

noncomputable def hp750283 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1))) Bool.false 10135153429485146557845

noncomputable def hp750284 := nat_lit 242874678730623086565311487

noncomputable def hp750285 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp750286 := @Enclosure.Real.IsNear.subLit_ff_p hp750080 (Enclosure.sfrac Bool.false 11 1) 380560231 33554432 9 16777216 11 1 0

noncomputable def hp750287 := @hp750285 500000000000000 11461479 33554432 9 16777216 10135153429485146557845 4722366482869645213696 hp750284 hp631123 hd4948 (@hp750286 1 11461479 11461479 33554432 9 16777216 (hp750265 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750288 := @hp750282 18003649 8388608 57 16777216 Bool.true 36518990 67108864 1 10890000 (@hp750283 4722366482869645213696 hp750284 hp631123 18003649 8388608 57 16777216 (hp750287 rfl) rfl) (Enclosure.sfrac_false_div 18003649 8388608)

noncomputable def hp750289 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 18003649) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 695623024868525277708288) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp750290 := BSN.sin_reduce_arg_pos_rat_q1 18003649 8388608 226375608064910080 72057594037927936 0 695623024868525277708288 hp630689 rfl rfl rfl rfl

noncomputable def hp750291 := nat_lit 42205925525314959895324802331454037673674559876344181333024314136467373310595892445363239745

noncomputable def hp750292 := nat_lit 1529935352338259799097973885531246643792435824407240949672391203580408531443155444104001

noncomputable def hp750293 := nat_lit 110536851718587775876652133196088762365057707160995244148764210295465895152033572248089459521

noncomputable def hp750294 := BSN.sin_dyadic_bound_f 79083181943 137438953472 3 2 67108864 21801270 hp750291 hp738039 hp750292 hp750293 hp738042

noncomputable def hp750295 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 79083181943) (BSN.sinEvenQ 137438953472) 0 2 hp750291 hp738039 hp750292 rfl rfl rfl

noncomputable def hp750296 := hp750294 hp750292 36518990 rfl rfl rfl rfl rfl rfl rfl rfl (hp750295 rfl)

noncomputable def hp750297 := @BSN.binarySplit_of_base2 (BSN.sinOddP 79083181943) (BSN.sinOddQ 137438953472) 0 2 hp750293 hp738042 hp750292 rfl rfl rfl

noncomputable def hp750298 := @BSN.sin_arg_round Bool.false 36518990 67108864 695623024868525277708288 hp630689 79083181943 137438953472 21801270 21780000 (hp750296 (hp750297 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750299 := hp750289 36518990 67108864 0 1000000000000000 21780000 10890000 hp750290 BSN.pi_near_15 hp750298 rfl rfl

noncomputable def hp750300 := @hp750280 18259495 33554432 39844201 11418992640000 (@hp750281 36518990 67108864 637507216 182703882240000 18259495 33554432 39844201 11418992640000 (hp750288 (hp750299 rfl rfl) rfl rfl) rfl)

noncomputable def hp750301 := @hp750279 18259495 33554432 39844201 11418992640000 61660669 61661461 33554432 hp750300 rfl rfl rfl

noncomputable def hp750302 := @Enclosure.Real.IsNear.recentre' hp750277 Bool.false 123322130 67108864 792 67108864 61661065 33554432 99 8388608 (hp750301 rfl rfl rfl)

noncomputable def hp750303 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750270 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp750304 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750270 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 60592739)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp750305 := nat_lit 286141121693461925982548961805

noncomputable def hp750306 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750270 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp750305

noncomputable def hp750307 := nat_lit 85730827013424507080293263594997

noncomputable def hp750308 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750270 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp750309 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp750310 := @hp750309 (Enclosure.sfrac Bool.false 1 16) 253217916857487 1125899906842624 15884271 17592186044416 1 16 0

noncomputable def hp750311 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)) 131365500867441

noncomputable def hp750312 := @hp750311 1125899906842624 6447087 17592186044416 11461479 33554432 9 16777216 8496583372376201232384 253217916857487 1125899906842624 15884271

noncomputable def hp750313 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)) 11461479 33554432 9

noncomputable def hp750314 := @hp750313 16777216 11461479 33554432 9 16777216 131365500867441 1125899906842624 6447087 17592186044416 (@hp750286 1 11461479 11461479 33554432 9 16777216 (hp750265 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750315 := hp750314 (@hp750286 1 11461479 11461479 33554432 9 16777216 (hp750265 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750316 := @hp750312 17592186044416 (hp750315 rfl) (@hp750286 1 11461479 11461479 33554432 9 16777216 (hp750265 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750317 := @hp750308 500000000000000 323586661035151 1125899906842624 15884271 17592186044416 hp750305 hp682141 hp750307 hp638793 hd4948 (@hp750310 1 5177386576562416 323586661035151 1125899906842624 15884271 17592186044416 (hp750316 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp750318 := @hp750304 60592739 33554432 191 33554432 Bool.true 7813176 33554432 1 10890000 (@hp750306 hp682141 hp750307 hp638793 60592739 33554432 191 33554432 (hp750317 rfl) rfl) (Enclosure.sfrac_true_div 60592739 33554432)

noncomputable def hp750319 := nat_lit 435060713787592659238550344413766101831719449843981893072171465474094090933356767562628919097644401

noncomputable def hp750320 := nat_lit 2449328379355014698655267325398683406411376232525754985793354488671050911535654080692852708721

noncomputable def hp750321 := nat_lit 2628288674529920572628892477616954384363874212516547195496092986200734111618348748681659773541242225

noncomputable def hp750322 := BSN.cos_dyadic_bound_t 60592739 33554432 4 3 33554432 10890000 hp750319 hp681868 hp750320 hp750321 hp681871

noncomputable def hp750323 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 60592739) (BSN.cosEvenQ 33554432) 0 3 hp750319 hp681868 hp750320 rfl rfl rfl

noncomputable def hp750324 := hp750322 hp750320 7813176 rfl rfl rfl rfl rfl rfl rfl rfl (hp750323 rfl)

noncomputable def hp750325 := @BSN.binarySplit_of_base3 (BSN.cosOddP 60592739) (BSN.cosOddQ 33554432) 0 3 hp750321 hp681871 hp750320 rfl rfl rfl

noncomputable def hp750326 := hp750318 (BSN.cos_neg_of_bound 60592739 33554432 Bool.true 7813176 33554432 1 10890000 (hp750324 (hp750325 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp750327 := hp750275 (hp750278 (@Enclosure.Real.IsNear.neg hp750277 Bool.false 61661065 33554432 99 8388608 (hp750302 rfl))) (@hp750303 7813176 33554432 2113544432 365407764480000 976647 4194304 132096527 22837985280000 (hp750326 rfl) rfl)

noncomputable def hp750328 := @hp750250 33554432 60221094149055 140737488355328 10251130642185947 766315624094760960000 75001819718093208255 590295810358705651712 102465341293849910801963 hp740088 (hp750268 rfl) (@hp750271 Bool.false 60221094149055 140737488355328 10251130642185947 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750080 (Enclosure.sfrac Bool.false 11 1)) (hp750272 rfl (hp750083 rfl rfl))) (hp750327 rfl))

noncomputable def hp750329 := @hp750077 hp750075 hp740088 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 808215 1000))) (@hp750082 hp750075 hp740088 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 808215 1000) 11 (hp750083 rfl rfl)) (@hp750086 hp750075 hp740088 hp750249 (hp750328 rfl) rfl rfl))

theorem hd5011 : hp750076 hp740088 := hp750329

noncomputable def hp750330 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 809508 1000)) Bool.true 707811633556837451943 1180591620717411303424 788086617649611877048099

noncomputable def hp750331 := nat_lit 1071386895801050757857280000

noncomputable def hp750332 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 809508 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 809508 1000)) Bool.true 707811633556837451943 1180591620717411303424

noncomputable def hp750333 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 809508 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750334 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp750333 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750335 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 809508 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750336 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp750334 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp750337 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 809508 1000)) hp750336 Bool.true 707811633556837451943 1180591620717411303424

noncomputable def hp750338 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 809508 1000) 809508 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl

noncomputable def hp750339 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp750334 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp750340 := nat_lit 95000869307967281665098645504

noncomputable def hp750341 := @hp750339 97310043 134217728 24555 33554432 148136556666222983001 1180591620717411303424 4049944747659569848099 hp750331 hp750340 707811633556837451943 1180591620717411303424

noncomputable def hp750342 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) 11)

noncomputable def hp750343 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) 11) hp750342

noncomputable def hp750344 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) 11)

noncomputable def hp750345 := @hp750344 194620086 536870912 196440 536870912 194620086 536870912 196440 536870912 208971726128676864 97310043 134217728

noncomputable def hp750346 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp750347 := hp750346 BSN.quadSignNeg 9 10 11 809508 1000 192 241 536870912 268435456 9007199254740992

noncomputable def hp750348 := hp750347 Bool.false 838254515863 3689 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp750349 := hp750348 Bool.true 136874232 168639 Bool.true 535500092 Bool.true 635000684 28296951008113761 1 Bool.false 291225150

noncomputable def hp750350 := hp750349 Bool.false Bool.false 496960876 Bool.true Bool.true 194620086 196440 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 291225150 536870912) BSN.abs_quadSignNeg

noncomputable def hp750351 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp750352 := hp750351 BSN.quadSignNeg 7 8 9 809508 1000 77 138 536870912 268435456 9007199254740992

noncomputable def hp750353 := hp750352 Bool.false 838254515863 3689 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp750354 := hp750353 Bool.false 177489904 137727 Bool.true 538233039 Bool.true 284675849 28296951008113761 1 Bool.false 452495800

noncomputable def hp750355 := hp750354 Bool.true Bool.false 463148128 Bool.true Bool.true 136874232 168639 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 452495800 536870912) BSN.abs_quadSignNeg

noncomputable def hp750356 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp750357 := hp750356 BSN.quadSignPos 5 6 7 809508 1000 70 8 536870912 268435456 9007199254740992

noncomputable def hp750358 := hp750357 Bool.false 838254515863 3689 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp750359 := hp750358 Bool.false 245445770 102348 Bool.false 521490393 Bool.true 694029844 28296951008113761 1 Bool.false 302894053

noncomputable def hp750360 := hp750359 Bool.true Bool.false 147368646 Bool.false Bool.false 177489904 137727 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 302894053 536870912) BSN.abs_quadSignPos

noncomputable def hp750361 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp750362 := hp750361 BSN.quadSignPos 3 4 5 809508 1000 279 164 536870912 268435456 9007199254740992

noncomputable def hp750363 := hp750362 Bool.false 838254515863 3689 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp750364 := hp750363 Bool.true 113064973 60495 Bool.false 484353113 Bool.false 487086060 28296951008113761 1 Bool.false 421271278

noncomputable def hp750365 := hp750364 Bool.false Bool.false 330658792 Bool.false Bool.false 245445770 102348 BSN.abs_quadSignPos (BSN.cos_quad_nat3 279 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 421271278 536870912) BSN.abs_quadSignPos

noncomputable def hp750366 := hp750346 BSN.quadSignPos 1 2 3 809508 1000 636 427 536870912 268435456 9007199254740992

noncomputable def hp750367 := hp750366 Bool.false 838254515863 3689 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp750368 := hp750367 Bool.true 536870720 3746 Bool.false 663614695 Bool.false 700749547 28296951008113761 1 Bool.false 176363430

noncomputable def hp750369 := hp750368 Bool.false Bool.false 518052876 Bool.false Bool.true 113064973 60495 BSN.abs_quadSignPos (BSN.cos_quad_nat0 636 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 176363430 536870912) BSN.abs_quadSignPos

noncomputable def hp750370 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) 1) Bool.true

noncomputable def hp750371 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)))

noncomputable def hp750372 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000))) Bool.true 67108840 67108864

noncomputable def hp750373 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 52390907241) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 52390907241 33554432

noncomputable def hp750374 := nat_lit 60386969382842571302616411687993491910927950088781947

noncomputable def hp750375 := nat_lit 38675613088792984801526546173149388902622035968000

noncomputable def hp750376 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) Bool.false hp750374 hp750375 30641292398752899871

noncomputable def hp750377 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 809508 4000) (Real.log (Enclosure.sfrac Bool.false 2621213808256 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1619016))))))

noncomputable def hp750378 := nat_lit 166858133940438647323927772528640000

noncomputable def hp750379 := nat_lit 810438110025452597098748468696941854720

noncomputable def hp750380 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp750377 (Enclosure.sfrac Bool.false 809508 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 809508 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp750378 hp750379)) Bool.false

noncomputable def hp750381 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 809508 1000) 809508 1000 2621213808256 16000000 1619016

noncomputable def hp750382 := hp750381 4000 2000 hp750378 hp750379 (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl rfl rfl rfl

noncomputable def hp750383 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp750377 (Enclosure.sfrac Bool.false 809508 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 809508 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp750378 hp750379) 7031789465041038627759 4503599627370496000

noncomputable def hp750384 := nat_lit 5698829412682517884159107585193451739659386757306515697172480

noncomputable def hp750385 := @hp750383 30641292398752899871 hp739140 hp750378 hp750379 0 1 hp750384 hp750374 hp750375 30641292398752899871 hp739140

noncomputable def hp750386 := @Enclosure.Real.IsNear.subLit_ff_p (hp750377 (Enclosure.sfrac Bool.false 809508 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 809508 2000) (Real.log Real.pi)) 9118460289622542799791 4503599627370496000 1277358123370763 544500000000000000000

noncomputable def hp750387 := nat_lit 117973850721517953922256338944000

noncomputable def hp750388 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 809508 4000) (Real.log (Enclosure.sfrac Bool.false 2621213808256 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1619016))))))

noncomputable def hp750389 := @hp750388 (Enclosure.sfrac Bool.false 809508 2000) 437652410127970421511 180143985094819840 1277358123370763 544500000000000000000 809508 2000 0

noncomputable def hp750390 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 809508 4000) (Real.log (Enclosure.sfrac Bool.false 2621213808256 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1619016))))) 437723124688866577911

noncomputable def hp750391 := nat_lit 985505615585063539963372452842569728

noncomputable def hp750392 := @hp750390 180143985094819840 843238748868467 363000000000000000000 883932011201955 2251799813685248 200000001089 8712000000000000000 hp750391 437652410127970421511 180143985094819840 1277358123370763

noncomputable def hp750393 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 809508 4000) (Real.log (Enclosure.sfrac Bool.false 2621213808256 16000000)) 809508 4000 0 1 54072736117353575 4503599627370496

noncomputable def hp750394 := nat_lit 116120316614635811346841600

noncomputable def hp750395 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2621213808256) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp750394 hp617687

noncomputable def hp750396 := BSN.log_rat_reduce_isNear 2621213808256 16000000 17 5242427616512 4194304000000 59876477 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp750397 := nat_lit 232147853951378494824226115486231527985046421722926772332831568311346952271984218625274012681637063557120

noncomputable def hp750398 := nat_lit 961736948306435089210399120530767271215539958302978660509915693051006829876912408564844199958548578304

noncomputable def hp750399 := nat_lit 597378223922042942683032247019895038843972733039937003700492049701447520731120832759813824839680

noncomputable def hp750400 := BSN.log_dyadic_bound 524061808256 4718365808256 5 4 hp750397 268435456 87120000 hp750398 hp750399 59876477 5242427616512

noncomputable def hp750401 := hp750400 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp750402 := @BSN.binarySplit_of_base4 (BSN.artanhP 524061808256) (BSN.artanhQ 4718365808256) 0 4 hp750398 hp750397 hp750399 rfl rfl rfl

noncomputable def hp750403 := hp750396 rfl rfl rfl rfl (hp750401 (hp750402 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp750404 := @hp750393 12500018513 1089000000000000000 437723124688866577911 180143985094819840 843238748868467 363000000000000000000 (Enclosure.Real.IsNear.const Bool.false 809508 4000) (BSN.isNear_log_sfrac 2621213808256 16000000 54072736117353575 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp750395 1000001481040000 87120000000000000000000 54072736117353575 4503599627370496 12500018513 1089000000000000000 (hp750403 rfl rfl rfl) rfl)) rfl

noncomputable def hp750405 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1619016)))) 1 4

noncomputable def hp750406 := @hp750405 0 1 883932011201955 562949953421312 200000001089 2178000000000000000 883932011201955 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp750407 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1619016))) 884279719003555 562949953421312 1

noncomputable def hp750408 := @hp750407 2000000000000000 20725 33554432 1 10890000 29659836562499237314560 883932011201955 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp750409 := BSN.arctan_dyadic_bound_f 1000 1619016 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp750410 := hp750409 1 20725 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1619016) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1619016) 0 0 rfl)

noncomputable def hp750411 := hp750406 (hp750408 (hp750410 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp750412 := @hp750386 7773454578897 16777216000 607131 134217728000 hp750387 7031789465041038627759 4503599627370496000 30641292398752899871 hp739140 (@hp750389 1 729476823169803423983280 9118460289622542799791 4503599627370496000 1277358123370763 544500000000000000000 (@hp750392 544500000000000000000 hp750404 hp750411 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 809508 2000) rfl rfl)

noncomputable def hp750413 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 809508 2000) (Real.log Real.pi) 809508 2000 0 1 38410761 33554432

noncomputable def hp750414 := hp750412 (@hp750413 3 268435456 7773454578897 16777216000 607131 134217728000 (Enclosure.Real.IsNear.const Bool.false 809508 2000) hd4909 rfl) rfl

noncomputable def hp750415 := @hp750376 hp739140 52390907241 33554432 231 33554432 (@hp750380 hp750374 hp750375 30641292398752899871 hp739140 (hp750382 rfl rfl rfl rfl rfl) (hp750385 (hp750414 rfl) (Enclosure.Real.IsNear.const Bool.true hp750378 hp750379) rfl rfl)) rfl

noncomputable def hp750416 := nat_lit 7591837859666134220931072

noncomputable def hp750417 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 52390907241) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp750416) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp750418 := BSN.sin_reduce_arg_pos_rat_q1 52390907241 33554432 226375608064910080 72057594037927936 248 hp750416 hp619237 rfl rfl rfl rfl

noncomputable def hp750419 := nat_lit 14349546288676048021070925989291601464414117587119384501801781522431597859387087384539672708533789842381862680931176511203018540964593830400000

noncomputable def hp750420 := nat_lit 10185103155855385727744177668456900228054716360323603838322298709629687591724050922200093381244249010618440733618844160977761000000000000

noncomputable def hp750421 := nat_lit 71658766531322929512397423077236521173017755307177157508801183479237153420049616939268762750080455984982641287058212806473183364872985152000000

noncomputable def hp750422 := BSN.sin_dyadic_bound_f 215773009690 137438953472 4 3 67108864 21801270 hp750419 hp737934 hp750420 hp750421 hp737937

noncomputable def hp750423 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215773009690) (BSN.sinEvenQ 137438953472) 0 3 hp750419 hp737934 hp750420 rfl rfl rfl

noncomputable def hp750424 := hp750422 hp750420 67108840 rfl rfl rfl rfl rfl rfl rfl rfl (hp750423 rfl)

noncomputable def hp750425 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215773009690) (BSN.sinOddQ 137438953472) 0 3 hp750421 hp737937 hp750420 rfl rfl rfl

noncomputable def hp750426 := @BSN.sin_arg_round Bool.false 67108840 67108864 hp750416 hp619237 215773009690 137438953472 21801270 21780000 (hp750424 (hp750425 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750427 := hp750417 67108840 67108864 248 1000000000000000 21780000 10890000 hp750418 BSN.pi_near_15 hp750426 rfl rfl

noncomputable def hp750428 := @hp750373 231 33554432 Bool.true 67108840 67108864 1 10890000 hp750415 (Enclosure.sfrac_false_div 52390907241 33554432) (hp750427 rfl rfl) rfl

noncomputable def hp750429 := @hp750370 8388605 8388608 159321527 22837985280000 536870720 536870912 3746 536870912 (@hp750371 Bool.true 8388605 8388608 159321527 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000)) (@hp750372 2549144432 365407764480000 8388605 8388608 159321527 22837985280000 (hp750428 rfl) rfl))

noncomputable def hp750430 := @hp750376 hp739140 838254515863 536870912 3689 536870912 (@hp750380 hp750374 hp750375 30641292398752899871 hp739140 (hp750382 rfl rfl rfl rfl rfl) (hp750385 (hp750414 rfl) (Enclosure.Real.IsNear.const Bool.true hp750378 hp750379) rfl rfl)) rfl

noncomputable def hp750431 := hp750369 (BSN.cos_quad_nat3 427 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 518052876 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl rfl (hp750429 rfl) hp750430

noncomputable def hp750432 := nat_lit 26751729778837240907246473547714941610546924587594705484747001374378867915483653109184777167973417897728439390625

noncomputable def hp750433 := nat_lit 7294439608273752490739005065728260661089925194862432424045824147758333209881592722603772180986894775390625

noncomputable def hp750434 := nat_lit 162143655083345621872659299874356426778447426698615831442181157466885606346989585114900318001828264748659536990625

noncomputable def hp750435 := BSN.cos_dyadic_bound_f 663614695 536870912 4 3 536870912 268435456 hp750432 hp716712 hp750433 hp750434 hp716714

noncomputable def hp750436 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 663614695) (BSN.cosEvenQ 536870912) 0 3 hp750432 hp716712 hp750433 rfl rfl rfl

noncomputable def hp750437 := hp750435 hp750433 176363430 rfl rfl rfl rfl rfl rfl rfl rfl (hp750436 rfl)

noncomputable def hp750438 := @BSN.binarySplit_of_base3 (BSN.cosOddP 663614695) (BSN.cosOddQ 536870912) 0 3 hp750434 hp716714 hp750433 rfl rfl rfl

noncomputable def hp750439 := nat_lit 86442253940152801347908438036132188849636984699300700915056868714712548045943257322032330236808361734831211175441

noncomputable def hp750440 := nat_lit 14020190290875273145775137743516528722261700914552203055817680905647921602807529982096426114782251110260241

noncomputable def hp750441 := nat_lit 431955009789921619757419323683703573318587773957976993615570166902422897493036740778729258596262273306039770832401

noncomputable def hp750442 := BSN.sin_dyadic_bound_f 700749547 536870912 4 3 536870912 268435456 hp750439 hp642702 hp750440 hp750441 hp642705

noncomputable def hp750443 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 700749547) (BSN.sinEvenQ 536870912) 0 3 hp750439 hp642702 hp750440 rfl rfl rfl

noncomputable def hp750444 := hp750442 hp750440 518052876 rfl rfl rfl rfl rfl rfl rfl rfl (hp750443 rfl)

noncomputable def hp750445 := @BSN.binarySplit_of_base3 (BSN.sinOddP 700749547) (BSN.sinOddQ 536870912) 0 3 hp750441 hp642705 hp750440 rfl rfl rfl

noncomputable def hp750446 := hp750431 hd4911 hd4913 hd4915 hd4917 hd4918 (hp750437 (hp750438 rfl) rfl rfl rfl rfl) (hp750444 (hp750445 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750447 := hp750365 (BSN.cos_quad_nat0 164 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 330658792 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl rfl (hp750446 rfl rfl rfl rfl rfl) hp750430

noncomputable def hp750448 := nat_lit 13829446438655264411674078762322899411221406116322514979075258919570252225

noncomputable def hp750449 := nat_lit 3028982490181078081654755359409789778680880704283529686018812584272321

noncomputable def hp750450 := nat_lit 36215074701017780285109431916454263560223913640656794468562600045166600641

noncomputable def hp750451 := BSN.sin_dyadic_bound_f 484353113 536870912 3 2 536870912 268435456 hp750448 hp708845 hp750449 hp750450 hp708848

noncomputable def hp750452 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 484353113) (BSN.sinEvenQ 536870912) 0 2 hp750448 hp708845 hp750449 rfl rfl rfl

noncomputable def hp750453 := hp750451 hp750449 421271278 rfl rfl rfl rfl rfl rfl rfl rfl (hp750452 rfl)

noncomputable def hp750454 := @BSN.binarySplit_of_base2 (BSN.sinOddP 484353113) (BSN.sinOddQ 536870912) 0 2 hp750450 hp708848 hp750449 rfl rfl rfl

noncomputable def hp750455 := nat_lit 7859351258250622132017212598795106345275098850718588136266484494540800000

noncomputable def hp750456 := nat_lit 3168440856505005736943475354436252056320463808418936236015641600000000

noncomputable def hp750457 := nat_lit 23571716893038856384577750845676446531712655624538926536327422200422400000

noncomputable def hp750458 := BSN.cos_dyadic_bound_f 487086060 536870912 3 2 536870912 268435456 hp750455 hp708868 hp750456 hp750457 hp708870

noncomputable def hp750459 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 487086060) (BSN.cosEvenQ 536870912) 0 2 hp750455 hp708868 hp750456 rfl rfl rfl

noncomputable def hp750460 := hp750458 hp750456 330658792 rfl rfl rfl rfl rfl rfl rfl rfl (hp750459 rfl)

noncomputable def hp750461 := @BSN.binarySplit_of_base2 (BSN.cosOddP 487086060) (BSN.cosOddQ 536870912) 0 2 hp750457 hp708870 hp750456 rfl rfl rfl

noncomputable def hp750462 := hp750447 hd4920 hd4922 hd4924 hd4926 hd4918 (hp750453 (hp750454 rfl) rfl rfl rfl rfl) (hp750460 (hp750461 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750463 := hp750360 (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 147368646 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl rfl (hp750462 rfl rfl rfl rfl rfl) hp750430

noncomputable def hp750464 := nat_lit 10192953791647882339305659822730684531437519539166945593148573799451927391642310201256171536445601420850487390881

noncomputable def hp750465 := nat_lit 404534668192742808448218158917989999378851657397382617134816241011677971159753343529631782922076985520801

noncomputable def hp750466 := nat_lit 61815417355048006995866004061831698344532128964460840673747236945111035768060793923237940077082485447192673022625

noncomputable def hp750467 := BSN.cos_dyadic_bound_f 521490393 536870912 4 3 536870912 268435456 hp750464 hp716712 hp750465 hp750466 hp716714

noncomputable def hp750468 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 521490393) (BSN.cosEvenQ 536870912) 0 3 hp750464 hp716712 hp750465 rfl rfl rfl

noncomputable def hp750469 := hp750467 hp750465 302894053 rfl rfl rfl rfl rfl rfl rfl rfl (hp750468 rfl)

noncomputable def hp750470 := @BSN.binarySplit_of_base3 (BSN.cosOddP 521490393) (BSN.cosOddQ 536870912) 0 3 hp750466 hp716714 hp750465 rfl rfl rfl

noncomputable def hp750471 := nat_lit 32012443278532799414991249905044783971094872835449558511235646733484339024997665385162603697958916018717029564416

noncomputable def hp750472 := nat_lit 12489290046457288053527155574394039432182421132554107099465530199162400566506010023454022650133366110683136

noncomputable def hp750473 := nat_lit 193993887201459958068123450684253287528268582447622664633416123788327862803652159202512091624959867565427413483520

noncomputable def hp750474 := BSN.cos_dyadic_bound_f 694029844 536870912 4 3 536870912 268435456 hp750471 hp716712 hp750472 hp750473 hp716714

noncomputable def hp750475 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 694029844) (BSN.cosEvenQ 536870912) 0 3 hp750471 hp716712 hp750472 rfl rfl rfl

noncomputable def hp750476 := hp750474 hp750472 147368646 rfl rfl rfl rfl rfl rfl rfl rfl (hp750475 rfl)

noncomputable def hp750477 := @BSN.binarySplit_of_base3 (BSN.cosOddP 694029844) (BSN.cosOddQ 536870912) 0 3 hp750473 hp716714 hp750472 rfl rfl rfl

noncomputable def hp750478 := hp750463 hd4928 hd4930 hd4932 hd4934 hd4918 (hp750469 (hp750470 rfl) rfl rfl rfl rfl) (hp750476 (hp750477 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750479 := hp750355 (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 463148128 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl rfl (hp750478 rfl rfl rfl rfl rfl) hp750430

noncomputable def hp750480 := nat_lit 21090542492244773456628461089254144294863330349606367967967293485163525505

noncomputable def hp750481 := nat_lit 7043083293192664295105560115969900456249602634677212493401432886916481

noncomputable def hp750482 := nat_lit 55225732011499713787072941469763569504855746797084343476829785379325654401

noncomputable def hp750483 := BSN.sin_dyadic_bound_f 538233039 536870912 3 2 536870912 268435456 hp750480 hp708845 hp750481 hp750482 hp708848

noncomputable def hp750484 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 538233039) (BSN.sinEvenQ 536870912) 0 2 hp750480 hp708845 hp750481 rfl rfl rfl

noncomputable def hp750485 := hp750483 hp750481 452495800 rfl rfl rfl rfl rfl rfl rfl rfl (hp750484 rfl)

noncomputable def hp750486 := @BSN.binarySplit_of_base2 (BSN.sinOddP 538233039) (BSN.sinOddQ 536870912) 0 2 hp750482 hp708848 hp750481 rfl rfl rfl

noncomputable def hp750487 := nat_lit 916667243746858759565623690293014896383910122952457386051949291726671681

noncomputable def hp750488 := nat_lit 43132536281236950619765560007696417738355976272079431227787819323201

noncomputable def hp750489 := nat_lit 2749915466168013804795631539759029296316253656904827999293392299541368641

noncomputable def hp750490 := BSN.cos_dyadic_bound_f 284675849 536870912 3 2 536870912 268435456 hp750487 hp708868 hp750488 hp750489 hp708870

noncomputable def hp750491 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 284675849) (BSN.cosEvenQ 536870912) 0 2 hp750487 hp708868 hp750488 rfl rfl rfl

noncomputable def hp750492 := hp750490 hp750488 463148128 rfl rfl rfl rfl rfl rfl rfl rfl (hp750491 rfl)

noncomputable def hp750493 := @BSN.binarySplit_of_base2 (BSN.cosOddP 284675849) (BSN.cosOddQ 536870912) 0 2 hp750489 hp708870 hp750488 rfl rfl rfl

noncomputable def hp750494 := hp750479 hd4936 hd4938 hd4940 hd4942 hd4918 (hp750485 (hp750486 rfl) rfl rfl rfl rfl) (hp750492 (hp750493 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750495 := hp750350 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 496960876 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl rfl (hp750494 rfl rfl rfl rfl rfl) hp750430

noncomputable def hp750496 := nat_lit 11333883387849371282085652936008170083726503338680870651567304122522055048461044019148282338283022516847290351616

noncomputable def hp750497 := nat_lit 556050963186136192776511881892724658629886858341047707831111306903443429197253252927824404697920449806336

noncomputable def hp750498 := nat_lit 68731897975228167626038698946620070352857675995760672395682741211065503096576712649069735310509162287412983889920

noncomputable def hp750499 := BSN.cos_dyadic_bound_f 535500092 536870912 4 3 536870912 268435456 hp750496 hp716712 hp750497 hp750498 hp716714

noncomputable def hp750500 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 535500092) (BSN.cosEvenQ 536870912) 0 3 hp750496 hp716712 hp750497 rfl rfl rfl

noncomputable def hp750501 := hp750499 hp750497 291225150 rfl rfl rfl rfl rfl rfl rfl rfl (hp750500 rfl)

noncomputable def hp750502 := @BSN.binarySplit_of_base3 (BSN.cosOddP 535500092) (BSN.cosOddQ 536870912) 0 3 hp750498 hp716714 hp750497 rfl rfl rfl

noncomputable def hp750503 := nat_lit 58268770094456539608731788285328830209124482017970708211196445439411496694528187237311073893833610896067323232256

noncomputable def hp750504 := nat_lit 4298236592783096467848289012187577553789644810497332770925695740228705429428844883150117722090541999456256

noncomputable def hp750505 := nat_lit 291227346521648387433538190994670338302531338872210769194318274128552742619706336206084596299732734937974771286016

noncomputable def hp750506 := BSN.sin_dyadic_bound_f 635000684 536870912 4 3 536870912 268435456 hp750503 hp642702 hp750504 hp750505 hp642705

noncomputable def hp750507 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 635000684) (BSN.sinEvenQ 536870912) 0 3 hp750503 hp642702 hp750504 rfl rfl rfl

noncomputable def hp750508 := hp750506 hp750504 496960876 rfl rfl rfl rfl rfl rfl rfl rfl (hp750507 rfl)

noncomputable def hp750509 := @BSN.binarySplit_of_base3 (BSN.sinOddP 635000684) (BSN.sinOddQ 536870912) 0 3 hp750505 hp642705 hp750504 rfl rfl rfl

noncomputable def hp750510 := hp750495 hd4944 hd4946 hd4961 hd4963 hd4918 (hp750501 (hp750502 rfl) rfl rfl rfl rfl) (hp750508 (hp750509 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750511 := @hp750345 24555 33554432 (hp750510 rfl rfl rfl rfl rfl) (hp750510 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp750512 := @hp750343 Bool.true 97310043 134217728 24555 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 809508 1000)) (Enclosure.sfrac Bool.false 809508 1000) 11) hp750511

noncomputable def hp750513 := @Enclosure.Real.IsNear.mulLit_tf hp750334 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1))) 9959547 33554432 1

noncomputable def hp750514 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp750333 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750515 := @hp750514 1 1 0 1 9959547 33554432 1 33554432 9959547 33554432 1

noncomputable def hp750516 := @Enclosure.Real.IsNear.of_eq (hp750333 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750517 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 809508 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750518 := @hp750516 (@Inv.inv Real Real.instInv (Real.sqrt hp750335)) Bool.false 9959547 33554432 1 33554432 (hp750517 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 809508 1000) 809508 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000))))

noncomputable def hp750519 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp750335)) Bool.false 19919094 67108864 2 67108864 9959547 33554432

noncomputable def hp750520 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp750335) Bool.false 226094606 67108864 6 67108864 113047303 33554432 3 33554432

noncomputable def hp750521 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 809508 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750522 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 809508 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750523 := @hp750522 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 809508 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2161529440539

noncomputable def hp750524 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 809508 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 809508 1000 0

noncomputable def hp750525 := @hp750524 1 10680707 67108864 1 67108864 2161529440539 16777216000 202377 16777216000 (Enclosure.Real.IsNear.const Bool.false 809508 1000) hd4949

noncomputable def hp750526 := @hp750523 16777216000 202377 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 809508 1000) 809508 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000))) (hp750525 rfl)

noncomputable def hp750527 := @hp750521 2161529440539 16777216000 202377 16777216000 380864505 380864542 33554432 hp750526 rfl rfl rfl

noncomputable def hp750528 := @Enclosure.Real.IsNear.recentre' hp750335 Bool.false 761729047 67108864 37 67108864 761729047 67108864 37 67108864 (hp750527 rfl rfl rfl)

noncomputable def hp750529 := @Enclosure.Real.IsNear.sqrt_image hp750335 761729047 67108864 37 67108864 113047300 113047306 33554432 (hp750528 rfl) rfl rfl

noncomputable def hp750530 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp750335) 113047303 33554432 3 33554432 9959546 9959548 33554432 (hp750520 (hp750529 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp750531 := @hp750515 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp750518 (@hp750519 1 33554432 (hp750530 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp750532 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750533 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp750534 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1))) (hp750532 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750533 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp750535 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 809508 1000) 809508 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl

noncomputable def hp750536 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750537 := @hp750536 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750533 (Enclosure.sfrac Bool.false 1 16)))) 7096111

noncomputable def hp750538 := @hp750537 4194304 343 33554432 2096053 8388608 68430451 11418992640000 14873824749883 35184372088832 1621136522138977 127719270682460160000

noncomputable def hp750539 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750540 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750541 := @hp750539 (@Neg.neg Real Real.instNeg hp750540) Bool.true 7096111 4194304 343 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750542 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750543 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp750544 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp750545 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 147853045) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp750546 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1))) Bool.false 20808466231760071635365

noncomputable def hp750547 := nat_lit 199696958067352819412017447

noncomputable def hp750548 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp750549 := @Enclosure.Real.IsNear.subLit_ff_p hp750335 (Enclosure.sfrac Bool.false 11 1) 761729047 67108864 37 67108864 11 1 0

noncomputable def hp750550 := @hp750548 500000000000000 23531543 67108864 37 67108864 20808466231760071635365 9444732965739290427392 hp750547 hp645312 hd4948 (@hp750549 1 23531543 23531543 67108864 37 67108864 (hp750528 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750551 := @hp750545 147853045 67108864 233 67108864 Bool.true 39666090 67108864 1 10890000 (@hp750546 9444732965739290427392 hp750547 hp645312 147853045 67108864 233 67108864 (hp750550 rfl) rfl) (Enclosure.sfrac_false_div 147853045 67108864)

noncomputable def hp750552 := nat_lit 6116059493217627925381120

noncomputable def hp750553 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 147853045) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp750552) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp750554 := BSN.sin_reduce_arg_pos_rat_q1 147853045 67108864 226375608064910080 72057594037927936 0 hp750552 hp617687 rfl rfl rfl rfl

noncomputable def hp750555 := nat_lit 61576034366149714725336973109890599372198208993464865964629021535027724418752589402211203905

noncomputable def hp750556 := nat_lit 3256380954896686882100043746804079290033128404680546799539363669523927616030215206976321

noncomputable def hp750557 := nat_lit 161265293961227039168549624740790077465478112774990880450638659336274334737735589990694239041

noncomputable def hp750558 := BSN.sin_dyadic_bound_f 86914432887 137438953472 3 2 67108864 21801270 hp750555 hp738039 hp750556 hp750557 hp738042

noncomputable def hp750559 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 86914432887) (BSN.sinEvenQ 137438953472) 0 2 hp750555 hp738039 hp750556 rfl rfl rfl

noncomputable def hp750560 := hp750558 hp750556 39666090 rfl rfl rfl rfl rfl rfl rfl rfl (hp750559 rfl)

noncomputable def hp750561 := @BSN.binarySplit_of_base2 (BSN.sinOddP 86914432887) (BSN.sinOddQ 137438953472) 0 2 hp750557 hp738042 hp750556 rfl rfl rfl

noncomputable def hp750562 := @BSN.sin_arg_round Bool.false 39666090 67108864 hp750552 hp617687 86914432887 137438953472 21801270 21780000 (hp750560 (hp750561 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750563 := hp750553 39666090 67108864 0 1000000000000000 21780000 10890000 hp750554 BSN.pi_near_15 hp750562 rfl rfl

noncomputable def hp750564 := @hp750543 19833045 33554432 162779929 45675970560000 (@hp750544 39666090 67108864 2604478864 730815528960000 19833045 33554432 162779929 45675970560000 (hp750551 (hp750563 rfl rfl) rfl rfl) rfl)

noncomputable def hp750565 := @hp750542 19833045 33554432 162779929 45675970560000 56768545 56769231 33554432 hp750564 rfl rfl rfl

noncomputable def hp750566 := @Enclosure.Real.IsNear.recentre' hp750540 Bool.false 113537776 67108864 686 67108864 7096111 4194304 343 33554432 (hp750565 rfl rfl rfl)

noncomputable def hp750567 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750533 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp750568 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750533 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 122362361)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp750569 := nat_lit 1155679825811300112165165939245

noncomputable def hp750570 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750533 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp750569

noncomputable def hp750571 := nat_lit 113998992490174996221361270437420601

noncomputable def hp750572 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750533 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp750573 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp750574 := @hp750573 (Enclosure.sfrac Bool.false 1 16) 1025441602936303 4503599627370496 4224363519 4503599627370496 1 16 0

noncomputable def hp750575 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)) 553733515960849

noncomputable def hp750576 := @hp750575 4503599627370496 1741335551 4503599627370496 23531543 67108864 37 67108864 68816221071394358689792 1025441602936303 4503599627370496 4224363519

noncomputable def hp750577 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)) 23531543 67108864 37

noncomputable def hp750578 := @hp750577 67108864 23531543 67108864 37 67108864 553733515960849 4503599627370496 1741335551 4503599627370496 (@hp750549 1 23531543 23531543 67108864 37 67108864 (hp750528 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750579 := hp750578 (@hp750549 1 23531543 23531543 67108864 37 67108864 (hp750528 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750580 := @hp750576 4503599627370496 (hp750579 rfl) (@hp750549 1 23531543 23531543 67108864 37 67108864 (hp750528 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750581 := @hp750572 500000000000000 1306916579646959 4503599627370496 4224363519 4503599627370496 hp750569 hp627574 hp750571 hp738055 hd4948 (@hp750574 1 20910665274351344 1306916579646959 4503599627370496 4224363519 4503599627370496 (hp750580 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp750582 := @hp750568 122362361 67108864 99 16777216 Bool.true 8384212 33554432 1 10890000 (@hp750570 hp627574 hp750571 hp738055 122362361 67108864 99 16777216 (hp750581 rfl) rfl) (Enclosure.sfrac_true_div 122362361 67108864)

noncomputable def hp750583 := nat_lit 1852706977572191844826689939807591563203038642130356199121457865990900416955192125836207872700610592801

noncomputable def hp750584 := nat_lit 11266114948552010274565561126862206787460779199176372821033848725557740085337656979507346301861921

noncomputable def hp750585 := nat_lit 11190723220907195945426784466588013417232886669152548869201542030290489792853285333313955978707220119585

noncomputable def hp750586 := BSN.cos_dyadic_bound_t 122362361 67108864 4 3 33554432 10890000 hp750583 hp745658 hp750584 hp750585 hp745661

noncomputable def hp750587 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 122362361) (BSN.cosEvenQ 67108864) 0 3 hp750583 hp745658 hp750584 rfl rfl rfl

noncomputable def hp750588 := hp750586 hp750584 8384212 rfl rfl rfl rfl rfl rfl rfl rfl (hp750587 rfl)

noncomputable def hp750589 := @BSN.binarySplit_of_base3 (BSN.cosOddP 122362361) (BSN.cosOddQ 67108864) 0 3 hp750585 hp745661 hp750584 rfl rfl rfl

noncomputable def hp750590 := hp750582 (BSN.cos_neg_of_bound 122362361 67108864 Bool.true 8384212 33554432 1 10890000 (hp750588 (hp750589 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp750591 := hp750538 (hp750541 (@Enclosure.Real.IsNear.neg hp750540 Bool.false 7096111 4194304 343 33554432 (hp750566 rfl))) (@hp750567 8384212 33554432 1094887216 182703882240000 2096053 8388608 68430451 11418992640000 (hp750590 rfl) rfl)

noncomputable def hp750592 := @hp750513 33554432 14873824749883 35184372088832 1621136522138977 127719270682460160000 148136556666222983001 1180591620717411303424 4049944747659569848099 hp750331 (hp750531 rfl) (@hp750534 Bool.false 14873824749883 35184372088832 1621136522138977 127719270682460160000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750335 (Enclosure.sfrac Bool.false 11 1)) (hp750535 rfl (hp750338 rfl rfl))) (hp750591 rfl))

noncomputable def hp750593 := @hp750332 788086617649611877048099 hp750331 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 809508 1000))) (@hp750337 788086617649611877048099 hp750331 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 809508 1000) 11 (hp750338 rfl rfl)) (@hp750341 788086617649611877048099 hp750331 hp750512 (hp750592 rfl) rfl rfl))

theorem hd5012 : hp750330 hp750331 := hp750593

noncomputable def hp750594 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 810801 1000)) Bool.false 1168338317454464274863 1180591620717411303424 10521034204879085394819

noncomputable def hp750595 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 810801 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 810801 1000)) Bool.false 1168338317454464274863 1180591620717411303424

noncomputable def hp750596 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 810801 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750597 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp750596 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750598 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 810801 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750599 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp750597 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp750600 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 810801 1000)) hp750599 Bool.false 1168338317454464274863 1180591620717411303424

noncomputable def hp750601 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 810801 1000) 810801 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl

noncomputable def hp750602 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp750597 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp750603 := nat_lit 313623429008161876858558742528

noncomputable def hp750604 := @hp750602 232364375 268435456 196755 268435456 146388988680852754863 1180591620717411303424 50448745242648402819 hp741092 hp750603 1168338317454464274863 1180591620717411303424

noncomputable def hp750605 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) 11)

noncomputable def hp750606 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) 11) hp750605

noncomputable def hp750607 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) 11)

noncomputable def hp750608 := @hp750607 232364375 536870912 196755 536870912 232364375 536870912 196755 536870912 249499347845120000 232364375 268435456

noncomputable def hp750609 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp750610 := hp750609 BSN.quadSignNeg 9 10 11 810801 1000 192 241 536870912 268435456 9007199254740992

noncomputable def hp750611 := hp750610 Bool.false 839941132723 3695 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp750612 := hp750611 Bool.false 265376858 168909 Bool.true 447278138 Bool.true 612940588 28296951008113761 1 Bool.false 361083160

noncomputable def hp750613 := hp750612 Bool.false Bool.false 488197266 Bool.true Bool.false 232364375 196755 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 361083160 536870912) BSN.abs_quadSignNeg

noncomputable def hp750614 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp750615 := hp750614 BSN.quadSignNeg 7 8 9 810801 1000 77 138 536870912 268435456 9007199254740992

noncomputable def hp750616 := hp750615 Bool.false 839941132723 3695 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp750617 := hp750616 Bool.false 538795602 137948 Bool.true 295110616 Bool.true 123315339 28296951008113761 1 Bool.false 280472002

noncomputable def hp750618 := hp750617 Bool.true Bool.false 522770750 Bool.true Bool.false 265376858 168909 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 280472002 536870912) BSN.abs_quadSignNeg

noncomputable def hp750619 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp750620 := hp750619 BSN.quadSignPos 5 6 7 810801 1000 71 8 536870912 268435456 9007199254740992

noncomputable def hp750621 := hp750620 Bool.false 839941132723 3695 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp750622 := hp750621 Bool.false 330414169 102513 Bool.false 120999409 Bool.true 358213370 28296951008113761 1 Bool.false 119977633

noncomputable def hp750623 := hp750622 Bool.false Bool.false 421734787 Bool.false Bool.false 538795602 137948 BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 119977633 536870912) BSN.abs_quadSignPos

noncomputable def hp750624 := hp750609 BSN.quadSignNeg 3 4 5 810801 1000 280 165 536870912 268435456 9007199254740992

noncomputable def hp750625 := hp750624 Bool.false 839941132723 3695 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp750626 := hp750625 Bool.false 214608019 60593 Bool.false 365325509 Bool.false 213157987 28296951008113761 1 Bool.false 417296861

noncomputable def hp750627 := hp750626 Bool.false Bool.false 207601630 Bool.true Bool.false 330414169 102513 BSN.abs_quadSignPos (BSN.cos_quad_nat0 280 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 417296861 536870912) BSN.abs_quadSignNeg

noncomputable def hp750628 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp750629 := hp750628 BSN.quadSignPos 1 2 3 810801 1000 638 428 536870912 268435456 9007199254740992

noncomputable def hp750630 := hp750629 Bool.false 839941132723 3695 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp750631 := hp750630 Bool.false 536870704 3754 Bool.false 182437049 Bool.false 781423373 28296951008113761 1 Bool.false 506170584

noncomputable def hp750632 := hp750631 Bool.true Bool.false 61754485 Bool.false Bool.false 214608019 60593 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 638 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 506170584 536870912) BSN.abs_quadSignPos

noncomputable def hp750633 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) 1) Bool.false

noncomputable def hp750634 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)))

noncomputable def hp750635 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000))) Bool.false 67108838 67108864

noncomputable def hp750636 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 52496320795) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 52496320795 33554432

noncomputable def hp750637 := nat_lit 8007277701839213940006900556027835596384487536287753916839

noncomputable def hp750638 := nat_lit 5118066391729732529407185826625965461665839719645184000

noncomputable def hp750639 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) Bool.false hp750637 hp750638 122760284592619364023

noncomputable def hp750640 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 810801 4000) (Real.log (Enclosure.sfrac Bool.false 2629594046404 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1621602))))))

noncomputable def hp750641 := nat_lit 168194981740372193781493321920480000

noncomputable def hp750642 := nat_lit 818236101550830468281544093394218626880

noncomputable def hp750643 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp750640 (Enclosure.sfrac Bool.false 810801 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 810801 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp750641 hp750642)) Bool.false

noncomputable def hp750644 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 810801 1000) 810801 1000 2629594046404 16000000 1621602

noncomputable def hp750645 := hp750644 4000 2000 hp750641 hp750642 (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl rfl rfl rfl

noncomputable def hp750646 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp750640 (Enclosure.sfrac Bool.false 810801 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 810801 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp750641 hp750642) 28183751324978382459639 18014398509481984000

noncomputable def hp750647 := nat_lit 23060959781296936147219873601360166517587324104508731280496320

noncomputable def hp750648 := @hp750646 122760284592619364023 hp738659 hp750641 hp750642 0 1 hp750647 hp750637 hp750638 122760284592619364023 hp738659

noncomputable def hp750649 := @Enclosure.Real.IsNear.subLit_ff_p (hp750640 (Enclosure.sfrac Bool.false 810801 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 810801 2000) (Real.log Real.pi)) 7308753300164206674891 3602879701896396800 10235027510903413 4356000000000000000000

noncomputable def hp750650 := nat_lit 378275906935558814284779828019200

noncomputable def hp750651 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 810801 4000) (Real.log (Enclosure.sfrac Bool.false 2629594046404 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1621602))))))

noncomputable def hp750652 := @hp750651 (Enclosure.sfrac Bool.false 810801 2000) 43846812663764284429047 18014398509481984000 10235027510903413 4356000000000000000000 810801 2000 0

noncomputable def hp750653 := nat_lit 73087533001642066748910000

noncomputable def hp750654 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 810801 4000) (Real.log (Enclosure.sfrac Bool.false 2629594046404 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1621602))))) 43853884124283085093047

noncomputable def hp750655 := nat_lit 98734244586956388237625994744646598656

noncomputable def hp750656 := @hp750654 18014398509481984000 1126114167817657 484000000000000000000 883932564850083 2251799813685248 200000001089 8712000000000000000 hp750655 43846812663764284429047 18014398509481984000 10235027510903413

noncomputable def hp750657 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 810801 4000) (Real.log (Enclosure.sfrac Bool.false 2629594046404 16000000)) 810801 4000 0 1 54087111540665447 4503599627370496

noncomputable def hp750658 := nat_lit 116151187601131134471110656

noncomputable def hp750659 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2629594046404) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp750658 hp617687

noncomputable def hp750660 := BSN.log_rat_reduce_isNear 2629594046404 16000000 17 5259188092808 4194304000000 60733319 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp750661 := nat_lit 235466953802288080582910713341357154651906690653960130193106452063220840300607147173104851013159940587520

noncomputable def hp750662 := nat_lit 1003581789958468777726294181076354294038111361651249394770770164077785029749955099346657468675781033984

noncomputable def hp750663 := nat_lit 678216030480470474825607876303694782196712150388327477926784591675447696314320238733960420065280

noncomputable def hp750664 := BSN.log_dyadic_bound 532442046404 4726746046404 5 4 hp750661 268435456 87120000 hp750662 hp750663 60733319 5259188092808

noncomputable def hp750665 := hp750664 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp750666 := @BSN.binarySplit_of_base4 (BSN.artanhP 532442046404) (BSN.artanhQ 4726746046404) 0 4 hp750662 hp750661 hp750663 rfl rfl rfl

noncomputable def hp750667 := hp750660 rfl rfl rfl rfl (hp750665 (hp750666 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp750668 := @hp750657 12500018513 1089000000000000000 43853884124283085093047 18014398509481984000 1126114167817657 484000000000000000000 (Enclosure.Real.IsNear.const Bool.false 810801 4000) (BSN.isNear_log_sfrac 2629594046404 16000000 54087111540665447 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp750659 1000001481040000 87120000000000000000000 54087111540665447 4503599627370496 12500018513 1089000000000000000 (hp750667 rfl rfl rfl) rfl)) rfl

noncomputable def hp750669 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1621602)))) 1 4

noncomputable def hp750670 := @hp750669 0 1 883932564850083 562949953421312 200000001089 2178000000000000000 883932564850083 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp750671 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1621602))) 884279719003555 562949953421312 1

noncomputable def hp750672 := @hp750671 2000000000000000 20692 33554432 1 10890000 29659855139847700217856 883932564850083 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp750673 := BSN.arctan_dyadic_bound_f 1000 1621602 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp750674 := hp750673 1 20692 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1621602) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1621602) 0 0 rfl)

noncomputable def hp750675 := hp750670 (hp750672 (hp750674 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp750676 := @hp750649 31143483429561 67108864000 2432403 536870912000 hp750650 28183751324978382459639 18014398509481984000 122760284592619364023 hp738659 (@hp750652 1 hp750653 7308753300164206674891 3602879701896396800 10235027510903413 4356000000000000000000 (@hp750656 4356000000000000000000 hp750668 hp750675 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 810801 2000) rfl rfl)

noncomputable def hp750677 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 810801 2000) (Real.log Real.pi) 810801 2000 0 1 38410761 33554432

noncomputable def hp750678 := hp750676 (@hp750677 3 268435456 31143483429561 67108864000 2432403 536870912000 (Enclosure.Real.IsNear.const Bool.false 810801 2000) hd4909 rfl) rfl

noncomputable def hp750679 := @hp750639 hp738659 52496320795 33554432 463 67108864 (@hp750643 hp750637 hp750638 122760284592619364023 hp738659 (hp750645 rfl rfl rfl rfl rfl) (hp750648 (hp750678 rfl) (Enclosure.Real.IsNear.const Bool.true hp750641 hp750642) rfl rfl)) rfl

noncomputable def hp750680 := nat_lit 7591722125575169549271040

noncomputable def hp750681 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 52496320795) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp750680) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp750682 := BSN.sin_reduce_arg_pos_rat_q3 52496320795 33554432 226375608064910080 72057594037927936 248 hp750680 hp619237 rfl rfl rfl rfl

noncomputable def hp750683 := nat_lit 14348669544151058693218952227122998293124768539229241797945181185696080878217553651511019030253174878291794469297165827708595359934235625865441

noncomputable def hp750684 := nat_lit 10183240105108997835666483073233007051017273098421286982774449301079466735860658273482366827876151946409358236607385651269016392386953441

noncomputable def hp750685 := nat_lit 71654393660438681907271316113517768962150448645065757582707988349475587784315551689991710083775972691349603469151288763368872452618757278744801

noncomputable def hp750686 := BSN.sin_dyadic_bound_f 215769720329 137438953472 4 3 67108864 21801270 hp750683 hp737934 hp750684 hp750685 hp737937

noncomputable def hp750687 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215769720329) (BSN.sinEvenQ 137438953472) 0 3 hp750683 hp737934 hp750684 rfl rfl rfl

noncomputable def hp750688 := hp750686 hp750684 67108838 rfl rfl rfl rfl rfl rfl rfl rfl (hp750687 rfl)

noncomputable def hp750689 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215769720329) (BSN.sinOddQ 137438953472) 0 3 hp750685 hp737937 hp750684 rfl rfl rfl

noncomputable def hp750690 := @BSN.sin_arg_round Bool.false 67108838 67108864 hp750680 hp619237 215769720329 137438953472 21801270 21780000 (hp750688 (hp750689 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750691 := hp750681 67108838 67108864 248 1000000000000000 21780000 10890000 hp750682 BSN.pi_near_15 hp750690 rfl rfl

noncomputable def hp750692 := @hp750636 463 67108864 Bool.false 67108838 67108864 1 10890000 hp750679 (Enclosure.sfrac_false_div 52496320795 33554432) (hp750691 rfl rfl) rfl

noncomputable def hp750693 := @hp750633 33554419 33554432 319323679 45675970560000 536870704 536870912 3754 536870912 (@hp750634 Bool.false 33554419 33554432 319323679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000)) (@hp750635 5109178864 730815528960000 33554419 33554432 319323679 45675970560000 (hp750692 rfl) rfl))

noncomputable def hp750694 := @hp750639 hp738659 839941132723 536870912 3695 536870912 (@hp750643 hp750637 hp750638 122760284592619364023 hp738659 (hp750645 rfl rfl rfl rfl rfl) (hp750648 (hp750678 rfl) (Enclosure.Real.IsNear.const Bool.true hp750641 hp750642) rfl rfl)) rfl

noncomputable def hp750695 := hp750632 (BSN.cos_quad_nat0 428 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 61754485 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl rfl (hp750693 rfl) hp750694

noncomputable def hp750696 := nat_lit 154612421014883518384440297609959405581514812718263065753278590810918081

noncomputable def hp750697 := nat_lit 1227168813232210541667758618366307314580191663737765038157286673601

noncomputable def hp750698 := nat_lit 463834808707024090732237557312641484129915277771461721729759457859407041

noncomputable def hp750699 := BSN.cos_dyadic_bound_f 182437049 536870912 3 2 536870912 268435456 hp750696 hp708868 hp750697 hp750698 hp708870

noncomputable def hp750700 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 182437049) (BSN.cosEvenQ 536870912) 0 2 hp750696 hp708868 hp750697 rfl rfl rfl

noncomputable def hp750701 := hp750699 hp750697 506170584 rfl rfl rfl rfl rfl rfl rfl rfl (hp750700 rfl)

noncomputable def hp750702 := @BSN.binarySplit_of_base2 (BSN.cosOddP 182437049) (BSN.cosOddQ 536870912) 0 2 hp750698 hp708870 hp750697 rfl rfl rfl

noncomputable def hp750703 := nat_lit 51497887875136894721395371955245973766505096020334324223524767046799375508151650714679774477992649395990486689201

noncomputable def hp750704 := nat_lit 51836630799764448789676624336206327427772267588593712530455982878104531210424522864765203244135471984780721

noncomputable def hp750705 := nat_lit 311865317188674549953793650319776197453520447240960834204426486698500145946280554650568395756530387769433803564465

noncomputable def hp750706 := BSN.cos_dyadic_bound_f 781423373 536870912 4 3 536870912 268435456 hp750703 hp716712 hp750704 hp750705 hp716714

noncomputable def hp750707 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 781423373) (BSN.cosEvenQ 536870912) 0 3 hp750703 hp716712 hp750704 rfl rfl rfl

noncomputable def hp750708 := hp750706 hp750704 61754485 rfl rfl rfl rfl rfl rfl rfl rfl (hp750707 rfl)

noncomputable def hp750709 := @BSN.binarySplit_of_base3 (BSN.cosOddP 781423373) (BSN.cosOddQ 536870912) 0 3 hp750705 hp716714 hp750704 rfl rfl rfl

noncomputable def hp750710 := hp750695 hd4911 hd4913 hd4915 hd4917 hd4918 (hp750701 (hp750702 rfl) rfl rfl rfl rfl) (hp750708 (hp750709 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750711 := hp750627 (BSN.cos_quad_nat1 165 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 207601630 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl rfl (hp750710 rfl rfl rfl rfl rfl) hp750694

noncomputable def hp750712 := nat_lit 2486361049671902460702774996513494761896085930509316865682809413397292001

noncomputable def hp750713 := nat_lit 317278018419132628936262706753888682162960867607838911679403061322721

noncomputable def hp750714 := nat_lit 7458448592978869116850452464126976508323931869792734919225069434069230561

noncomputable def hp750715 := BSN.cos_dyadic_bound_f 365325509 536870912 3 2 536870912 268435456 hp750712 hp708868 hp750713 hp750714 hp708870

noncomputable def hp750716 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 365325509) (BSN.cosEvenQ 536870912) 0 2 hp750712 hp708868 hp750713 rfl rfl rfl

noncomputable def hp750717 := hp750715 hp750713 417296861 rfl rfl rfl rfl rfl rfl rfl rfl (hp750716 rfl)

noncomputable def hp750718 := @BSN.binarySplit_of_base2 (BSN.cosOddP 365325509) (BSN.cosOddQ 536870912) 0 2 hp750714 hp708870 hp750713 rfl rfl rfl

noncomputable def hp750719 := nat_lit 2064459849589390276839528263524561

noncomputable def hp750720 := BSN.sin_dyadic_bound_f 213157987 536870912 2 1 536870912 268435456 hp750719 hp708890 hp750719 hp750719 hp708891

noncomputable def hp750721 := @BSN.binarySplit_of_base (BSN.sinEvenP 213157987) (BSN.sinEvenQ 536870912) 0 1 hp750719 hp708890 hp750719 rfl rfl rfl

noncomputable def hp750722 := hp750720 hp750719 207601630 rfl rfl rfl rfl rfl rfl rfl rfl (hp750721 rfl)

noncomputable def hp750723 := @BSN.binarySplit_of_base (BSN.sinOddP 213157987) (BSN.sinOddQ 536870912) 0 1 hp750719 hp708891 hp750719 rfl rfl rfl

noncomputable def hp750724 := hp750711 hd4920 hd4922 hd4924 hd4926 hd4918 (hp750717 (hp750718 rfl) rfl rfl rfl rfl) (hp750722 (hp750723 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750725 := hp750623 (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 421734787 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl rfl (hp750724 rfl rfl rfl rfl rfl) hp750694

noncomputable def hp750726 := nat_lit 214354693060478838816387633216961

noncomputable def hp750727 := BSN.sin_dyadic_bound_f 120999409 536870912 2 1 536870912 268435456 hp750726 hp708890 hp750726 hp750726 hp708891

noncomputable def hp750728 := @BSN.binarySplit_of_base (BSN.sinEvenP 120999409) (BSN.sinEvenQ 536870912) 0 1 hp750726 hp708890 hp750726 rfl rfl rfl

noncomputable def hp750729 := hp750727 hp750726 119977633 rfl rfl rfl rfl rfl rfl rfl rfl (hp750728 rfl)

noncomputable def hp750730 := @BSN.binarySplit_of_base (BSN.sinOddP 120999409) (BSN.sinOddQ 536870912) 0 1 hp750726 hp708891 hp750726 rfl rfl rfl

noncomputable def hp750731 := nat_lit 2298302429546031399006328885747843264800013259827901136148894536752800000

noncomputable def hp750732 := nat_lit 271103005207485498693131374747623669355609779822936279599712100000000

noncomputable def hp750733 := nat_lit 6894365082627679226021600394494034547061328559924057535887484186058400000

noncomputable def hp750734 := BSN.cos_dyadic_bound_f 358213370 536870912 3 2 536870912 268435456 hp750731 hp708868 hp750732 hp750733 hp708870

noncomputable def hp750735 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 358213370) (BSN.cosEvenQ 536870912) 0 2 hp750731 hp708868 hp750732 rfl rfl rfl

noncomputable def hp750736 := hp750734 hp750732 421734787 rfl rfl rfl rfl rfl rfl rfl rfl (hp750735 rfl)

noncomputable def hp750737 := @BSN.binarySplit_of_base2 (BSN.cosOddP 358213370) (BSN.cosOddQ 536870912) 0 2 hp750733 hp708870 hp750732 rfl rfl rfl

noncomputable def hp750738 := hp750725 hd4928 hd4930 hd4932 hd4934 hd4918 (hp750729 (hp750730 rfl) rfl rfl rfl rfl) (hp750736 (hp750737 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750739 := hp750618 (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 522770750 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl rfl (hp750738 rfl rfl rfl rfl rfl) hp750694

noncomputable def hp750740 := nat_lit 1905520941523713373476385056540065406222148970439803541324195387198668800

noncomputable def hp750741 := nat_lit 57527918580093559665269416099721739745750469109895806096289715716096

noncomputable def hp750742 := nat_lit 4990556944503452969532026616645533657288897040868545634067784402171068416

noncomputable def hp750743 := BSN.sin_dyadic_bound_f 295110616 536870912 3 2 536870912 268435456 hp750740 hp708845 hp750741 hp750742 hp708848

noncomputable def hp750744 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 295110616) (BSN.sinEvenQ 536870912) 0 2 hp750740 hp708845 hp750741 rfl rfl rfl

noncomputable def hp750745 := hp750743 hp750741 280472002 rfl rfl rfl rfl rfl rfl rfl rfl (hp750744 rfl)

noncomputable def hp750746 := @BSN.binarySplit_of_base2 (BSN.sinOddP 295110616) (BSN.sinOddQ 536870912) 0 2 hp750742 hp708848 hp750741 rfl rfl rfl

noncomputable def hp750747 := nat_lit 231242898640317639350001660776241

noncomputable def hp750748 := BSN.cos_dyadic_bound_f 123315339 536870912 2 1 536870912 268435456 hp750747 hp708767 hp750747 hp750747 hp708768

noncomputable def hp750749 := @BSN.binarySplit_of_base (BSN.cosEvenP 123315339) (BSN.cosEvenQ 536870912) 0 1 hp750747 hp708767 hp750747 rfl rfl rfl

noncomputable def hp750750 := hp750748 hp750747 522770750 rfl rfl rfl rfl rfl rfl rfl rfl (hp750749 rfl)

noncomputable def hp750751 := @BSN.binarySplit_of_base (BSN.cosOddP 123315339) (BSN.cosOddQ 536870912) 0 1 hp750747 hp708768 hp750747 rfl rfl rfl

noncomputable def hp750752 := hp750739 hd4936 hd4938 hd4940 hd4942 hd4918 (hp750745 (hp750746 rfl) rfl rfl rfl rfl) (hp750750 (hp750751 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750753 := hp750613 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 488197266 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl rfl (hp750752 rfl rfl rfl rfl rfl) hp750694

noncomputable def hp750754 := nat_lit 5587582974251913914792901073800594823420029439416708419169546366308229376

noncomputable def hp750755 := nat_lit 1601848247538281542468592916830019115404112380845491404669033829540096

noncomputable def hp750756 := nat_lit 16759545226260665181293766035568124432029280093488434274699301031265607936

noncomputable def hp750757 := BSN.cos_dyadic_bound_f 447278138 536870912 3 2 536870912 268435456 hp750754 hp708868 hp750755 hp750756 hp708870

noncomputable def hp750758 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 447278138) (BSN.cosEvenQ 536870912) 0 2 hp750754 hp708868 hp750755 rfl rfl rfl

noncomputable def hp750759 := hp750757 hp750755 361083160 rfl rfl rfl rfl rfl rfl rfl rfl (hp750758 rfl)

noncomputable def hp750760 := @BSN.binarySplit_of_base2 (BSN.cosOddP 447278138) (BSN.cosOddQ 536870912) 0 2 hp750756 hp708870 hp750755 rfl rfl rfl

noncomputable def hp750761 := nat_lit 35479602182066750581327132988421716720416809885236671894129660680537702400

noncomputable def hp750762 := nat_lit 19922647232331858078717354533459587670378554082624043082521876375863296

noncomputable def hp750763 := nat_lit 92890511905131999942776948776621752078196746326152749367253599696799727616

noncomputable def hp750764 := BSN.sin_dyadic_bound_f 612940588 536870912 3 2 536870912 268435456 hp750761 hp708845 hp750762 hp750763 hp708848

noncomputable def hp750765 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 612940588) (BSN.sinEvenQ 536870912) 0 2 hp750761 hp708845 hp750762 rfl rfl rfl

noncomputable def hp750766 := hp750764 hp750762 488197266 rfl rfl rfl rfl rfl rfl rfl rfl (hp750765 rfl)

noncomputable def hp750767 := @BSN.binarySplit_of_base2 (BSN.sinOddP 612940588) (BSN.sinOddQ 536870912) 0 2 hp750763 hp708848 hp750762 rfl rfl rfl

noncomputable def hp750768 := hp750753 hd4944 hd4946 hd4961 hd4963 hd4918 (hp750759 (hp750760 rfl) rfl rfl rfl rfl) (hp750766 (hp750767 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750769 := @hp750608 196755 268435456 (hp750768 rfl rfl rfl rfl rfl) (hp750768 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp750770 := @hp750606 Bool.false 232364375 268435456 196755 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 810801 1000)) (Enclosure.sfrac Bool.false 810801 1000) 11) hp750769

noncomputable def hp750771 := @Enclosure.Real.IsNear.mulLit_tf hp750597 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1))) 4977787 16777216 1

noncomputable def hp750772 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp750596 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750773 := @hp750772 1 1 0 1 4977787 16777216 1 33554432 4977787 16777216 1

noncomputable def hp750774 := @Enclosure.Real.IsNear.of_eq (hp750596 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750775 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 810801 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750776 := @hp750774 (@Inv.inv Real Real.instInv (Real.sqrt hp750598)) Bool.false 4977787 16777216 1 33554432 (hp750775 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 810801 1000) 810801 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000))))

noncomputable def hp750777 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp750598)) Bool.false 19911148 67108864 2 67108864 4977787 16777216

noncomputable def hp750778 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp750598) Bool.false 226184836 67108864 6 67108864 56546209 16777216 3 33554432

noncomputable def hp750779 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 810801 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750780 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 810801 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750781 := @hp750780 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 810801 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8659927916307

noncomputable def hp750782 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 810801 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 810801 1000 0

noncomputable def hp750783 := @hp750782 1 10680707 67108864 1 67108864 8659927916307 67108864000 810801 67108864000 (Enclosure.Real.IsNear.const Bool.false 810801 1000) hd4949

noncomputable def hp750784 := @hp750781 67108864000 810801 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 810801 1000) 810801 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000))) (hp750783 rfl)

noncomputable def hp750785 := @hp750779 8659927916307 67108864000 810801 67108864000 381168555 381168592 33554432 hp750784 rfl rfl rfl

noncomputable def hp750786 := @Enclosure.Real.IsNear.recentre' hp750598 Bool.false 762337147 67108864 37 67108864 762337147 67108864 37 67108864 (hp750785 rfl rfl rfl)

noncomputable def hp750787 := @Enclosure.Real.IsNear.sqrt_image hp750598 762337147 67108864 37 67108864 113092415 113092421 33554432 (hp750786 rfl) rfl rfl

noncomputable def hp750788 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp750598) 56546209 16777216 3 33554432 9955573 9955575 33554432 (hp750778 (hp750787 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp750789 := @hp750773 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp750776 (@hp750777 1 33554432 (hp750788 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp750790 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750791 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp750792 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1))) (hp750790 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750791 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp750793 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 810801 1000) 810801 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl

noncomputable def hp750794 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750795 := @hp750794 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750791 (Enclosure.sfrac Bool.false 1 16)))) 52757487

noncomputable def hp750796 := @hp750795 33554432 37 4194304 557427 2097152 17277769 2854748160000 29408447705949 70368744177664 1136140848736127 95789453011845120000

noncomputable def hp750797 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750798 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750799 := @hp750797 (@Neg.neg Real Real.instNeg hp750798) Bool.true 52757487 33554432 37 4194304 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750800 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp750801 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp750802 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp750803 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 75836925) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp750804 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1))) Bool.false 21346196728886133430865

noncomputable def hp750805 := nat_lit 199696958068397527257096487

noncomputable def hp750806 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp750807 := @Enclosure.Real.IsNear.subLit_ff_p hp750598 (Enclosure.sfrac Bool.false 11 1) 762337147 67108864 37 67108864 11 1 0

noncomputable def hp750808 := @hp750806 500000000000000 24139643 67108864 37 67108864 21346196728886133430865 9444732965739290427392 hp750805 hp645312 hd4948 (@hp750807 1 24139643 24139643 67108864 37 67108864 (hp750786 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750809 := @hp750803 75836925 33554432 233 67108864 Bool.true 42682090 67108864 1 10890000 (@hp750804 9444732965739290427392 hp750805 hp645312 75836925 33554432 233 67108864 (hp750808 rfl) rfl) (Enclosure.sfrac_false_div 75836925 33554432)

noncomputable def hp750810 := nat_lit 3333347762196899210199040

noncomputable def hp750811 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 75836925) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp750810) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp750812 := BSN.sin_reduce_arg_pos_rat_q1 75836925 33554432 226375608064910080 72057594037927936 0 hp750810 hp619237 rfl rfl rfl rfl

noncomputable def hp750813 := nat_lit 86931435380472692247414844182613818331745519997203230217882343421483678007038539218017483585

noncomputable def hp750814 := nat_lit 6490027879989381931032344728376473361178862278147940977937227811136635435393619525532481

noncomputable def hp750815 := nat_lit 227667061189432306410579110967761676578653500882320030094775191544572554513443632091766356801

noncomputable def hp750816 := BSN.sin_dyadic_bound_f 94739441527 137438953472 3 2 67108864 21801270 hp750813 hp738039 hp750814 hp750815 hp738042

noncomputable def hp750817 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 94739441527) (BSN.sinEvenQ 137438953472) 0 2 hp750813 hp738039 hp750814 rfl rfl rfl

noncomputable def hp750818 := hp750816 hp750814 42682090 rfl rfl rfl rfl rfl rfl rfl rfl (hp750817 rfl)

noncomputable def hp750819 := @BSN.binarySplit_of_base2 (BSN.sinOddP 94739441527) (BSN.sinOddQ 137438953472) 0 2 hp750815 hp738042 hp750814 rfl rfl rfl

noncomputable def hp750820 := @BSN.sin_arg_round Bool.false 42682090 67108864 hp750810 hp619237 94739441527 137438953472 21801270 21780000 (hp750818 (hp750819 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750821 := hp750811 42682090 67108864 0 1000000000000000 21780000 10890000 hp750812 BSN.pi_near_15 hp750820 rfl rfl

noncomputable def hp750822 := @hp750801 21341045 33554432 162779929 45675970560000 (@hp750802 42682090 67108864 2604478864 730815528960000 21341045 33554432 162779929 45675970560000 (hp750809 (hp750821 rfl rfl) rfl rfl) rfl)

noncomputable def hp750823 := @hp750800 21341045 33554432 162779929 45675970560000 52757191 52757783 33554432 hp750822 rfl rfl rfl

noncomputable def hp750824 := @Enclosure.Real.IsNear.recentre' hp750798 Bool.false 105514974 67108864 592 67108864 52757487 33554432 37 4194304 (hp750823 rfl rfl rfl)

noncomputable def hp750825 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750791 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp750826 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750791 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 61734517)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp750827 := nat_lit 1166132058065216426754196788245

noncomputable def hp750828 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750791 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp750827

noncomputable def hp750829 := nat_lit 115213349692038266313900202171386001

noncomputable def hp750830 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp750791 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp750831 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp750832 := @hp750831 (Enclosure.sfrac Bool.false 1 16) 1037261654928103 4503599627370496 4269362919 4503599627370496 1 16 0

noncomputable def hp750833 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)) 582722364167449

noncomputable def hp750834 := @hp750833 4503599627370496 1786334951 4503599627370496 24139643 67108864 37 67108864 69609451332984994004992 1037261654928103 4503599627370496 4269362919

noncomputable def hp750835 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)) 24139643 67108864 37

noncomputable def hp750836 := @hp750835 67108864 24139643 67108864 37 67108864 582722364167449 4503599627370496 1786334951 4503599627370496 (@hp750807 1 24139643 24139643 67108864 37 67108864 (hp750786 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750837 := hp750836 (@hp750807 1 24139643 24139643 67108864 37 67108864 (hp750786 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750838 := @hp750834 4503599627370496 (hp750837 rfl) (@hp750807 1 24139643 24139643 67108864 37 67108864 (hp750786 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp750839 := @hp750830 500000000000000 1318736631638759 4503599627370496 4269362919 4503599627370496 hp750827 hp627574 hp750829 hp738055 hd4948 (@hp750832 1 21099786106220144 1318736631638759 4503599627370496 4269362919 4503599627370496 (hp750838 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp750840 := @hp750826 61734517 33554432 25 4194304 Bool.true 8918832 33554432 1 10890000 (@hp750828 hp627574 hp750829 hp738055 61734517 33554432 25 4194304 (hp750839 rfl) rfl) (Enclosure.sfrac_true_div 61734517 33554432)

noncomputable def hp750841 := nat_lit 469020552492009609109269764578770315166967457222147265944654900557859017037503474307368727732612241

noncomputable def hp750842 := nat_lit 3064337922563447322428502156795377969948543761338654780983699521957098632463256904770138991761

noncomputable def hp750843 := nat_lit 2832525938513263959562315223836203407468206304660632534929098096735803531931672319046491513638415505

noncomputable def hp750844 := BSN.cos_dyadic_bound_t 61734517 33554432 4 3 33554432 10890000 hp750841 hp681868 hp750842 hp750843 hp681871

noncomputable def hp750845 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 61734517) (BSN.cosEvenQ 33554432) 0 3 hp750841 hp681868 hp750842 rfl rfl rfl

noncomputable def hp750846 := hp750844 hp750842 8918832 rfl rfl rfl rfl rfl rfl rfl rfl (hp750845 rfl)

noncomputable def hp750847 := @BSN.binarySplit_of_base3 (BSN.cosOddP 61734517) (BSN.cosOddQ 33554432) 0 3 hp750843 hp681871 hp750842 rfl rfl rfl

noncomputable def hp750848 := hp750840 (BSN.cos_neg_of_bound 61734517 33554432 Bool.true 8918832 33554432 1 10890000 (hp750846 (hp750847 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp750849 := hp750796 (hp750799 (@Enclosure.Real.IsNear.neg hp750798 Bool.false 52757487 33554432 37 4194304 (hp750824 rfl))) (@hp750825 8918832 33554432 276444304 45675970560000 557427 2097152 17277769 2854748160000 (hp750848 rfl) rfl)

noncomputable def hp750850 := @hp750771 33554432 29408447705949 70368744177664 1136140848736127 95789453011845120000 146388988680852754863 1180591620717411303424 50448745242648402819 hp741092 (hp750789 rfl) (@hp750792 Bool.false 29408447705949 70368744177664 1136140848736127 95789453011845120000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750598 (Enclosure.sfrac Bool.false 11 1)) (hp750793 rfl (hp750601 rfl rfl))) (hp750849 rfl))

noncomputable def hp750851 := @hp750595 10521034204879085394819 hp741092 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 810801 1000))) (@hp750600 10521034204879085394819 hp741092 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 810801 1000) 11 (hp750601 rfl rfl)) (@hp750604 10521034204879085394819 hp741092 hp750770 (hp750850 rfl) rfl rfl))

theorem hd5013 : hp750594 hp741092 := hp750851

noncomputable def hp750852 := nat_lit 12641268729298678684736239

noncomputable def hp750853 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 812094 1000)) Bool.true 186741526178853892521597 75557863725914323419136 hp750852

noncomputable def hp750854 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 812094 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 812094 1000)) Bool.true 186741526178853892521597 75557863725914323419136

noncomputable def hp750855 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 812094 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750856 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp750855 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp750857 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 812094 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp750858 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp750856 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp750859 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 812094 1000)) hp750858 Bool.true 186741526178853892521597 75557863725914323419136

noncomputable def hp750860 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 812094 1000) 812094 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl

noncomputable def hp750861 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp750856 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp750862 := nat_lit 6266005841744572774551235067904

noncomputable def hp750863 := @hp750861 87044187 33554432 49265 67108864 9264557890129993531779 75557863725914323419136 57088988955879119936239 hp741590 hp750862 186741526178853892521597 75557863725914323419136

noncomputable def hp750864 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) 11)

noncomputable def hp750865 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) 11) hp750864

noncomputable def hp750866 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) 11)

noncomputable def hp750867 := @hp750866 696353496 536870912 197060 536870912 696353496 536870912 197060 536870912 747703872943816704 87044187 33554432

noncomputable def hp750868 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp750869 := hp750868 BSN.quadSignNeg 9 10 11 812094 1000 192 241 536870912 268435456 9007199254740992

noncomputable def hp750870 := hp750869 Bool.false 841628302819 3700 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp750871 := hp750870 Bool.true 685430527 169170 Bool.true 358502948 Bool.true 590327257 28296951008113761 1 Bool.false 421555532

noncomputable def hp750872 := hp750871 Bool.false Bool.false 478358598 Bool.true Bool.true 696353496 197060 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 421555532 536870912) BSN.abs_quadSignNeg

noncomputable def hp750873 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp750874 := hp750873 BSN.quadSignNeg 7 8 9 812094 1000 77 137 536870912 268435456 9007199254740992

noncomputable def hp750875 := hp750874 Bool.false 841628302819 3700 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp750876 := hp750875 Bool.true 488778668 138160 Bool.true 51434957 Bool.true 804716451 28296951008113761 1 Bool.false 51356309

noncomputable def hp750877 := hp750876 Bool.true Bool.false 535483990 Bool.true Bool.true 685430527 169170 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51356309 536870912) BSN.abs_quadSignNeg

noncomputable def hp750878 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp750879 := hp750878 BSN.quadSignPos 5 6 7 812094 1000 71 8 536870912 268435456 9007199254740992

noncomputable def hp750880 := hp750879 Bool.false 841628302819 3700 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp750881 := hp750880 Bool.true 881782110 102669 Bool.false 564376517 Bool.true 21843659 28296951008113761 1 Bool.false 466023365

noncomputable def hp750882 := hp750881 Bool.false Bool.false 536426596 Bool.false Bool.true 488778668 138160 BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 466023365 536870912) BSN.abs_quadSignPos

noncomputable def hp750883 := hp750873 BSN.quadSignNeg 3 4 5 812094 1000 281 165 536870912 268435456 9007199254740992

noncomputable def hp750884 := hp750883 Bool.false 841628302819 3700 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp750885 := hp750884 Bool.true 524072452 60683 Bool.false 246851141 Bool.false 783098007 28296951008113761 1 Bool.false 238244721

noncomputable def hp750886 := hp750885 Bool.true Bool.false 533497411 Bool.true Bool.true 881782110 102669 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 281 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 238244721 536870912) BSN.abs_quadSignNeg

noncomputable def hp750887 := hp750878 BSN.quadSignNeg 1 2 3 812094 1000 639 430 536870912 268435456 9007199254740992

noncomputable def hp750888 := hp750887 Bool.false 841628302819 3700 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp750889 := hp750888 Bool.true 536870904 3754 Bool.false 545127495 Bool.false 19335578 28296951008113761 1 Bool.false 456168746

noncomputable def hp750890 := hp750889 Bool.false Bool.false 536522761 Bool.true Bool.true 524072452 60683 BSN.abs_quadSignPos (BSN.cos_quad_nat3 639 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 456168746 536870912) BSN.abs_quadSignNeg

noncomputable def hp750891 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) 1) Bool.true

noncomputable def hp750892 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)))

noncomputable def hp750893 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000))) Bool.true 67108863 67108864

noncomputable def hp750894 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 26300884463) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false 26300884463 16777216

noncomputable def hp750895 := nat_lit 12656935126107541492365077550900590214167685706363108113

noncomputable def hp750896 := nat_lit 8073802035312697355735535132782747617600684530073600

noncomputable def hp750897 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) Bool.false hp750895 hp750896 5588881799555778571

noncomputable def hp750898 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 812094 4000) (Real.log (Enclosure.sfrac Bool.false 2637987659344 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1624188))))))

noncomputable def hp750899 := nat_lit 169540384378259533962662400107520000

noncomputable def hp750900 := nat_lit 826096519606543054142319035634554081280

noncomputable def hp750901 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp750898 (Enclosure.sfrac Bool.false 812094 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 812094 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp750899 hp750900)) Bool.false

noncomputable def hp750902 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 812094 1000) 812094 1000 2637987659344 16000000 1624188

noncomputable def hp750903 := hp750902 4000 2000 hp750899 hp750900 (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl rfl rfl rfl

noncomputable def hp750904 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp750898 (Enclosure.sfrac Bool.false 812094 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 812094 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp750899 hp750900) 2824036335332926379397 1801439850948198400

noncomputable def hp750905 := nat_lit 2332926282444142047872731094181996788275387829396848087388160

noncomputable def hp750906 := @hp750904 5588881799555778571 811008000000000000000000 hp750899 hp750900 0 1 hp750905 hp750895 hp750896 5588881799555778571 811008000000000000000000

noncomputable def hp750907 := @Enclosure.Real.IsNear.subLit_ff_p (hp750898 (Enclosure.sfrac Bool.false 812094 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 812094 2000) (Real.log Real.pi)) 18306855203344274467737 9007199254740992000 465963183401851 198000000000000000000

noncomputable def hp750908 := nat_lit 473794675897289377792414187520000

noncomputable def hp750909 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 812094 4000) (Real.log (Enclosure.sfrac Bool.false 2637987659344 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1624188))))))

noncomputable def hp750910 := @hp750909 (Enclosure.sfrac Bool.false 812094 2000) 21964201439134090046361 9007199254740992000 465963183401851 198000000000000000000 812094 2000 0

noncomputable def hp750911 := nat_lit 36613710406688548935474000

noncomputable def hp750912 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 812094 4000) (Real.log (Enclosure.sfrac Bool.false 2637987659344 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1624188))))) 21967737171608082890361

noncomputable def hp750913 := nat_lit 49458984708387399956084618066581782528

noncomputable def hp750914 := @hp750912 9007199254740992000 1691865005716037 726000000000000000000 883933118498211 2251799813685248 200000001089 8712000000000000000 hp750913 21964201439134090046361 9007199254740992000 465963183401851

noncomputable def hp750915 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 812094 4000) (Real.log (Enclosure.sfrac Bool.false 2637987659344 16000000)) 812094 4000 0 1 54101464046300263 4503599627370496

noncomputable def hp750916 := nat_lit 116182009372289729690599424

noncomputable def hp750917 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2637987659344) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp750916 hp617687

noncomputable def hp750918 := BSN.log_rat_reduce_isNear 2637987659344 16000000 17 5275975318688 4194304000000 61588795 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp750919 := nat_lit 238832898998779827853247874451531841553522143251671830816006947015408404077784411446189615373496740741120

noncomputable def hp750920 := nat_lit 1046781038930384493830554250136900019555667125036122389072331137282609324346017181471628921735011631104

noncomputable def hp750921 := nat_lit 768620294905006902805788884824767639350584877626427525201621274597862302215863776609000153415680

noncomputable def hp750922 := BSN.log_dyadic_bound 540835659344 4735139659344 5 4 hp750919 268435456 87120000 hp750920 hp750921 61588795 5275975318688

noncomputable def hp750923 := hp750922 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp750924 := @BSN.binarySplit_of_base4 (BSN.artanhP 540835659344) (BSN.artanhQ 4735139659344) 0 4 hp750920 hp750919 hp750921 rfl rfl rfl

noncomputable def hp750925 := hp750918 rfl rfl rfl rfl (hp750923 (hp750924 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp750926 := @hp750915 12500018513 1089000000000000000 21967737171608082890361 9007199254740992000 1691865005716037 726000000000000000000 (Enclosure.Real.IsNear.const Bool.false 812094 4000) (BSN.isNear_log_sfrac 2637987659344 16000000 54101464046300263 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp750917 1000001481040000 87120000000000000000000 54101464046300263 4503599627370496 12500018513 1089000000000000000 (hp750925 rfl rfl rfl) rfl)) rfl

noncomputable def hp750927 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1624188)))) 1 4

noncomputable def hp750928 := @hp750927 0 1 883933118498211 562949953421312 200000001089 2178000000000000000 883933118498211 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp750929 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1624188))) 884279719003555 562949953421312 1

noncomputable def hp750930 := @hp750929 2000000000000000 20659 33554432 1 10890000 29659873717196163121152 883933118498211 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp750931 := BSN.arctan_dyadic_bound_f 1000 1624188 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp750932 := hp750931 1 20659 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1624188) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1624188) 0 0 rfl)

noncomputable def hp750933 := hp750928 (hp750930 (hp750932 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp750934 := @hp750907 15596574271767 33554432000 1218141 268435456000 hp750908 2824036335332926379397 1801439850948198400 5588881799555778571 811008000000000000000000 (@hp750910 1 hp750911 18306855203344274467737 9007199254740992000 465963183401851 198000000000000000000 (@hp750914 198000000000000000000 hp750926 hp750933 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 812094 2000) rfl rfl)

noncomputable def hp750935 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 812094 2000) (Real.log Real.pi) 812094 2000 0 1 38410761 33554432

noncomputable def hp750936 := hp750934 (@hp750935 3 268435456 15596574271767 33554432000 1218141 268435456000 (Enclosure.Real.IsNear.const Bool.false 812094 2000) hd4909 rfl) rfl

noncomputable def hp750937 := @hp750897 811008000000000000000000 26300884463 16777216 463 67108864 (@hp750901 hp750895 hp750896 5588881799555778571 811008000000000000000000 (hp750903 rfl rfl rfl rfl rfl) (hp750906 (hp750936 rfl) (Enclosure.Real.IsNear.const Bool.true hp750899 hp750900) rfl rfl)) rfl

noncomputable def hp750938 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 26300884463) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 342257534813440311296) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp750939 := BSN.sin_reduce_arg_pos_rat_q2 26300884463 16777216 226375608064910080 72057594037927936 249 342257534813440311296 hp619230 rfl rfl rfl rfl

noncomputable def hp750940 := BSN.cos_dyadic_bound_f 19455088 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp750941 := hp750940 1 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 19455088) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp750942 := hp750941 (@BSN.binarySplit_of_le (BSN.cosOddP 19455088) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp750943 := @BSN.cos_arg_round Bool.false 67108863 67108864 342257534813440311296 hp619230 19455088 137438953472 21801270 21780000 hp750942 rfl

noncomputable def hp750944 := hp750938 67108863 67108864 249 1000000000000000 21780000 10890000 hp750939 BSN.pi_near_15 hp750943 rfl rfl

noncomputable def hp750945 := @hp750894 463 67108864 Bool.true 67108863 67108864 1 10890000 hp750937 (Enclosure.sfrac_false_div 26300884463 16777216) (hp750944 rfl rfl) rfl

noncomputable def hp750946 := @hp750891 67108863 67108864 319323679 45675970560000 536870904 536870912 3754 536870912 (@hp750892 Bool.true 67108863 67108864 319323679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000)) (@hp750893 5109178864 730815528960000 67108863 67108864 319323679 45675970560000 (hp750945 rfl) rfl))

noncomputable def hp750947 := @hp750897 811008000000000000000000 841628302819 536870912 3700 536870912 (@hp750901 hp750895 hp750896 5588881799555778571 811008000000000000000000 (hp750903 rfl rfl rfl rfl rfl) (hp750906 (hp750936 rfl) (Enclosure.Real.IsNear.const Bool.true hp750899 hp750900) rfl rfl)) rfl

noncomputable def hp750948 := hp750890 (BSN.cos_quad_nat2 430 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536522761 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl rfl (hp750946 rfl) hp750947

noncomputable def hp750949 := nat_lit 22192501770862796449464557165223629212461939842418201646722709180310930625

noncomputable def hp750950 := nat_lit 7798026366949862763909731952126922437062405564211531830990154687890625

noncomputable def hp750951 := nat_lit 58110593547665595685075129200044156729645074740181804689880730459891090625

noncomputable def hp750952 := BSN.sin_dyadic_bound_f 545127495 536870912 3 2 536870912 268435456 hp750949 hp708845 hp750950 hp750951 hp708848

noncomputable def hp750953 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 545127495) (BSN.sinEvenQ 536870912) 0 2 hp750949 hp708845 hp750950 rfl rfl rfl

noncomputable def hp750954 := hp750952 hp750950 456168746 rfl rfl rfl rfl rfl rfl rfl rfl (hp750953 rfl)

noncomputable def hp750955 := @BSN.binarySplit_of_base2 (BSN.sinOddP 545127495) (BSN.sinOddQ 536870912) 0 2 hp750951 hp708848 hp750950 rfl rfl rfl

noncomputable def hp750956 := nat_lit 139774721631873701889703799056

noncomputable def hp750957 := BSN.cos_dyadic_bound_f 19335578 536870912 2 1 536870912 268435456 hp750956 hp708767 hp750956 hp750956 hp708768

noncomputable def hp750958 := @BSN.binarySplit_of_base (BSN.cosEvenP 19335578) (BSN.cosEvenQ 536870912) 0 1 hp750956 hp708767 hp750956 rfl rfl rfl

noncomputable def hp750959 := hp750957 hp750956 536522761 rfl rfl rfl rfl rfl rfl rfl rfl (hp750958 rfl)

noncomputable def hp750960 := @BSN.binarySplit_of_base (BSN.cosOddP 19335578) (BSN.cosOddQ 536870912) 0 1 hp750956 hp708768 hp750956 rfl rfl rfl

noncomputable def hp750961 := hp750948 hd4911 hd4913 hd4915 hd4917 hd4918 (hp750954 (hp750955 rfl) rfl rfl rfl rfl) (hp750959 (hp750960 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750962 := hp750886 (BSN.cos_quad_nat1 165 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533497411 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl rfl (hp750961 rfl rfl rfl rfl rfl) hp750947

noncomputable def hp750963 := nat_lit 932842359146591614998173850313629309204762730626613904751341769073197025

noncomputable def hp750964 := nat_lit 13787359878389329261313890858683157588958803349088761211353515261921

noncomputable def hp750965 := nat_lit 2443136237277460647033556052140972227566853599292852178259171965690806241

noncomputable def hp750966 := BSN.sin_dyadic_bound_f 246851141 536870912 3 2 536870912 268435456 hp750963 hp708845 hp750964 hp750965 hp708848

noncomputable def hp750967 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 246851141) (BSN.sinEvenQ 536870912) 0 2 hp750963 hp708845 hp750964 rfl rfl rfl

noncomputable def hp750968 := hp750966 hp750964 238244721 rfl rfl rfl rfl rfl rfl rfl rfl (hp750967 rfl)

noncomputable def hp750969 := @BSN.binarySplit_of_base2 (BSN.sinOddP 246851141) (BSN.sinOddQ 536870912) 0 2 hp750965 hp708848 hp750964 rfl rfl rfl

noncomputable def hp750970 := nat_lit 134887695573019994501584275352036164899735461311366691413995167320505346387173274875709678792957022395847147701601

noncomputable def hp750971 := nat_lit 53185521767396633278936604742156358417536387872029552248888987681575936787538818628137628589957451455055201

noncomputable def hp750972 := nat_lit 673815087339985991571122490766635524468731373400871138495218715864848367355070036935224775559829544932262187025761

noncomputable def hp750973 := BSN.sin_dyadic_bound_f 783098007 536870912 4 3 536870912 268435456 hp750970 hp642702 hp750971 hp750972 hp642705

noncomputable def hp750974 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 783098007) (BSN.sinEvenQ 536870912) 0 3 hp750970 hp642702 hp750971 rfl rfl rfl

noncomputable def hp750975 := hp750973 hp750971 533497411 rfl rfl rfl rfl rfl rfl rfl rfl (hp750974 rfl)

noncomputable def hp750976 := @BSN.binarySplit_of_base3 (BSN.sinOddP 783098007) (BSN.sinOddQ 536870912) 0 3 hp750972 hp642705 hp750971 rfl rfl rfl

noncomputable def hp750977 := hp750962 hd4920 hd4922 hd4924 hd4926 hd4918 (hp750968 (hp750969 rfl) rfl rfl rfl rfl) (hp750975 (hp750976 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750978 := hp750882 (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536426596 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl rfl (hp750977 rfl rfl rfl rfl rfl) hp750947

noncomputable def hp750979 := nat_lit 25498367491308502239612451611805832324180709274843142254639244113972591585

noncomputable def hp750980 := nat_lit 10293225330180500164399903153288384417877817070030712471836609481833441

noncomputable def hp750981 := nat_lit 66764773445749594579671201997243284417130055444571037132434094359338580961

noncomputable def hp750982 := BSN.sin_dyadic_bound_f 564376517 536870912 3 2 536870912 268435456 hp750979 hp708845 hp750980 hp750981 hp708848

noncomputable def hp750983 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 564376517) (BSN.sinEvenQ 536870912) 0 2 hp750979 hp708845 hp750980 rfl rfl rfl

noncomputable def hp750984 := hp750982 hp750980 466023365 rfl rfl rfl rfl rfl rfl rfl rfl (hp750983 rfl)

noncomputable def hp750985 := @BSN.binarySplit_of_base2 (BSN.sinOddP 564376517) (BSN.sinOddQ 536870912) 0 2 hp750981 hp708848 hp750980 rfl rfl rfl

noncomputable def hp750986 := nat_lit 227667769489259765002505574961

noncomputable def hp750987 := BSN.cos_dyadic_bound_f 21843659 536870912 2 1 536870912 268435456 hp750986 hp708767 hp750986 hp750986 hp708768

noncomputable def hp750988 := @BSN.binarySplit_of_base (BSN.cosEvenP 21843659) (BSN.cosEvenQ 536870912) 0 1 hp750986 hp708767 hp750986 rfl rfl rfl

noncomputable def hp750989 := hp750987 hp750986 536426596 rfl rfl rfl rfl rfl rfl rfl rfl (hp750988 rfl)

noncomputable def hp750990 := @BSN.binarySplit_of_base (BSN.cosOddP 21843659) (BSN.cosOddQ 536870912) 0 1 hp750986 hp708768 hp750986 rfl rfl rfl

noncomputable def hp750991 := hp750978 hd4928 hd4930 hd4932 hd4934 hd4918 (hp750984 (hp750985 rfl) rfl rfl rfl rfl) (hp750989 (hp750990 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp750992 := hp750877 (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535483990 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl rfl (hp750991 rfl rfl rfl rfl rfl) hp750947

noncomputable def hp750993 := nat_lit 6998960208225687528184383238801

noncomputable def hp750994 := BSN.sin_dyadic_bound_f 51434957 536870912 2 1 536870912 268435456 hp750993 hp708890 hp750993 hp750993 hp708891

noncomputable def hp750995 := @BSN.binarySplit_of_base (BSN.sinEvenP 51434957) (BSN.sinEvenQ 536870912) 0 1 hp750993 hp708890 hp750993 rfl rfl rfl

noncomputable def hp750996 := hp750994 hp750993 51356309 rfl rfl rfl rfl rfl rfl rfl rfl (hp750995 rfl)

noncomputable def hp750997 := @BSN.binarySplit_of_base (BSN.sinOddP 51434957) (BSN.sinOddQ 536870912) 0 1 hp750993 hp708891 hp750993 rfl rfl rfl

noncomputable def hp750998 := nat_lit 150436811347465560023023640063618533478492396411847209409543801864877618121407799597285625712064867896264638642801

noncomputable def hp750999 := nat_lit 73741939787998644742004969066356154549150615030614388271864046215477543586372160211659679015715499137612401

noncomputable def hp751000 := nat_lit 751408896758540104388687856642546301485222824582798956610907143113482412168625763076430817132121551715857125390961

noncomputable def hp751001 := BSN.sin_dyadic_bound_f 804716451 536870912 4 3 536870912 268435456 hp750998 hp642702 hp750999 hp751000 hp642705

noncomputable def hp751002 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 804716451) (BSN.sinEvenQ 536870912) 0 3 hp750998 hp642702 hp750999 rfl rfl rfl

noncomputable def hp751003 := hp751001 hp750999 535483990 rfl rfl rfl rfl rfl rfl rfl rfl (hp751002 rfl)

noncomputable def hp751004 := @BSN.binarySplit_of_base3 (BSN.sinOddP 804716451) (BSN.sinOddQ 536870912) 0 3 hp751000 hp642705 hp750999 rfl rfl rfl

noncomputable def hp751005 := hp750992 hd4936 hd4938 hd4940 hd4942 hd4918 (hp750996 (hp750997 rfl) rfl rfl rfl rfl) (hp751003 (hp751004 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751006 := hp750872 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 478358598 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl rfl (hp751005 rfl rfl rfl rfl rfl) hp750947

noncomputable def hp751007 := nat_lit 2305744074034076002024574920781307280044640888314978523558059350006235136

noncomputable def hp751008 := nat_lit 272861241034374186159974611308488936293039740996887308005531891859456

noncomputable def hp751009 := nat_lit 6916686499620159257701404813121304862261336585462941796058166986234986496

noncomputable def hp751010 := BSN.cos_dyadic_bound_f 358502948 536870912 3 2 536870912 268435456 hp751007 hp708868 hp751008 hp751009 hp708870

noncomputable def hp751011 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 358502948) (BSN.cosEvenQ 536870912) 0 2 hp751007 hp708868 hp751008 rfl rfl rfl

noncomputable def hp751012 := hp751010 hp751008 421555532 rfl rfl rfl rfl rfl rfl rfl rfl (hp751011 rfl)

noncomputable def hp751013 := @BSN.binarySplit_of_base2 (BSN.cosOddP 358502948) (BSN.cosOddQ 536870912) 0 2 hp751009 hp708870 hp751008 rfl rfl rfl

noncomputable def hp751014 := nat_lit 30524075398603274619053676467291324903522782243711727628622427648533155265

noncomputable def hp751015 := nat_lit 14748324677976567842939521185249171123463171247857007280329873359588801

noncomputable def hp751016 := nat_lit 79920128756387090511490107713367828470264536932462756253652490713099881921

noncomputable def hp751017 := BSN.sin_dyadic_bound_f 590327257 536870912 3 2 536870912 268435456 hp751014 hp708845 hp751015 hp751016 hp708848

noncomputable def hp751018 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 590327257) (BSN.sinEvenQ 536870912) 0 2 hp751014 hp708845 hp751015 rfl rfl rfl

noncomputable def hp751019 := hp751017 hp751015 478358598 rfl rfl rfl rfl rfl rfl rfl rfl (hp751018 rfl)

noncomputable def hp751020 := @BSN.binarySplit_of_base2 (BSN.sinOddP 590327257) (BSN.sinOddQ 536870912) 0 2 hp751016 hp708848 hp751015 rfl rfl rfl

noncomputable def hp751021 := hp751006 hd4944 hd4946 hd4961 hd4963 hd4918 (hp751012 (hp751013 rfl) rfl rfl rfl rfl) (hp751019 (hp751020 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751022 := @hp750867 49265 67108864 (hp751021 rfl rfl rfl rfl rfl) (hp751021 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp751023 := @hp750865 Bool.true 87044187 33554432 49265 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 812094 1000)) (Enclosure.sfrac Bool.false 812094 1000) 11) hp751022

noncomputable def hp751024 := @Enclosure.Real.IsNear.mulLit_tf hp750856 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1))) 19903217 67108864 1

noncomputable def hp751025 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp750855 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751026 := @hp751025 1 1 0 1 19903217 67108864 1 67108864 19903217 67108864 1

noncomputable def hp751027 := @Enclosure.Real.IsNear.of_eq (hp750855 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751028 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 812094 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751029 := @hp751027 (@Inv.inv Real Real.instInv (Real.sqrt hp750857)) Bool.false 19903217 67108864 1 67108864 (hp751028 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 812094 1000) 812094 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000))))

noncomputable def hp751030 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp750857)) Bool.false 19903217 67108864 1 67108864 19903217 67108864

noncomputable def hp751031 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp750857) Bool.false 226274957 67108864 7 67108864 226274957 67108864 7 67108864

noncomputable def hp751032 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 812094 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751033 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 812094 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751034 := @hp751033 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 812094 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4336869035229

noncomputable def hp751035 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 812094 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 812094 1000 0

noncomputable def hp751036 := @hp751035 1 10680707 67108864 1 67108864 4336869035229 33554432000 406047 33554432000 (Enclosure.Real.IsNear.const Bool.false 812094 1000) hd4949

noncomputable def hp751037 := @hp751034 33554432000 406047 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 812094 1000) 812094 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000))) (hp751036 rfl)

noncomputable def hp751038 := @hp751032 4336869035229 33554432000 406047 33554432000 381472362 381472399 33554432 hp751037 rfl rfl rfl

noncomputable def hp751039 := @Enclosure.Real.IsNear.recentre' hp750857 Bool.false 762944761 67108864 37 67108864 762944761 67108864 37 67108864 (hp751038 rfl rfl rfl)

noncomputable def hp751040 := @Enclosure.Real.IsNear.sqrt_image hp750857 762944761 67108864 37 67108864 113137475 113137482 33554432 (hp751039 rfl) rfl rfl

noncomputable def hp751041 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp750857) 226274957 67108864 7 67108864 9951608 9951609 33554432 (hp751031 (hp751040 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp751042 := @hp751026 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp751029 (@hp751030 1 67108864 (hp751041 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp751043 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751044 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp751045 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1))) (hp751043 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751044 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp751046 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 812094 1000) 812094 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl

noncomputable def hp751047 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751048 := @hp751047 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751044 (Enclosure.sfrac Bool.false 1 16)))) 49427611

noncomputable def hp751049 := @hp751048 33554432 261 33554432 9417417 33554432 279847429 45675970560000 465480424100787 1125899906842624 8589070835378669 766315624094760960000

noncomputable def hp751050 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751051 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751052 := @hp751050 (@Neg.neg Real Real.instNeg hp751051) Bool.true 49427611 33554432 261 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751053 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751054 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp751055 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp751056 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 155491601) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp751057 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1))) Bool.false 21883497466068759498635

noncomputable def hp751058 := nat_lit 998484790347207000802665923

noncomputable def hp751059 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp751060 := @Enclosure.Real.IsNear.subLit_ff_p hp750857 (Enclosure.sfrac Bool.false 11 1) 762944761 67108864 37 67108864 11 1 0

noncomputable def hp751061 := @hp751059 500000000000000 24747257 67108864 37 67108864 21883497466068759498635 9444732965739290427392 hp751058 hp738031 hd4948 (@hp751060 1 24747257 24747257 67108864 37 67108864 (hp751039 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751062 := @hp751056 155491601 67108864 117 33554432 Bool.true 45557529 67108864 1 10890000 (@hp751057 9444732965739290427392 hp751058 hp738031 155491601 67108864 117 33554432 (hp751061 rfl) rfl) (Enclosure.sfrac_false_div 155491601 67108864)

noncomputable def hp751063 := nat_lit 7216891427785585251581952

noncomputable def hp751064 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 155491601) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp751063) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp751065 := BSN.sin_reduce_arg_pos_rat_q1 155491601 67108864 226375608064910080 72057594037927936 0 hp751063 hp617687 rfl rfl rfl rfl

noncomputable def hp751066 := nat_lit 119384283358617929535335542812709402425434279956813593577331543145448545332919240209737890625

noncomputable def hp751067 := nat_lit 12239480072560305252188888372590452490403035732199765083119089338855136791699371337890625

noncomputable def hp751068 := nat_lit 312653306781024717812613353928302336095914842590945374035257563045816615174268592043337890625

noncomputable def hp751069 := BSN.sin_dyadic_bound_f 102558195575 137438953472 3 2 67108864 21801270 hp751066 hp738039 hp751067 hp751068 hp738042

noncomputable def hp751070 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 102558195575) (BSN.sinEvenQ 137438953472) 0 2 hp751066 hp738039 hp751067 rfl rfl rfl

noncomputable def hp751071 := hp751069 hp751067 45557529 rfl rfl rfl rfl rfl rfl rfl rfl (hp751070 rfl)

noncomputable def hp751072 := @BSN.binarySplit_of_base2 (BSN.sinOddP 102558195575) (BSN.sinOddQ 137438953472) 0 2 hp751068 hp738042 hp751067 rfl rfl rfl

noncomputable def hp751073 := @BSN.sin_arg_round Bool.false 45557529 67108864 hp751063 hp617687 102558195575 137438953472 21801270 21780000 (hp751071 (hp751072 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751074 := hp751064 45557529 67108864 0 1000000000000000 21780000 10890000 hp751065 BSN.pi_near_15 hp751073 rfl rfl

noncomputable def hp751075 := @hp751054 45557529 67108864 81730277 22837985280000 (@hp751055 45557529 67108864 1307684432 365407764480000 45557529 67108864 81730277 22837985280000 (hp751062 (hp751074 rfl rfl) rfl rfl) rfl)

noncomputable def hp751076 := @hp751053 45557529 67108864 81730277 22837985280000 49427350 49427872 33554432 hp751075 rfl rfl rfl

noncomputable def hp751077 := @Enclosure.Real.IsNear.recentre' hp751051 Bool.false 98855222 67108864 522 67108864 49427611 33554432 261 33554432 (hp751076 rfl rfl rfl)

noncomputable def hp751078 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751044 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp751079 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751044 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 62252831)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp751080 := nat_lit 1175922732755331700386563288525

noncomputable def hp751081 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751044 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp751080

noncomputable def hp751082 := nat_lit 23285347273335819829047955557601409

noncomputable def hp751083 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751044 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp751084 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp751085 := @hp751084 (Enclosure.sfrac Bool.false 1 16) 1048333575361999 4503599627370496 4314326355 4503599627370496 1 16 0

noncomputable def hp751086 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)) 612426729024049

noncomputable def hp751087 := @hp751086 4503599627370496 1831298387 4503599627370496 24747257 67108864 37 67108864 70352475335602141659136 1048333575361999 4503599627370496 4314326355

noncomputable def hp751088 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)) 24747257 67108864 37

noncomputable def hp751089 := @hp751088 67108864 24747257 67108864 37 67108864 612426729024049 4503599627370496 1831298387 4503599627370496 (@hp751060 1 24747257 24747257 67108864 37 67108864 (hp751039 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751090 := hp751089 (@hp751060 1 24747257 24747257 67108864 37 67108864 (hp751039 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751091 := @hp751087 4503599627370496 (hp751090 rfl) (@hp751060 1 24747257 24747257 67108864 37 67108864 (hp751039 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751092 := @hp751083 500000000000000 1329808552072655 4503599627370496 4314326355 4503599627370496 hp751080 hp627574 hp751082 hp742826 hd4948 (@hp751085 1 21276936833162480 1329808552072655 4503599627370496 4314326355 4503599627370496 (hp751091 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp751093 := @hp751079 62252831 33554432 405 67108864 Bool.true 9417417 33554432 1 10890000 (@hp751081 hp627574 hp751082 hp742826 62252831 33554432 405 67108864 (hp751092 rfl) rfl) (Enclosure.sfrac_true_div 62252831 33554432)

noncomputable def hp751094 := nat_lit 485083291702527341707156584882460589154240369978823498904548591085467601467283972597676724330803841

noncomputable def hp751095 := nat_lit 3387733771269297215537108942520679351368025202576919376272750182538156550307627362136257311361

noncomputable def hp751096 := nat_lit 2929082705696956637992363941114966010572181123106103276451412966071042315605081920752525973333848705

noncomputable def hp751097 := BSN.cos_dyadic_bound_t 62252831 33554432 4 3 33554432 10890000 hp751094 hp681868 hp751095 hp751096 hp681871

noncomputable def hp751098 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 62252831) (BSN.cosEvenQ 33554432) 0 3 hp751094 hp681868 hp751095 rfl rfl rfl

noncomputable def hp751099 := hp751097 hp751095 9417417 rfl rfl rfl rfl rfl rfl rfl rfl (hp751098 rfl)

noncomputable def hp751100 := @BSN.binarySplit_of_base3 (BSN.cosOddP 62252831) (BSN.cosOddQ 33554432) 0 3 hp751096 hp681871 hp751095 rfl rfl rfl

noncomputable def hp751101 := hp751093 (BSN.cos_neg_of_bound 62252831 33554432 Bool.true 9417417 33554432 1 10890000 (hp751099 (hp751100 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp751102 := hp751049 (hp751052 (@Enclosure.Real.IsNear.neg hp751051 Bool.false 49427611 33554432 261 33554432 (hp751077 rfl))) (@hp751078 9417417 33554432 4477558864 730815528960000 9417417 33554432 279847429 45675970560000 (hp751101 rfl) rfl)

noncomputable def hp751103 := @hp751024 67108864 465480424100787 1125899906842624 8589070835378669 766315624094760960000 9264557890129993531779 75557863725914323419136 57088988955879119936239 hp741590 (hp751042 rfl) (@hp751045 Bool.false 465480424100787 1125899906842624 8589070835378669 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp750857 (Enclosure.sfrac Bool.false 11 1)) (hp751046 rfl (hp750860 rfl rfl))) (hp751102 rfl))

noncomputable def hp751104 := @hp750854 hp750852 hp741590 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 812094 1000))) (@hp750859 hp750852 hp741590 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 812094 1000) 11 (hp750860 rfl rfl)) (@hp750863 hp750852 hp741590 hp751023 (hp751103 rfl) rfl rfl))

theorem hd5014 : hp750853 hp741590 := hp751104

noncomputable def hp751105 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 813386 1000)) Bool.false 65765378703299323461187 37778931862957161709568 421977255240610470725531

noncomputable def hp751106 := nat_lit 571406344427227070857216000

noncomputable def hp751107 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 813386 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 813386 1000)) Bool.false 65765378703299323461187 37778931862957161709568

noncomputable def hp751108 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 813386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751109 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp751108 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751110 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 813386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751111 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp751109 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp751112 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 813386 1000)) hp751111 Bool.false 65765378703299323461187 37778931862957161709568

noncomputable def hp751113 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 813386 1000) 813386 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl

noncomputable def hp751114 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp751109 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp751115 := nat_lit 8826879710616421298897615323136

noncomputable def hp751116 := @hp751114 217360519 134217728 197389 268435456 4583831679958222470723 37778931862957161709568 1804269894941662021531 hp751106 hp751115 65765378703299323461187 37778931862957161709568

noncomputable def hp751117 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) 11)

noncomputable def hp751118 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) 11) hp751117

noncomputable def hp751119 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) 11)

noncomputable def hp751120 := @hp751119 434721038 536870912 197389 536870912 434721038 536870912 197389 536870912 466778160273293312 217360519 134217728

noncomputable def hp751121 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp751122 := hp751121 BSN.quadSignNeg 9 10 11 813386 1000 192 241 536870912 268435456 9007199254740992

noncomputable def hp751123 := hp751122 Bool.false 843314720062 3707 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp751124 := hp751123 Bool.false 426782599 169454 Bool.true 269244420 Bool.true 567179418 28296951008113761 1 Bool.false 470760177

noncomputable def hp751125 := hp751124 Bool.false Bool.false 467408651 Bool.true Bool.false 434721038 197389 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 470760177 536870912) BSN.abs_quadSignNeg

noncomputable def hp751126 := hp751121 BSN.quadSignNeg 7 8 9 813386 1000 76 137 536870912 268435456 9007199254740992

noncomputable def hp751127 := hp751126 Bool.false 843314720062 3707 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp751128 := hp751127 Bool.false 526706156 138394 Bool.true 650710616 Bool.true 642375932 28296951008113761 1 Bool.false 188499257

noncomputable def hp751129 := hp751128 Bool.false Bool.false 499704337 Bool.true Bool.false 426782599 169454 BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 188499257 536870912) BSN.abs_quadSignNeg

noncomputable def hp751130 := hp751121 BSN.quadSignPos 5 6 7 813386 1000 72 7 536870912 268435456 9007199254740992

noncomputable def hp751131 := hp751130 Bool.false 843314720062 3707 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp751132 := hp751131 Bool.false 148737163 102845 Bool.false 164647858 Bool.true 528496956 28296951008113761 1 Bool.false 511821026

noncomputable def hp751133 := hp751132 Bool.false Bool.false 447182057 Bool.false Bool.false 526706156 138394 BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 511821026 536870912) BSN.abs_quadSignPos

noncomputable def hp751134 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp751135 := hp751134 BSN.quadSignNeg 3 4 5 813386 1000 282 166 536870912 268435456 9007199254740992

noncomputable def hp751136 := hp751135 Bool.false 843314720062 3707 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp751137 := hp751136 Bool.false 549265715 60791 Bool.false 128368181 Bool.false 509834377 28296951008113761 1 Bool.false 521597191

noncomputable def hp751138 := hp751137 Bool.true Bool.false 312445691 Bool.true Bool.false 148737163 102845 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 282 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 521597191 536870912) BSN.abs_quadSignNeg

noncomputable def hp751139 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp751140 := hp751139 BSN.quadSignPos 1 2 3 813386 1000 641 431 536870912 268435456 9007199254740992

noncomputable def hp751141 := hp751140 Bool.false 843314720062 3707 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp751142 := hp751141 Bool.false 536870888 3770 Bool.false 64122362 Bool.false 100399599 28296951008113761 1 Bool.false 63970017

noncomputable def hp751143 := hp751142 Bool.true Bool.false 99815420 Bool.false Bool.false 549265715 60791 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 641 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63970017 536870912) BSN.abs_quadSignPos

noncomputable def hp751144 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) 1) Bool.false

noncomputable def hp751145 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)))

noncomputable def hp751146 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000))) Bool.false 67108861 67108864

noncomputable def hp751147 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 105414340007) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 105414340007 67108864

noncomputable def hp751148 := nat_lit 115234562873732126673978322892600672320313310925248786491

noncomputable def hp751149 := nat_lit 73360613057189159665143741836141568657970675738214400

noncomputable def hp751150 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) Bool.false hp751148 hp751149 61575181843415664739

noncomputable def hp751151 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 813386 4000) (Real.log (Enclosure.sfrac Bool.false 2646388139984 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1626772))))))

noncomputable def hp751152 := nat_lit 170893332339135723541491072404480000

noncomputable def hp751153 := nat_lit 834013611179093000659392394438118215680

noncomputable def hp751154 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp751151 (Enclosure.sfrac Bool.false 813386 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 813386 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp751152 hp751153)) Bool.false

noncomputable def hp751155 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 813386 1000) 813386 1000 2646388139984 16000000 1626772

noncomputable def hp751156 := hp751155 4000 2000 hp751152 hp751153 (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl rfl rfl rfl

noncomputable def hp751157 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp751151 (Enclosure.sfrac Bool.false 813386 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 813386 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp751152 hp751153) 2829695012017393227751 1801439850948198400

noncomputable def hp751158 := nat_lit 2360003847654033954283076052840461769120016607749095147335680

noncomputable def hp751159 := @hp751157 61575181843415664739 hp739631 hp751152 hp751153 0 1 hp751158 hp751148 hp751149 61575181843415664739 hp739631

noncomputable def hp751160 := @Enclosure.Real.IsNear.subLit_ff_p (hp751151 (Enclosure.sfrac Bool.false 813386 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 813386 2000) (Real.log Real.pi)) 18341809370119853651843 9007199254740992000 5133670029379759 2178000000000000000000

noncomputable def hp751161 := nat_lit 474744044307384019389157212160000

noncomputable def hp751162 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 813386 4000) (Real.log (Enclosure.sfrac Bool.false 2646388139984 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1626772))))))

noncomputable def hp751163 := @hp751162 (Enclosure.sfrac Bool.false 813386 2000) 22004974256628231911299 9007199254740992000 5133670029379759 2178000000000000000000 813386 2000 0

noncomputable def hp751164 := nat_lit 36683618740239707303686000

noncomputable def hp751165 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 813386 4000) (Real.log (Enclosure.sfrac Bool.false 2646388139984 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1626772))))) 22008509991316817267299

noncomputable def hp751166 := nat_lit 49550796931224131227789703447840817152

noncomputable def hp751167 := @hp751165 9007199254740992000 5083670029107509 2178000000000000000000 883933672146339 2251799813685248 200000001089 8712000000000000000 hp751166 22004974256628231911299 9007199254740992000 5133670029379759

noncomputable def hp751168 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 813386 4000) (Real.log (Enclosure.sfrac Bool.false 2646388139984 16000000)) 813386 4000 0 1 54115782645181543 4503599627370496

noncomputable def hp751169 := nat_lit 116212758329249549583908864

noncomputable def hp751170 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2646388139984) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp751169 hp617687

noncomputable def hp751171 := BSN.log_rat_reduce_isNear 2646388139984 16000000 17 5292776279968 4194304000000 62442250 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp751172 := nat_lit 242243675928238300855353454596702268754670782853885556722849390481053638920106427262217235362973713694720

noncomputable def hp751173 := nat_lit 1091332789116315343306909930424965449711006078154628308285903366756819211840062078629486597103863988224

noncomputable def hp751174 := nat_lit 869485110410656154450854513269109047033284844342759408120090533094619987806663416956667905966080

noncomputable def hp751175 := BSN.log_dyadic_bound 549236139984 4743540139984 5 4 hp751172 268435456 87120000 hp751173 hp751174 62442250 5292776279968

noncomputable def hp751176 := hp751175 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp751177 := @BSN.binarySplit_of_base4 (BSN.artanhP 549236139984) (BSN.artanhQ 4743540139984) 0 4 hp751173 hp751172 hp751174 rfl rfl rfl

noncomputable def hp751178 := hp751171 rfl rfl rfl rfl (hp751176 (hp751177 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp751179 := @hp751168 12500018513 1089000000000000000 22008509991316817267299 9007199254740992000 5083670029107509 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 813386 4000) (BSN.isNear_log_sfrac 2646388139984 16000000 54115782645181543 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp751170 1000001481040000 87120000000000000000000 54115782645181543 4503599627370496 12500018513 1089000000000000000 (hp751178 rfl rfl rfl) rfl)) rfl

noncomputable def hp751180 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1626772)))) 1 4

noncomputable def hp751181 := @hp751180 0 1 883933672146339 562949953421312 200000001089 2178000000000000000 883933672146339 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp751182 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1626772))) 884279719003555 562949953421312 1

noncomputable def hp751183 := @hp751182 2000000000000000 20626 33554432 1 10890000 29659892294544626024448 883933672146339 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp751184 := BSN.arctan_dyadic_bound_f 1000 1626772 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp751185 := hp751184 1 20626 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1626772) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1626772) 0 0 rfl)

noncomputable def hp751186 := hp751181 (hp751183 (hp751185 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp751187 := @hp751160 15621387623373 33554432000 1220079 268435456000 hp751161 2829695012017393227751 1801439850948198400 61575181843415664739 hp739631 (@hp751163 1 hp751164 18341809370119853651843 9007199254740992000 5133670029379759 2178000000000000000000 (@hp751167 2178000000000000000000 hp751179 hp751186 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 813386 2000) rfl rfl)

noncomputable def hp751188 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 813386 2000) (Real.log Real.pi) 813386 2000 0 1 38410761 33554432

noncomputable def hp751189 := hp751187 (@hp751188 3 268435456 15621387623373 33554432000 1220079 268435456000 (Enclosure.Real.IsNear.const Bool.false 813386 2000) hd4909 rfl) rfl

noncomputable def hp751190 := @hp751150 hp739631 105414340007 67108864 465 67108864 (@hp751154 hp751148 hp751149 61575181843415664739 hp739631 (hp751156 rfl rfl rfl rfl rfl) (hp751159 (hp751189 rfl) (Enclosure.Real.IsNear.const Bool.true hp751152 hp751153) rfl rfl)) rfl

noncomputable def hp751191 := nat_lit 15189351350214621317300224

noncomputable def hp751192 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 105414340007) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp751191) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp751193 := BSN.sin_reduce_arg_pos_rat_q3 105414340007 67108864 226375608064910080 72057594037927936 249 hp751191 hp617687 rfl rfl rfl rfl

noncomputable def hp751194 := nat_lit 14371056795951262659782963341360842638785888896400001017595531748395619922788441266837107981629596875921540577931886283692061097615976600436736

noncomputable def hp751195 := nat_lit 10230883279175519965590944323959401325713378943342603392166213458500841801243235742658202252314852461557892477679564780954997541186830336

noncomputable def hp751196 := nat_lit 71766052618846513082874798528766906105176306403331836367368965378125342129063057147730489398731575651174340344623921565357141693337569639530496

noncomputable def hp751197 := BSN.sin_dyadic_bound_f 215853665256 137438953472 4 3 67108864 21801270 hp751194 hp737934 hp751195 hp751196 hp737937

noncomputable def hp751198 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215853665256) (BSN.sinEvenQ 137438953472) 0 3 hp751194 hp737934 hp751195 rfl rfl rfl

noncomputable def hp751199 := hp751197 hp751195 67108861 rfl rfl rfl rfl rfl rfl rfl rfl (hp751198 rfl)

noncomputable def hp751200 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215853665256) (BSN.sinOddQ 137438953472) 0 3 hp751196 hp737937 hp751195 rfl rfl rfl

noncomputable def hp751201 := @BSN.sin_arg_round Bool.false 67108861 67108864 hp751191 hp617687 215853665256 137438953472 21801270 21780000 (hp751199 (hp751200 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751202 := hp751192 67108861 67108864 249 1000000000000000 21780000 10890000 hp751193 BSN.pi_near_15 hp751201 rfl rfl

noncomputable def hp751203 := @hp751147 465 67108864 Bool.false 67108861 67108864 1 10890000 hp751190 (Enclosure.sfrac_false_div 105414340007 67108864) (hp751202 rfl rfl) rfl

noncomputable def hp751204 := @hp751144 67108861 67108864 320684929 45675970560000 536870888 536870912 3770 536870912 (@hp751145 Bool.false 67108861 67108864 320684929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000)) (@hp751146 5130958864 730815528960000 67108861 67108864 320684929 45675970560000 (hp751203 rfl) rfl))

noncomputable def hp751205 := @hp751150 hp739631 843314720062 536870912 3707 536870912 (@hp751154 hp751148 hp751149 61575181843415664739 hp739631 (hp751156 rfl rfl rfl rfl rfl) (hp751159 (hp751189 rfl) (Enclosure.Real.IsNear.const Bool.true hp751152 hp751153) rfl rfl)) rfl

noncomputable def hp751206 := hp751143 (BSN.cos_quad_nat3 431 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 99815420 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl rfl (hp751204 rfl) hp751205

noncomputable def hp751207 := nat_lit 16905890288897008460557825393936

noncomputable def hp751208 := BSN.sin_dyadic_bound_f 64122362 536870912 2 1 536870912 268435456 hp751207 hp708890 hp751207 hp751207 hp708891

noncomputable def hp751209 := @BSN.binarySplit_of_base (BSN.sinEvenP 64122362) (BSN.sinEvenQ 536870912) 0 1 hp751207 hp708890 hp751207 rfl rfl rfl

noncomputable def hp751210 := hp751208 hp751207 63970017 rfl rfl rfl rfl rfl rfl rfl rfl (hp751209 rfl)

noncomputable def hp751211 := @BSN.binarySplit_of_base (BSN.sinOddP 64122362) (BSN.sinOddQ 536870912) 0 1 hp751207 hp708891 hp751207 rfl rfl rfl

noncomputable def hp751212 := nat_lit 101608002310230716953335535361601

noncomputable def hp751213 := BSN.sin_dyadic_bound_f 100399599 536870912 2 1 536870912 268435456 hp751212 hp708890 hp751212 hp751212 hp708891

noncomputable def hp751214 := @BSN.binarySplit_of_base (BSN.sinEvenP 100399599) (BSN.sinEvenQ 536870912) 0 1 hp751212 hp708890 hp751212 rfl rfl rfl

noncomputable def hp751215 := hp751213 hp751212 99815420 rfl rfl rfl rfl rfl rfl rfl rfl (hp751214 rfl)

noncomputable def hp751216 := @BSN.binarySplit_of_base (BSN.sinOddP 100399599) (BSN.sinOddQ 536870912) 0 1 hp751212 hp708891 hp751212 rfl rfl rfl

noncomputable def hp751217 := hp751206 hd4911 hd4913 hd4915 hd4917 hd4918 (hp751210 (hp751211 rfl) rfl rfl rfl rfl) (hp751215 (hp751216 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751218 := hp751138 (BSN.cos_quad_nat2 166 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 312445691 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl rfl (hp751217 rfl rfl rfl rfl rfl) hp751205

noncomputable def hp751219 := nat_lit 271537333473922912945407028035121

noncomputable def hp751220 := BSN.cos_dyadic_bound_f 128368181 536870912 2 1 536870912 268435456 hp751219 hp708767 hp751219 hp751219 hp708768

noncomputable def hp751221 := @BSN.binarySplit_of_base (BSN.cosEvenP 128368181) (BSN.cosEvenQ 536870912) 0 1 hp751219 hp708767 hp751219 rfl rfl rfl

noncomputable def hp751222 := hp751220 hp751219 521597191 rfl rfl rfl rfl rfl rfl rfl rfl (hp751221 rfl)

noncomputable def hp751223 := @BSN.binarySplit_of_base (BSN.cosOddP 128368181) (BSN.cosOddQ 536870912) 0 1 hp751219 hp708768 hp751219 rfl rfl rfl

noncomputable def hp751224 := nat_lit 9311322757949467885192244010939559946402590965464179328524802861304216833797914627114308785666822354011147583201

noncomputable def hp751225 := nat_lit 308424868043669514044331791665438777975589754061596685731667036139625646621653854583693621510442589994721

noncomputable def hp751226 := nat_lit 56470468184011288065052343206729896863909036270017893777113719245156531251965852746940472571200529469090249162465

noncomputable def hp751227 := BSN.cos_dyadic_bound_f 509834377 536870912 4 3 536870912 268435456 hp751224 hp716712 hp751225 hp751226 hp716714

noncomputable def hp751228 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 509834377) (BSN.cosEvenQ 536870912) 0 3 hp751224 hp716712 hp751225 rfl rfl rfl

noncomputable def hp751229 := hp751227 hp751225 312445691 rfl rfl rfl rfl rfl rfl rfl rfl (hp751228 rfl)

noncomputable def hp751230 := @BSN.binarySplit_of_base3 (BSN.cosOddP 509834377) (BSN.cosOddQ 536870912) 0 3 hp751226 hp716714 hp751225 rfl rfl rfl

noncomputable def hp751231 := hp751218 hd4920 hd4922 hd4924 hd4926 hd4918 (hp751222 (hp751223 rfl) rfl rfl rfl rfl) (hp751229 (hp751230 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751232 := hp751133 (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 447182057 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl rfl (hp751231 rfl rfl rfl rfl rfl) hp751205

noncomputable def hp751233 := nat_lit 102568831019645528531216931239958516029048223719415404597673028506992896

noncomputable def hp751234 := nat_lit 540068292783799735085550280993589004029096492805925777298886082816

noncomputable def hp751235 := nat_lit 307705412922351017994180622619313560909136612965260601941464487748813056

noncomputable def hp751236 := BSN.cos_dyadic_bound_f 164647858 536870912 3 2 536870912 268435456 hp751233 hp708868 hp751234 hp751235 hp708870

noncomputable def hp751237 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 164647858) (BSN.cosEvenQ 536870912) 0 2 hp751233 hp708868 hp751234 rfl rfl rfl

noncomputable def hp751238 := hp751236 hp751234 511821026 rfl rfl rfl rfl rfl rfl rfl rfl (hp751237 rfl)

noncomputable def hp751239 := @BSN.binarySplit_of_base2 (BSN.cosOddP 164647858) (BSN.cosOddQ 536870912) 0 2 hp751235 hp708870 hp751234 rfl rfl rfl

noncomputable def hp751240 := nat_lit 19604965703656021070410469052017743780150963920493618857874497146269532160

noncomputable def hp751241 := nat_lit 6086111742553207429390671720689413315736839437768166727092707975561216

noncomputable def hp751242 := nat_lit 51336485042944492848570310239165355612169903004107853310208390046364532736

noncomputable def hp751243 := BSN.sin_dyadic_bound_f 528496956 536870912 3 2 536870912 268435456 hp751240 hp708845 hp751241 hp751242 hp708848

noncomputable def hp751244 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 528496956) (BSN.sinEvenQ 536870912) 0 2 hp751240 hp708845 hp751241 rfl rfl rfl

noncomputable def hp751245 := hp751243 hp751241 447182057 rfl rfl rfl rfl rfl rfl rfl rfl (hp751244 rfl)

noncomputable def hp751246 := @BSN.binarySplit_of_base2 (BSN.sinOddP 528496956) (BSN.sinOddQ 536870912) 0 2 hp751242 hp708848 hp751241 rfl rfl rfl

noncomputable def hp751247 := hp751232 hd4928 hd4930 hd4932 hd4934 hd4918 (hp751238 (hp751239 rfl) rfl rfl rfl rfl) (hp751245 (hp751246 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751248 := hp751129 (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 499704337 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl rfl (hp751247 rfl rfl rfl rfl rfl) hp751205

noncomputable def hp751249 := nat_lit 24728280363882625464752035313926366776603924530967047887852787823327357134893431246537257734667390969385934913536

noncomputable def hp751250 := nat_lit 5763080751790389029543055714476345983229785477212087832466291469012346021665571090366208956812462030585856

noncomputable def hp751251 := nat_lit 149889895763243414576798314348735356061247861861463874534860254340826151437579254616824820044661773944817776066560

noncomputable def hp751252 := BSN.cos_dyadic_bound_f 650710616 536870912 4 3 536870912 268435456 hp751249 hp716712 hp751250 hp751251 hp716714

noncomputable def hp751253 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 650710616) (BSN.cosEvenQ 536870912) 0 3 hp751249 hp716712 hp751250 rfl rfl rfl

noncomputable def hp751254 := hp751252 hp751250 188499257 rfl rfl rfl rfl rfl rfl rfl rfl (hp751253 rfl)

noncomputable def hp751255 := @BSN.binarySplit_of_base3 (BSN.cosOddP 650710616) (BSN.cosOddQ 536870912) 0 3 hp751251 hp716714 hp751250 rfl rfl rfl

noncomputable def hp751256 := nat_lit 61025227040436053520966024226818728592262027330698172579463828831424813527768579874786061442563269032101361483776

noncomputable def hp751257 := nat_lit 4937090970232084444218028091402993645043823404377323560939294029084142552010523324712733805894741184741376

noncomputable def hp751258 := nat_lit 304998354807900815313820357878097620414253002813878900715159171622703113348722017129190106358678559467307255463936

noncomputable def hp751259 := BSN.sin_dyadic_bound_f 642375932 536870912 4 3 536870912 268435456 hp751256 hp642702 hp751257 hp751258 hp642705

noncomputable def hp751260 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 642375932) (BSN.sinEvenQ 536870912) 0 3 hp751256 hp642702 hp751257 rfl rfl rfl

noncomputable def hp751261 := hp751259 hp751257 499704337 rfl rfl rfl rfl rfl rfl rfl rfl (hp751260 rfl)

noncomputable def hp751262 := @BSN.binarySplit_of_base3 (BSN.sinOddP 642375932) (BSN.sinOddQ 536870912) 0 3 hp751258 hp642705 hp751257 rfl rfl rfl

noncomputable def hp751263 := hp751248 hd4936 hd4938 hd4940 hd4942 hd4918 (hp751254 (hp751255 rfl) rfl rfl rfl rfl) (hp751261 (hp751262 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751264 := hp751125 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 467408651 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl rfl (hp751263 rfl rfl rfl rfl rfl) hp751205

noncomputable def hp751265 := nat_lit 733486249605268958419914477684219853962381503973873069531656728780800000

noncomputable def hp751266 := nat_lit 27616821419987072904447824004738837808422368341089125912601600000000

noncomputable def hp751267 := nat_lit 2200403515172966901113934537404650084211527667184937030343144983142400000

noncomputable def hp751268 := BSN.cos_dyadic_bound_f 269244420 536870912 3 2 536870912 268435456 hp751265 hp708868 hp751266 hp751267 hp708870

noncomputable def hp751269 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 269244420) (BSN.cosEvenQ 536870912) 0 2 hp751265 hp708868 hp751266 rfl rfl rfl

noncomputable def hp751270 := hp751268 hp751266 470760177 rfl rfl rfl rfl rfl rfl rfl rfl (hp751269 rfl)

noncomputable def hp751271 := @BSN.binarySplit_of_base2 (BSN.cosOddP 269244420) (BSN.cosOddQ 536870912) 0 2 hp751267 hp708870 hp751266 rfl rfl rfl

noncomputable def hp751272 := nat_lit 26008900624585952293429671851040140463010108371958590345880802422903415040

noncomputable def hp751273 := nat_lit 10709364519046175680900212314256172358390361963904845472705163499806976

noncomputable def hp751274 := nat_lit 68101210283741895531689587837548715028827175626235700203684388461937828096

noncomputable def hp751275 := BSN.sin_dyadic_bound_f 567179418 536870912 3 2 536870912 268435456 hp751272 hp708845 hp751273 hp751274 hp708848

noncomputable def hp751276 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 567179418) (BSN.sinEvenQ 536870912) 0 2 hp751272 hp708845 hp751273 rfl rfl rfl

noncomputable def hp751277 := hp751275 hp751273 467408651 rfl rfl rfl rfl rfl rfl rfl rfl (hp751276 rfl)

noncomputable def hp751278 := @BSN.binarySplit_of_base2 (BSN.sinOddP 567179418) (BSN.sinOddQ 536870912) 0 2 hp751274 hp708848 hp751273 rfl rfl rfl

noncomputable def hp751279 := hp751264 hd4944 hd4946 hd4961 hd4963 hd4918 (hp751270 (hp751271 rfl) rfl rfl rfl rfl) (hp751277 (hp751278 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751280 := @hp751120 197389 268435456 (hp751279 rfl rfl rfl rfl rfl) (hp751279 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp751281 := @hp751118 Bool.false 217360519 134217728 197389 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 813386 1000)) (Enclosure.sfrac Bool.false 813386 1000) 11) hp751280

noncomputable def hp751282 := @Enclosure.Real.IsNear.mulLit_tf hp751109 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1))) 19895309 67108864 1

noncomputable def hp751283 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp751108 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751284 := @hp751283 1 1 0 1 19895309 67108864 1 67108864 19895309 67108864 1

noncomputable def hp751285 := @Enclosure.Real.IsNear.of_eq (hp751108 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751286 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 813386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751287 := @hp751285 (@Inv.inv Real Real.instInv (Real.sqrt hp751110)) Bool.false 19895309 67108864 1 67108864 (hp751286 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 813386 1000) 813386 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000))))

noncomputable def hp751288 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp751110)) Bool.false 19895309 67108864 1 67108864 19895309 67108864

noncomputable def hp751289 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp751110) Bool.false 226364901 67108864 7 67108864 226364901 67108864 7 67108864

noncomputable def hp751290 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 813386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751291 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 813386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751292 := @hp751291 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 813386 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4343768771951

noncomputable def hp751293 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 813386 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 813386 1000 0

noncomputable def hp751294 := @hp751293 1 10680707 67108864 1 67108864 4343768771951 33554432000 406693 33554432000 (Enclosure.Real.IsNear.const Bool.false 813386 1000) hd4949

noncomputable def hp751295 := @hp751292 33554432000 406693 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 813386 1000) 813386 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000))) (hp751294 rfl)

noncomputable def hp751296 := @hp751290 4343768771951 33554432000 406693 33554432000 381775693 381775730 33554432 hp751295 rfl rfl rfl

noncomputable def hp751297 := @Enclosure.Real.IsNear.recentre' hp751110 Bool.false 763551423 67108864 37 67108864 763551423 67108864 37 67108864 (hp751296 rfl rfl rfl)

noncomputable def hp751298 := @Enclosure.Real.IsNear.sqrt_image hp751110 763551423 67108864 37 67108864 113182447 113182454 33554432 (hp751297 rfl) rfl rfl

noncomputable def hp751299 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp751110) 226364901 67108864 7 67108864 9947654 9947655 33554432 (hp751289 (hp751298 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp751300 := @hp751284 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp751287 (@hp751288 1 67108864 (hp751299 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp751301 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751302 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp751303 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1))) (hp751301 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751302 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp751304 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 813386 1000) 813386 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl

noncomputable def hp751305 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751306 := @hp751305 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751302 (Enclosure.sfrac Bool.false 1 16)))) 93278121

noncomputable def hp751307 := @hp751306 67108864 463 67108864 2470007 8388608 282569929 45675970560000 230397611816847 562949953421312 254567944963637 23947363252961280000

noncomputable def hp751308 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751309 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751310 := @hp751308 (@Neg.neg Real Real.instNeg hp751309) Bool.true 93278121 67108864 463 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751311 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751312 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp751313 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp751314 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 159303371) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp751315 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1))) Bool.false 22419956368958894182045

noncomputable def hp751316 := nat_lit 998484790352418187702117827

noncomputable def hp751317 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp751318 := @Enclosure.Real.IsNear.subLit_ff_p hp751110 (Enclosure.sfrac Bool.false 11 1) 763551423 67108864 37 67108864 11 1 0

noncomputable def hp751319 := @hp751317 500000000000000 25353919 67108864 37 67108864 22419956368958894182045 9444732965739290427392 hp751316 hp738031 hd4948 (@hp751318 1 25353919 25353919 67108864 37 67108864 (hp751297 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751320 := @hp751314 159303371 67108864 233 67108864 Bool.true 48281415 67108864 1 10890000 (@hp751315 9444732965739290427392 hp751316 hp738031 159303371 67108864 233 67108864 (hp751319 rfl) rfl) (Enclosure.sfrac_false_div 159303371 67108864)

noncomputable def hp751321 := nat_lit 7766225378237490388795392

noncomputable def hp751322 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 159303371) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp751321) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp751323 := BSN.sin_reduce_arg_pos_rat_q1 159303371 67108864 226375608064910080 72057594037927936 0 hp751321 hp617687 rfl rfl rfl rfl

noncomputable def hp751324 := nat_lit 160103790059626843137648859250941767001365645237306619165224757591312572944532026035181730625

noncomputable def hp751325 := nat_lit 22011088179789786784750404171411740477024243151847411638466087825135975530603780937890625

noncomputable def hp751326 := nat_lit 419283813156255405705714559288569961233280555418319106766269229549339851846724804923005090625

noncomputable def hp751327 := BSN.sin_dyadic_bound_f 110364700535 137438953472 3 2 67108864 21801270 hp751324 hp738039 hp751325 hp751326 hp738042

noncomputable def hp751328 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 110364700535) (BSN.sinEvenQ 137438953472) 0 2 hp751324 hp738039 hp751325 rfl rfl rfl

noncomputable def hp751329 := hp751327 hp751325 48281415 rfl rfl rfl rfl rfl rfl rfl rfl (hp751328 rfl)

noncomputable def hp751330 := @BSN.binarySplit_of_base2 (BSN.sinOddP 110364700535) (BSN.sinOddQ 137438953472) 0 2 hp751326 hp738042 hp751325 rfl rfl rfl

noncomputable def hp751331 := @BSN.sin_arg_round Bool.false 48281415 67108864 hp751321 hp617687 110364700535 137438953472 21801270 21780000 (hp751329 (hp751330 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751332 := hp751322 48281415 67108864 0 1000000000000000 21780000 10890000 hp751323 BSN.pi_near_15 hp751331 rfl rfl

noncomputable def hp751333 := @hp751312 48281415 67108864 162779929 45675970560000 (@hp751313 48281415 67108864 2604478864 730815528960000 48281415 67108864 162779929 45675970560000 (hp751320 (hp751332 rfl rfl) rfl rfl) rfl)

noncomputable def hp751334 := @hp751311 48281415 67108864 162779929 45675970560000 46638829 46639292 33554432 hp751333 rfl rfl rfl

noncomputable def hp751335 := @Enclosure.Real.IsNear.recentre' hp751309 Bool.false 93278121 67108864 463 67108864 93278121 67108864 463 67108864 (hp751334 rfl rfl rfl)

noncomputable def hp751336 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751302 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp751337 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751302 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 125471695)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp751338 := nat_lit 1185046658400509409359979344605

noncomputable def hp751339 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751302 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp751338

noncomputable def hp751340 := nat_lit 117638221926273038810225698115748393

noncomputable def hp751341 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751302 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp751342 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp751343 := @hp751342 (Enclosure.sfrac Bool.false 1 16) 1058651493379455 4503599627370496 4359219343 4503599627370496 1 16 0

noncomputable def hp751344 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)) 642821208658561

noncomputable def hp751345 := @hp751344 4503599627370496 1876191375 4503599627370496 25353919 67108864 37 67108864 71044899092598745989120 1058651493379455 4503599627370496 4359219343

noncomputable def hp751346 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)) 25353919 67108864 37

noncomputable def hp751347 := @hp751346 67108864 25353919 67108864 37 67108864 642821208658561 4503599627370496 1876191375 4503599627370496 (@hp751318 1 25353919 25353919 67108864 37 67108864 (hp751297 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751348 := hp751347 (@hp751318 1 25353919 25353919 67108864 37 67108864 (hp751297 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751349 := @hp751345 4503599627370496 (hp751348 rfl) (@hp751318 1 25353919 25353919 67108864 37 67108864 (hp751297 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751350 := @hp751341 500000000000000 1340126470090111 4503599627370496 4359219343 4503599627370496 hp751338 hp627574 hp751340 hp738055 hd4948 (@hp751343 1 21442023521441776 1340126470090111 4503599627370496 4359219343 4503599627370496 (hp751349 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp751351 := @hp751337 125471695 67108864 409 67108864 Bool.true 9880028 33554432 1 10890000 (@hp751339 hp627574 hp751340 hp738055 125471695 67108864 409 67108864 (hp751350 rfl) rfl) (Enclosure.sfrac_true_div 125471695 67108864)

noncomputable def hp751352 := nat_lit 2049739131359684963839499724211497250930964199227650576286022550567682649183112015614155352625741890625

noncomputable def hp751353 := nat_lit 15224715264345867637821698839627903436887992994670205912815404686242206304884264623226933837890625

noncomputable def hp751354 := nat_lit 12375143579617906072739689387410138307380311104343367166413590156671922971636248081681892324961255490625

noncomputable def hp751355 := BSN.cos_dyadic_bound_t 125471695 67108864 4 3 33554432 10890000 hp751352 hp745658 hp751353 hp751354 hp745661

noncomputable def hp751356 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 125471695) (BSN.cosEvenQ 67108864) 0 3 hp751352 hp745658 hp751353 rfl rfl rfl

noncomputable def hp751357 := hp751355 hp751353 9880028 rfl rfl rfl rfl rfl rfl rfl rfl (hp751356 rfl)

noncomputable def hp751358 := @BSN.binarySplit_of_base3 (BSN.cosOddP 125471695) (BSN.cosOddQ 67108864) 0 3 hp751354 hp745661 hp751353 rfl rfl rfl

noncomputable def hp751359 := hp751351 (BSN.cos_neg_of_bound 125471695 67108864 Bool.true 9880028 33554432 1 10890000 (hp751357 (hp751358 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp751360 := hp751307 (hp751310 (@Enclosure.Real.IsNear.neg hp751309 Bool.false 93278121 67108864 463 67108864 (hp751335 rfl))) (@hp751336 9880028 33554432 4521118864 730815528960000 2470007 8388608 282569929 45675970560000 (hp751359 rfl) rfl)

noncomputable def hp751361 := @hp751282 67108864 230397611816847 562949953421312 254567944963637 23947363252961280000 4583831679958222470723 37778931862957161709568 1804269894941662021531 hp751106 (hp751300 rfl) (@hp751303 Bool.false 230397611816847 562949953421312 254567944963637 23947363252961280000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751110 (Enclosure.sfrac Bool.false 11 1)) (hp751304 rfl (hp751113 rfl rfl))) (hp751360 rfl))

noncomputable def hp751362 := @hp751107 421977255240610470725531 hp751106 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 813386 1000))) (@hp751112 421977255240610470725531 hp751106 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 813386 1000) 11 (hp751113 rfl rfl)) (@hp751116 421977255240610470725531 hp751106 hp751281 (hp751361 rfl) rfl rfl))

theorem hd5015 : hp751105 hp751106 := hp751362

noncomputable def hp751363 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 814678 1000)) Bool.true 13016006086865015373005 18889465931478580854784 432132676092571296169351

noncomputable def hp751364 := nat_lit 584392852255118595194880000

noncomputable def hp751365 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 814678 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 814678 1000)) Bool.true 13016006086865015373005 18889465931478580854784

noncomputable def hp751366 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 814678 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751367 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp751366 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751368 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 814678 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751369 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp751367 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp751370 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 814678 1000)) hp751369 Bool.true 13016006086865015373005 18889465931478580854784

noncomputable def hp751371 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 814678 1000) 814678 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl

noncomputable def hp751372 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp751367 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp751373 := nat_lit 436744691153298251512450908160

noncomputable def hp751374 := @hp751372 27152513 33554432 197683 268435456 2269499841756553184051 18889465931478580854784 1770257007558140329351 hp751364 hp751373 13016006086865015373005 18889465931478580854784

noncomputable def hp751375 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) 11)

noncomputable def hp751376 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) 11) hp751375

noncomputable def hp751377 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) 11)

noncomputable def hp751378 := @hp751377 217220104 536870912 197683 536870912 217220104 536870912 197683 536870912 233238310678429696 27152513 33554432

noncomputable def hp751379 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp751380 := hp751379 BSN.quadSignNeg 9 10 11 814678 1000 192 241 536870912 268435456 9007199254740992

noncomputable def hp751381 := hp751380 Bool.false 845001688432 3712 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp751382 := hp751381 Bool.true 240321705 169704 Bool.true 179434765 Bool.true 543480452 28296951008113761 1 Bool.false 507163364

noncomputable def hp751383 := hp751382 Bool.false Bool.false 455298118 Bool.true Bool.true 217220104 197683 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 507163364 536870912) BSN.abs_quadSignNeg

noncomputable def hp751384 := hp751379 BSN.quadSignNeg 7 8 9 814678 1000 76 137 536870912 268435456 9007199254740992

noncomputable def hp751385 := hp751384 Bool.false 845001688432 3712 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp751386 := hp751385 Bool.true 238955045 138596 Bool.true 406120291 Bool.true 479484287 28296951008113761 1 Bool.false 390450980

noncomputable def hp751387 := hp751386 Bool.false Bool.false 418235798 Bool.true Bool.true 240321705 169704 BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 390450980 536870912) BSN.abs_quadSignNeg

noncomputable def hp751388 := hp751379 BSN.quadSignPos 5 6 7 814678 1000 72 7 536870912 268435456 9007199254740992

noncomputable def hp751389 := hp751388 Bool.false 845001688432 3712 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp751390 := hp751389 Bool.true 402463700 102992 Bool.false 608785184 Bool.true 191284269 28296951008113761 1 Bool.false 227141150

noncomputable def hp751391 := hp751390 Bool.false Bool.false 187262753 Bool.false Bool.true 238955045 138596 BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 227141150 536870912) BSN.abs_quadSignPos

noncomputable def hp751392 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp751393 := hp751392 BSN.quadSignPos 3 4 5 814678 1000 283 167 536870912 268435456 9007199254740992

noncomputable def hp751394 := hp751393 Bool.false 845001688432 3712 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp751395 := hp751394 Bool.true 510311371 60872 Bool.false 10436348 Bool.false 237121874 28296951008113761 1 Bool.false 10435690

noncomputable def hp751396 := hp751395 Bool.false Bool.false 229487263 Bool.false Bool.true 402463700 102992 BSN.abs_quadSignPos (BSN.cos_quad_nat3 283 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 10435690 536870912) BSN.abs_quadSignPos

noncomputable def hp751397 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp751398 := hp751397 BSN.quadSignPos 1 2 3 814678 1000 642 432 536870912 268435456 9007199254740992

noncomputable def hp751399 := hp751398 Bool.false 845001688432 3712 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp751400 := hp751399 Bool.true 536870872 3762 Bool.false 426983213 Bool.false 182014748 28296951008113761 1 Bool.false 375840546

noncomputable def hp751401 := hp751400 Bool.true Bool.false 506311185 Bool.false Bool.true 510311371 60872 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 642 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 375840546 536870912) BSN.abs_quadSignPos

noncomputable def hp751402 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) 1) Bool.true

noncomputable def hp751403 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)))

noncomputable def hp751404 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000))) Bool.true 67108859 67108864

noncomputable def hp751405 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 52812605527) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 52812605527 33554432

noncomputable def hp751406 := nat_lit 582849502596954068639340788962997361338075371837948312361

noncomputable def hp751407 := nat_lit 370312803277973439803325373715083968925179007991808000

noncomputable def hp751408 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) Bool.false hp751406 hp751407 20557554630572588399

noncomputable def hp751409 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 814678 4000) (Real.log (Enclosure.sfrac Bool.false 2654801974736 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1629356))))))

noncomputable def hp751410 := nat_lit 172254903868405909582433469936640000

noncomputable def hp751411 := nat_lit 841993831449993740087223554189868011520

noncomputable def hp751412 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp751409 (Enclosure.sfrac Bool.false 814678 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 814678 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp751410 hp751411)) Bool.false

noncomputable def hp751413 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 814678 1000) 814678 1000 2654801974736 16000000 1629356

noncomputable def hp751414 := hp751413 4000 2000 hp751410 hp751411 (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl rfl rfl rfl

noncomputable def hp751415 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp751409 (Enclosure.sfrac Bool.false 814678 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 814678 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp751410 hp751411) 14176777689883573338989 9007199254740992000

noncomputable def hp751416 := nat_lit 11936757813185619325733699357962185960203783615241181437153280

noncomputable def hp751417 := @hp751415 20557554630572588399 hp740893 hp751410 hp751411 0 1 hp751416 hp751406 hp751407 20557554630572588399 hp740893

noncomputable def hp751418 := @Enclosure.Real.IsNear.subLit_ff_p (hp751409 (Enclosure.sfrac Bool.false 814678 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 814678 2000) (Real.log Real.pi)) 18376772783269705794413 9007199254740992000 1713915013779719 726000000000000000000

noncomputable def hp751419 := nat_lit 475693722974315449520119349248000

noncomputable def hp751420 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 814678 4000) (Real.log (Enclosure.sfrac Bool.false 2654801974736 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1629356))))))

noncomputable def hp751421 := @hp751420 (Enclosure.sfrac Bool.false 814678 2000) 22045756320496646734701 9007199254740992000 1713915013779719 726000000000000000000 814678 2000 0

noncomputable def hp751422 := nat_lit 36753545566539411588826000

noncomputable def hp751423 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 814678 4000) (Real.log (Enclosure.sfrac Bool.false 2654801974736 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1629356))))) 22049292057399824602701

noncomputable def hp751424 := nat_lit 49642629975044727611434458592573390848

noncomputable def hp751425 := @hp751423 9007199254740992000 5091745041066907 2178000000000000000000 883934225794467 2251799813685248 200000001089 8712000000000000000 hp751424 22045756320496646734701 9007199254740992000 1713915013779719

noncomputable def hp751426 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 814678 4000) (Real.log (Enclosure.sfrac Bool.false 2654801974736 16000000)) 814678 4000 0 1 54130078527712359 4503599627370496

noncomputable def hp751427 := nat_lit 116243458503218205800005632

noncomputable def hp751428 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2654801974736) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp751427 hp617687

noncomputable def hp751429 := BSN.log_rat_reduce_isNear 2654801974736 16000000 17 5309603949472 4194304000000 63294351 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp751430 := nat_lit 245702521509292590531390386593775082772158235592312092196427791169740307266243207002914597369339099217920

noncomputable def hp751431 := nat_lit 1137303649791069467325668615598213346762303511795977913608814489979038723930585128516712441567892209664

noncomputable def hp751432 := nat_lit 981935121420214644924153764946655501866097133217452788029582657211536217453441700180939117690880

noncomputable def hp751433 := BSN.log_dyadic_bound 557649974736 4751953974736 5 4 hp751430 268435456 87120000 hp751431 hp751432 63294351 5309603949472

noncomputable def hp751434 := hp751433 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp751435 := @BSN.binarySplit_of_base4 (BSN.artanhP 557649974736) (BSN.artanhQ 4751953974736) 0 4 hp751431 hp751430 hp751432 rfl rfl rfl

noncomputable def hp751436 := hp751429 rfl rfl rfl rfl (hp751434 (hp751435 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp751437 := @hp751426 12500018513 1089000000000000000 22049292057399824602701 9007199254740992000 5091745041066907 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 814678 4000) (BSN.isNear_log_sfrac 2654801974736 16000000 54130078527712359 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp751428 1000001481040000 87120000000000000000000 54130078527712359 4503599627370496 12500018513 1089000000000000000 (hp751436 rfl rfl rfl) rfl)) rfl

noncomputable def hp751438 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1629356)))) 1 4

noncomputable def hp751439 := @hp751438 0 1 883934225794467 562949953421312 200000001089 2178000000000000000 883934225794467 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp751440 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1629356))) 884279719003555 562949953421312 1

noncomputable def hp751441 := @hp751440 2000000000000000 20593 33554432 1 10890000 29659910871893088927744 883934225794467 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp751442 := BSN.arctan_dyadic_bound_f 1000 1629356 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp751443 := hp751442 1 20593 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1629356) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1629356) 0 0 rfl)

noncomputable def hp751444 := hp751439 (hp751441 (hp751443 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp751445 := @hp751418 15646200974979 33554432000 1222017 268435456000 hp751419 14176777689883573338989 9007199254740992000 20557554630572588399 hp740893 (@hp751421 1 hp751422 18376772783269705794413 9007199254740992000 1713915013779719 726000000000000000000 (@hp751425 726000000000000000000 hp751437 hp751444 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 814678 2000) rfl rfl)

noncomputable def hp751446 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 814678 2000) (Real.log Real.pi) 814678 2000 0 1 38410761 33554432

noncomputable def hp751447 := hp751445 (@hp751446 3 268435456 15646200974979 33554432000 1222017 268435456000 (Enclosure.Real.IsNear.const Bool.false 814678 2000) hd4909 rfl) rfl

noncomputable def hp751448 := @hp751408 hp740893 52812605527 33554432 29 4194304 (@hp751412 hp751406 hp751407 20557554630572588399 hp740893 (hp751414 rfl rfl rfl rfl rfl) (hp751417 (hp751447 rfl) (Enclosure.Real.IsNear.const Bool.true hp751410 hp751411) rfl rfl)) rfl

noncomputable def hp751449 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 52812605527) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1821132368101637095424) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp751450 := BSN.sin_reduce_arg_pos_rat_q2 52812605527 33554432 226375608064910080 72057594037927936 250 1821132368101637095424 hp619237 rfl rfl rfl rfl

noncomputable def hp751451 := BSN.cos_dyadic_bound_f 51759695 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp751452 := hp751451 1 67108859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 51759695) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp751453 := hp751452 (@BSN.binarySplit_of_le (BSN.cosOddP 51759695) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp751454 := @BSN.cos_arg_round Bool.false 67108859 67108864 1821132368101637095424 hp619237 51759695 137438953472 21801270 21780000 hp751453 rfl

noncomputable def hp751455 := hp751449 67108859 67108864 250 1000000000000000 21780000 10890000 hp751450 BSN.pi_near_15 hp751454 rfl rfl

noncomputable def hp751456 := @hp751405 29 4194304 Bool.true 67108859 67108864 1 10890000 hp751448 (Enclosure.sfrac_false_div 52812605527 33554432) (hp751455 rfl rfl) rfl

noncomputable def hp751457 := @hp751402 67108859 67108864 20000269 2854748160000 536870872 536870912 3762 536870912 (@hp751403 Bool.true 67108859 67108864 20000269 2854748160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000)) (@hp751404 320004304 45675970560000 67108859 67108864 20000269 2854748160000 (hp751456 rfl) rfl))

noncomputable def hp751458 := @hp751408 hp740893 845001688432 536870912 3712 536870912 (@hp751412 hp751406 hp751407 20557554630572588399 hp740893 (hp751414 rfl rfl rfl rfl rfl) (hp751417 (hp751447 rfl) (Enclosure.Real.IsNear.const Bool.true hp751410 hp751411) rfl rfl)) rfl

noncomputable def hp751459 := hp751401 (BSN.cos_quad_nat0 432 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 506311185 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl rfl (hp751457 rfl) hp751458

noncomputable def hp751460 := nat_lit 4640186094198435159744475113973212356114051036042726479353948922236583201

noncomputable def hp751461 := nat_lit 1104806974756973543809800296715492559842704314497696830194829251525921

noncomputable def hp751462 := nat_lit 13918348668645791532145805741326206083222467699499184044401457108206697761

noncomputable def hp751463 := BSN.cos_dyadic_bound_f 426983213 536870912 3 2 536870912 268435456 hp751460 hp708868 hp751461 hp751462 hp708870

noncomputable def hp751464 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 426983213) (BSN.cosEvenQ 536870912) 0 2 hp751460 hp708868 hp751461 rfl rfl rfl

noncomputable def hp751465 := hp751463 hp751461 375840546 rfl rfl rfl rfl rfl rfl rfl rfl (hp751464 rfl)

noncomputable def hp751466 := @BSN.binarySplit_of_base2 (BSN.cosOddP 426983213) (BSN.cosOddQ 536870912) 0 2 hp751462 hp708870 hp751461 rfl rfl rfl

noncomputable def hp751467 := nat_lit 153185799970544402813009891978135245679851280006746432497823321581223936

noncomputable def hp751468 := nat_lit 1204627102077930020082040514546107682148175422817049554026988896256

noncomputable def hp751469 := nat_lit 459554990657429052578989511853376644824189543669393663394361910765879296

noncomputable def hp751470 := BSN.cos_dyadic_bound_f 182014748 536870912 3 2 536870912 268435456 hp751467 hp708868 hp751468 hp751469 hp708870

noncomputable def hp751471 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 182014748) (BSN.cosEvenQ 536870912) 0 2 hp751467 hp708868 hp751468 rfl rfl rfl

noncomputable def hp751472 := hp751470 hp751468 506311185 rfl rfl rfl rfl rfl rfl rfl rfl (hp751471 rfl)

noncomputable def hp751473 := @BSN.binarySplit_of_base2 (BSN.cosOddP 182014748) (BSN.cosOddQ 536870912) 0 2 hp751469 hp708870 hp751468 rfl rfl rfl

noncomputable def hp751474 := hp751459 hd4911 hd4913 hd4915 hd4917 hd4918 (hp751465 (hp751466 rfl) rfl rfl rfl rfl) (hp751472 (hp751473 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751475 := hp751396 (BSN.cos_quad_nat3 167 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 229487263 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl rfl (hp751474 rfl rfl rfl rfl rfl) hp751458

noncomputable def hp751476 := BSN.sin_dyadic_bound_f 10436348 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp751477 := hp751476 1 10435690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 10436348) (BSN.sinEvenQ 536870912) 0 0 rfl)

noncomputable def hp751478 := hp751477 (@BSN.binarySplit_of_le (BSN.sinOddP 10436348) (BSN.sinOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp751479 := nat_lit 794242684571457538980286277753736667403784644437622311832051189291434240

noncomputable def hp751480 := nat_lit 9994773317348603856714479748384687988768126821124782320855749509376

noncomputable def hp751481 := nat_lit 2080143229958922609113553189721146267991263682274157567055424110264074496

noncomputable def hp751482 := BSN.sin_dyadic_bound_f 237121874 536870912 3 2 536870912 268435456 hp751479 hp708845 hp751480 hp751481 hp708848

noncomputable def hp751483 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 237121874) (BSN.sinEvenQ 536870912) 0 2 hp751479 hp708845 hp751480 rfl rfl rfl

noncomputable def hp751484 := hp751482 hp751480 229487263 rfl rfl rfl rfl rfl rfl rfl rfl (hp751483 rfl)

noncomputable def hp751485 := @BSN.binarySplit_of_base2 (BSN.sinOddP 237121874) (BSN.sinOddQ 536870912) 0 2 hp751481 hp708848 hp751480 rfl rfl rfl

noncomputable def hp751486 := hp751475 hd4920 hd4922 hd4924 hd4926 hd4918 hp751478 (hp751484 (hp751485 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp751487 := hp751391 (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 187262753 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl rfl (hp751486 rfl rfl rfl rfl) hp751458

noncomputable def hp751488 := nat_lit 18939490016178612195956801053514435852105521260374824542560135383747916699486465518557511146532087406701299367936

noncomputable def hp751489 := nat_lit 2591605504111305925031748453773448209843406095767067128508351873211978222276004914551817558710851528032256

noncomputable def hp751490 := nat_lit 114824247074468788165956498770505837082748895244316889271286918479903148603899065534493720384972842853278794383360

noncomputable def hp751491 := BSN.cos_dyadic_bound_f 608785184 536870912 4 3 536870912 268435456 hp751488 hp716712 hp751489 hp751490 hp716714

noncomputable def hp751492 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 608785184) (BSN.cosEvenQ 536870912) 0 3 hp751488 hp716712 hp751489 rfl rfl rfl

noncomputable def hp751493 := hp751491 hp751489 227141150 rfl rfl rfl rfl rfl rfl rfl rfl (hp751492 rfl)

noncomputable def hp751494 := @BSN.binarySplit_of_base3 (BSN.cosOddP 608785184) (BSN.cosOddQ 536870912) 0 3 hp751490 hp716714 hp751489 rfl rfl rfl

noncomputable def hp751495 := nat_lit 1338804065371002262565665771938321

noncomputable def hp751496 := BSN.sin_dyadic_bound_f 191284269 536870912 2 1 536870912 268435456 hp751495 hp708890 hp751495 hp751495 hp708891

noncomputable def hp751497 := @BSN.binarySplit_of_base (BSN.sinEvenP 191284269) (BSN.sinEvenQ 536870912) 0 1 hp751495 hp708890 hp751495 rfl rfl rfl

noncomputable def hp751498 := hp751496 hp751495 187262753 rfl rfl rfl rfl rfl rfl rfl rfl (hp751497 rfl)

noncomputable def hp751499 := @BSN.binarySplit_of_base (BSN.sinOddP 191284269) (BSN.sinOddQ 536870912) 0 1 hp751495 hp708891 hp751495 rfl rfl rfl

noncomputable def hp751500 := hp751487 hd4928 hd4930 hd4932 hd4934 hd4918 (hp751493 (hp751494 rfl) rfl rfl rfl rfl) (hp751498 (hp751499 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751501 := hp751387 (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 418235798 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl rfl (hp751500 rfl rfl rfl rfl rfl) hp751458

noncomputable def hp751502 := nat_lit 3797450948675385145735935553648905669994058207119331261352339757450826401

noncomputable def hp751503 := nat_lit 740009865499310037937362706797398843772425996396839311205601201001121

noncomputable def hp751504 := nat_lit 11390872826295156817131931935533122212294629769365200105434608069950476961

noncomputable def hp751505 := BSN.cos_dyadic_bound_f 406120291 536870912 3 2 536870912 268435456 hp751502 hp708868 hp751503 hp751504 hp708870

noncomputable def hp751506 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 406120291) (BSN.cosEvenQ 536870912) 0 2 hp751502 hp708868 hp751503 rfl rfl rfl

noncomputable def hp751507 := hp751505 hp751503 390450980 rfl rfl rfl rfl rfl rfl rfl rfl (hp751506 rfl)

noncomputable def hp751508 := @BSN.binarySplit_of_base2 (BSN.cosOddP 406120291) (BSN.cosOddQ 536870912) 0 2 hp751504 hp708870 hp751503 rfl rfl rfl

noncomputable def hp751509 := nat_lit 13281592961116223679981618594237853299015378131827738743087523375513089025

noncomputable def hp751510 := nat_lit 2793798225080628308459180075631835846859254668650321888892966772945921

noncomputable def hp751511 := nat_lit 34780601129606645763642924312405259477478694409132929520266258322997130241

noncomputable def hp751512 := BSN.sin_dyadic_bound_f 479484287 536870912 3 2 536870912 268435456 hp751509 hp708845 hp751510 hp751511 hp708848

noncomputable def hp751513 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 479484287) (BSN.sinEvenQ 536870912) 0 2 hp751509 hp708845 hp751510 rfl rfl rfl

noncomputable def hp751514 := hp751512 hp751510 418235798 rfl rfl rfl rfl rfl rfl rfl rfl (hp751513 rfl)

noncomputable def hp751515 := @BSN.binarySplit_of_base2 (BSN.sinOddP 479484287) (BSN.sinOddQ 536870912) 0 2 hp751511 hp708848 hp751510 rfl rfl rfl

noncomputable def hp751516 := hp751501 hd4936 hd4938 hd4940 hd4942 hd4918 (hp751507 (hp751508 rfl) rfl rfl rfl rfl) (hp751514 (hp751515 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751517 := hp751383 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 455298118 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl rfl (hp751516 rfl rfl rfl rfl rfl) hp751458

noncomputable def hp751518 := nat_lit 144683286541524216238197292196924029310064174810908632071797060942190625

noncomputable def hp751519 := nat_lit 1074614563408977148226403490697258970625370380543835495786625390625

noncomputable def hp751520 := nat_lit 434047710395445830760295423783790693412251273691964808544399609575790625

noncomputable def hp751521 := BSN.cos_dyadic_bound_f 179434765 536870912 3 2 536870912 268435456 hp751518 hp708868 hp751519 hp751520 hp708870

noncomputable def hp751522 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 179434765) (BSN.cosEvenQ 536870912) 0 2 hp751518 hp708868 hp751519 rfl rfl rfl

noncomputable def hp751523 := hp751521 hp751519 507163364 rfl rfl rfl rfl rfl rfl rfl rfl (hp751522 rfl)

noncomputable def hp751524 := @BSN.binarySplit_of_base2 (BSN.cosOddP 179434765) (BSN.cosOddQ 536870912) 0 2 hp751520 hp708870 hp751519 rfl rfl rfl

noncomputable def hp751525 := nat_lit 21925413330768538094781345923267520086241664016676829869417398450408980480

noncomputable def hp751526 := nat_lit 7611520534886469701869030116843255755361021973952798333010928226861056

noncomputable def hp751527 := nat_lit 57411378166384926440148118035987663526076630770005297508315930629180030976

noncomputable def hp751528 := BSN.sin_dyadic_bound_f 543480452 536870912 3 2 536870912 268435456 hp751525 hp708845 hp751526 hp751527 hp708848

noncomputable def hp751529 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 543480452) (BSN.sinEvenQ 536870912) 0 2 hp751525 hp708845 hp751526 rfl rfl rfl

noncomputable def hp751530 := hp751528 hp751526 455298118 rfl rfl rfl rfl rfl rfl rfl rfl (hp751529 rfl)

noncomputable def hp751531 := @BSN.binarySplit_of_base2 (BSN.sinOddP 543480452) (BSN.sinOddQ 536870912) 0 2 hp751527 hp708848 hp751526 rfl rfl rfl

noncomputable def hp751532 := hp751517 hd4944 hd4946 hd4961 hd4963 hd4918 (hp751523 (hp751524 rfl) rfl rfl rfl rfl) (hp751530 (hp751531 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751533 := @hp751378 197683 268435456 (hp751532 rfl rfl rfl rfl rfl) (hp751532 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp751534 := @hp751376 Bool.true 27152513 33554432 197683 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 814678 1000)) (Enclosure.sfrac Bool.false 814678 1000) 11) hp751533

noncomputable def hp751535 := @Enclosure.Real.IsNear.mulLit_tf hp751367 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1))) 2485927 8388608 1

noncomputable def hp751536 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp751366 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751537 := @hp751536 1 1 0 1 2485927 8388608 1 33554432 2485927 8388608 1

noncomputable def hp751538 := @Enclosure.Real.IsNear.of_eq (hp751366 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751539 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 814678 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751540 := @hp751538 (@Inv.inv Real Real.instInv (Real.sqrt hp751368)) Bool.false 2485927 8388608 1 33554432 (hp751539 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 814678 1000) 814678 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000))))

noncomputable def hp751541 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp751368)) Bool.false 19887416 67108864 2 67108864 2485927 8388608

noncomputable def hp751542 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp751368) Bool.false 226454739 67108864 7 67108864 226454739 67108864 7 67108864

noncomputable def hp751543 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 814678 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751544 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 814678 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751545 := @hp751544 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 814678 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4350668508673

noncomputable def hp751546 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 814678 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 814678 1000 0

noncomputable def hp751547 := @hp751546 1 10680707 67108864 1 67108864 4350668508673 33554432000 407339 33554432000 (Enclosure.Real.IsNear.const Bool.false 814678 1000) hd4949

noncomputable def hp751548 := @hp751545 33554432000 407339 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 814678 1000) 814678 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000))) (hp751547 rfl)

noncomputable def hp751549 := @hp751543 4350668508673 33554432000 407339 33554432000 382078783 382078820 33554432 hp751548 rfl rfl rfl

noncomputable def hp751550 := @Enclosure.Real.IsNear.recentre' hp751368 Bool.false 764157603 67108864 37 67108864 764157603 67108864 37 67108864 (hp751549 rfl rfl rfl)

noncomputable def hp751551 := @Enclosure.Real.IsNear.sqrt_image hp751368 764157603 67108864 37 67108864 113227366 113227373 33554432 (hp751550 rfl) rfl rfl

noncomputable def hp751552 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp751368) 226454739 67108864 7 67108864 9943707 9943709 33554432 (hp751542 (hp751551 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp751553 := @hp751537 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp751540 (@hp751541 1 33554432 (hp751552 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp751554 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751555 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp751556 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1))) (hp751554 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751555 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp751557 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 814678 1000) 814678 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl

noncomputable def hp751558 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751559 := @hp751558 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751555 (Enclosure.sfrac Bool.false 1 16)))) 88570547

noncomputable def hp751560 := @hp751559 67108864 419 67108864 10307479 33554432 142986527 22837985280000 912939053221013 2251799813685248 1418541909919837 139330113471774720000

noncomputable def hp751561 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751562 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751563 := @hp751561 (@Neg.neg Real Real.instNeg hp751562) Bool.true 88570547 67108864 419 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751564 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751565 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp751566 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp751567 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 10194507) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false

noncomputable def hp751568 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1))) Bool.false 22955989049024469151945

noncomputable def hp751569 := nat_lit 998484790357625234253096387

noncomputable def hp751570 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp751571 := @Enclosure.Real.IsNear.subLit_ff_p hp751368 (Enclosure.sfrac Bool.false 11 1) 764157603 67108864 37 67108864 11 1 0

noncomputable def hp751572 := @hp751570 500000000000000 25960099 67108864 37 67108864 22955989049024469151945 9444732965739290427392 hp751569 hp738031 hd4948 (@hp751571 1 25960099 25960099 67108864 37 67108864 (hp751550 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751573 := @hp751567 10194507 4194304 117 33554432 Bool.true 50847599 67108864 1 10890000 (@hp751568 9444732965739290427392 hp751569 hp738031 10194507 4194304 117 33554432 (hp751572 rfl) rfl) (Enclosure.sfrac_false_div 10194507 4194304)

noncomputable def hp751574 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 10194507) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 519695175236544609910784) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp751575 := BSN.sin_reduce_arg_pos_rat_q1 10194507 4194304 226375608064910080 72057594037927936 0 519695175236544609910784 604462909807314587353088 rfl rfl rfl rfl

noncomputable def hp751576 := nat_lit 210404526575306097922590419882118353907105691986170942645667681250492520072648658808246434625

noncomputable def hp751577 := nat_lit 38011143628762177359901359960989071278225116531851222580653057228131760894899691581668161

noncomputable def hp751578 := nat_lit 550997932512307498652963640346563611260350162156062804949713345944349148767869030711417961281

noncomputable def hp751579 := BSN.sin_dyadic_bound_f 118165002103 137438953472 3 2 67108864 21801270 hp751576 hp738039 hp751577 hp751578 hp738042

noncomputable def hp751580 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 118165002103) (BSN.sinEvenQ 137438953472) 0 2 hp751576 hp738039 hp751577 rfl rfl rfl

noncomputable def hp751581 := hp751579 hp751577 50847599 rfl rfl rfl rfl rfl rfl rfl rfl (hp751580 rfl)

noncomputable def hp751582 := @BSN.binarySplit_of_base2 (BSN.sinOddP 118165002103) (BSN.sinOddQ 137438953472) 0 2 hp751578 hp738042 hp751577 rfl rfl rfl

noncomputable def hp751583 := @BSN.sin_arg_round Bool.false 50847599 67108864 519695175236544609910784 604462909807314587353088 118165002103 137438953472 21801270 21780000 (hp751581 (hp751582 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751584 := hp751574 50847599 67108864 0 1000000000000000 21780000 10890000 hp751575 BSN.pi_near_15 hp751583 rfl rfl

noncomputable def hp751585 := @hp751565 50847599 67108864 81730277 22837985280000 (@hp751566 50847599 67108864 1307684432 365407764480000 50847599 67108864 81730277 22837985280000 (hp751573 (hp751584 rfl rfl) rfl rfl) rfl)

noncomputable def hp751586 := @hp751564 50847599 67108864 81730277 22837985280000 44285064 44285483 33554432 hp751585 rfl rfl rfl

noncomputable def hp751587 := @Enclosure.Real.IsNear.recentre' hp751562 Bool.false 88570547 67108864 419 67108864 88570547 67108864 419 67108864 (hp751586 rfl rfl rfl)

noncomputable def hp751588 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751555 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp751589 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751555 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 63184063)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp751590 := nat_lit 1193513212033112435911004480005

noncomputable def hp751591 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751555 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp751590

noncomputable def hp751592 := nat_lit 118848744946522902949690295627038593

noncomputable def hp751593 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751555 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp751594 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp751595 := @hp751594 (Enclosure.sfrac Bool.false 1 16) 1068226013127735 4503599627370496 4404076663 4503599627370496 1 16 0

noncomputable def hp751596 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)) 673926740089801

noncomputable def hp751597 := @hp751596 4503599627370496 1921048695 4503599627370496 25960099 67108864 37 67108864 71687434236251382743040 1068226013127735 4503599627370496 4404076663

noncomputable def hp751598 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)) 25960099 67108864 37

noncomputable def hp751599 := @hp751598 67108864 25960099 67108864 37 67108864 673926740089801 4503599627370496 1921048695 4503599627370496 (@hp751571 1 25960099 25960099 67108864 37 67108864 (hp751550 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751600 := hp751599 (@hp751571 1 25960099 25960099 67108864 37 67108864 (hp751550 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751601 := @hp751597 4503599627370496 (hp751600 rfl) (@hp751571 1 25960099 25960099 67108864 37 67108864 (hp751550 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751602 := @hp751593 500000000000000 1349700989838391 4503599627370496 4404076663 4503599627370496 hp751590 hp627574 hp751592 hp738055 hd4948 (@hp751595 1 21595215837414256 1349700989838391 4503599627370496 4404076663 4503599627370496 (hp751601 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp751603 := @hp751589 63184063 33554432 207 33554432 Bool.true 10307479 33554432 1 10890000 (@hp751591 hp627574 hp751592 hp738055 63184063 33554432 207 33554432 (hp751602 rfl) rfl) (Enclosure.sfrac_true_div 63184063 33554432)

noncomputable def hp751604 := nat_lit 514987315781120234080084845630492957431035982519368678021340773042430593750614643367899346700322561

noncomputable def hp751605 := nat_lit 4048466901870548867413011562559036975152659660920869655305309621345655439795858505092363175681

noncomputable def hp751606 := nat_lit 3108764268466114333259624548989258519279539130858985438036826753462039886653273188689608564616447745

noncomputable def hp751607 := BSN.cos_dyadic_bound_t 63184063 33554432 4 3 33554432 10890000 hp751604 hp681868 hp751605 hp751606 hp681871

noncomputable def hp751608 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 63184063) (BSN.cosEvenQ 33554432) 0 3 hp751604 hp681868 hp751605 rfl rfl rfl

noncomputable def hp751609 := hp751607 hp751605 10307479 rfl rfl rfl rfl rfl rfl rfl rfl (hp751608 rfl)

noncomputable def hp751610 := @BSN.binarySplit_of_base3 (BSN.cosOddP 63184063) (BSN.cosOddQ 33554432) 0 3 hp751606 hp681871 hp751605 rfl rfl rfl

noncomputable def hp751611 := hp751603 (BSN.cos_neg_of_bound 63184063 33554432 Bool.true 10307479 33554432 1 10890000 (hp751609 (hp751610 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp751612 := hp751560 (hp751563 (@Enclosure.Real.IsNear.neg hp751562 Bool.false 88570547 67108864 419 67108864 (hp751587 rfl))) (@hp751588 10307479 33554432 2287784432 365407764480000 10307479 33554432 142986527 22837985280000 (hp751611 rfl) rfl)

noncomputable def hp751613 := @hp751535 33554432 912939053221013 2251799813685248 1418541909919837 139330113471774720000 2269499841756553184051 18889465931478580854784 1770257007558140329351 hp751364 (hp751553 rfl) (@hp751556 Bool.false 912939053221013 2251799813685248 1418541909919837 139330113471774720000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751368 (Enclosure.sfrac Bool.false 11 1)) (hp751557 rfl (hp751371 rfl rfl))) (hp751612 rfl))

noncomputable def hp751614 := @hp751365 432132676092571296169351 hp751364 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 814678 1000))) (@hp751370 432132676092571296169351 hp751364 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 814678 1000) 11 (hp751371 rfl rfl)) (@hp751374 432132676092571296169351 hp751364 hp751534 (hp751613 rfl) rfl rfl))

theorem hd5016 : hp751363 hp751364 := hp751614

noncomputable def hp790762 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) Bool.false 556919581 10737418240 1213 10737418240

noncomputable def hp791847 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) 806921 1000 808215 1000

noncomputable def hp791848 := hp791847 (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl rfl rfl

noncomputable def hp791849 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848))

noncomputable def hp791850 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 806921 1000) 806921 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl rfl

noncomputable def hp791851 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848))

noncomputable def hp791852 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848)) 2227330288615246330305

noncomputable def hp791853 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 806921 1000))

noncomputable def hp791854 := @hp791852 295147905179352825856 209648501612658346520693 hp748549 (@hp791853 Bool.true 2227330288615246330305 295147905179352825856 209648501612658346520693 hp748549 (hd4340 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848) hd5010)

noncomputable def hp791855 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848)) 199211420697390054079

noncomputable def hp791856 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 808215 1000))

noncomputable def hp791857 := @hp791855 590295810358705651712 hp750075 hp740088 (@hp791856 Bool.false 199211420697390054079 590295810358705651712 hp750075 hp740088 (hd4359 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848) hd5011)

noncomputable def hp791858 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848) hp791850 (hp791851 (hp791854 rfl rfl rfl) (hp791857 rfl rfl rfl))

noncomputable def hp791859 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791860 := hp791859 (Enclosure.sfrac Bool.false 806921 1000) 749551 1000 806921 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791861 := hp791860 (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl rfl rfl rfl

noncomputable def hp791862 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791863 := @hp791862 Bool.true Bool.false 2227330288615246330305 295147905179352825856 209648501612658346520693 hp748549 556919581 10737418240 1213 10737418240 (@hp791853 Bool.true 2227330288615246330305 295147905179352825856 209648501612658346520693 hp748549 (hd4340 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848) hd5010)

noncomputable def hp791864 := hp791863 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791865 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791866 := hp791865 (Enclosure.sfrac Bool.false 808215 1000) 749551 1000 808215 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791867 := hp791866 (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl rfl rfl rfl

noncomputable def hp791868 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791869 := @hp791868 Bool.false Bool.false 199211420697390054079 590295810358705651712 hp750075 hp740088 556919581 10737418240 1213 10737418240 (@hp791856 Bool.false 199211420697390054079 590295810358705651712 hp750075 hp740088 (hd4359 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848) hd5011)

noncomputable def hp791870 := hp791869 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791872 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) 808215 1000 809508 1000

noncomputable def hp791873 := hp791872 (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl rfl rfl

noncomputable def hp791874 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873))

noncomputable def hp791875 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 808215 1000) 808215 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl rfl

noncomputable def hp791876 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873))

noncomputable def hp791877 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873)) 199211420697390054079

noncomputable def hp791878 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 808215 1000))

noncomputable def hp791879 := @hp791877 590295810358705651712 hp750075 hp740088 (@hp791878 Bool.false 199211420697390054079 590295810358705651712 hp750075 hp740088 (hd4340 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873) hd5011)

noncomputable def hp791880 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873)) 707811633556837451943

noncomputable def hp791881 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 809508 1000))

noncomputable def hp791882 := @hp791880 1180591620717411303424 788086617649611877048099 hp750331 (@hp791881 Bool.true 707811633556837451943 1180591620717411303424 788086617649611877048099 hp750331 (hd4359 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873) hd5012)

noncomputable def hp791883 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873) hp791875 (hp791876 (hp791879 rfl rfl rfl) (hp791882 rfl rfl rfl))

noncomputable def hp791884 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791885 := hp791884 (Enclosure.sfrac Bool.false 808215 1000) 749551 1000 808215 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791886 := hp791885 (@Eq.refl Real (Enclosure.sfrac Bool.false 808215 1000)) rfl rfl rfl rfl

noncomputable def hp791887 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791888 := @hp791887 Bool.false Bool.false 199211420697390054079 590295810358705651712 hp750075 hp740088 556919581 10737418240 1213 10737418240 (@hp791878 Bool.false 199211420697390054079 590295810358705651712 hp750075 hp740088 (hd4340 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873) hd5011)

noncomputable def hp791889 := hp791888 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791890 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791891 := hp791890 (Enclosure.sfrac Bool.false 809508 1000) 749551 1000 809508 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791892 := hp791891 (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl rfl rfl rfl

noncomputable def hp791893 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791894 := @hp791893 Bool.true Bool.false 707811633556837451943 1180591620717411303424 788086617649611877048099 hp750331 556919581 10737418240 1213 10737418240 (@hp791881 Bool.true 707811633556837451943 1180591620717411303424 788086617649611877048099 hp750331 (hd4359 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873) hd5012)

noncomputable def hp791895 := hp791894 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791897 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) 809508 1000 810801 1000

noncomputable def hp791898 := hp791897 (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl rfl rfl

noncomputable def hp791899 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898))

noncomputable def hp791900 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 809508 1000) 809508 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl rfl

noncomputable def hp791901 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898))

noncomputable def hp791902 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898)) 707811633556837451943

noncomputable def hp791903 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 809508 1000))

noncomputable def hp791904 := @hp791902 1180591620717411303424 788086617649611877048099 hp750331 (@hp791903 Bool.true 707811633556837451943 1180591620717411303424 788086617649611877048099 hp750331 (hd4340 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898) hd5012)

noncomputable def hp791905 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898)) 1168338317454464274863

noncomputable def hp791906 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 810801 1000))

noncomputable def hp791907 := @hp791905 1180591620717411303424 10521034204879085394819 hp741092 (@hp791906 Bool.false 1168338317454464274863 1180591620717411303424 10521034204879085394819 hp741092 (hd4359 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898) hd5013)

noncomputable def hp791908 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898) hp791900 (hp791901 (hp791904 rfl rfl rfl) (hp791907 rfl rfl rfl))

noncomputable def hp791909 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791910 := hp791909 (Enclosure.sfrac Bool.false 809508 1000) 749551 1000 809508 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791911 := hp791910 (@Eq.refl Real (Enclosure.sfrac Bool.false 809508 1000)) rfl rfl rfl rfl

noncomputable def hp791912 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791913 := @hp791912 Bool.true Bool.false 707811633556837451943 1180591620717411303424 788086617649611877048099 hp750331 556919581 10737418240 1213 10737418240 (@hp791903 Bool.true 707811633556837451943 1180591620717411303424 788086617649611877048099 hp750331 (hd4340 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898) hd5012)

noncomputable def hp791914 := hp791913 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791915 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791916 := hp791915 (Enclosure.sfrac Bool.false 810801 1000) 749551 1000 810801 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791917 := hp791916 (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl rfl rfl rfl

noncomputable def hp791918 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791919 := @hp791918 Bool.false Bool.false 1168338317454464274863 1180591620717411303424 10521034204879085394819 hp741092 556919581 10737418240 1213 10737418240 (@hp791906 Bool.false 1168338317454464274863 1180591620717411303424 10521034204879085394819 hp741092 (hd4359 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898) hd5013)

noncomputable def hp791920 := hp791919 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791922 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) 810801 1000 812094 1000

noncomputable def hp791923 := hp791922 (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl rfl rfl

noncomputable def hp791924 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923))

noncomputable def hp791925 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 810801 1000) 810801 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl rfl

noncomputable def hp791926 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923))

noncomputable def hp791927 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923)) 1168338317454464274863

noncomputable def hp791928 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 810801 1000))

noncomputable def hp791929 := @hp791927 1180591620717411303424 10521034204879085394819 hp741092 (@hp791928 Bool.false 1168338317454464274863 1180591620717411303424 10521034204879085394819 hp741092 (hd4340 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923) hd5013)

noncomputable def hp791930 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923)) 186741526178853892521597

noncomputable def hp791931 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 812094 1000))

noncomputable def hp791932 := @hp791930 75557863725914323419136 hp750852 hp741590 (@hp791931 Bool.true 186741526178853892521597 75557863725914323419136 hp750852 hp741590 (hd4359 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923) hd5014)

noncomputable def hp791933 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923) hp791925 (hp791926 (hp791929 rfl rfl rfl) (hp791932 rfl rfl rfl))

noncomputable def hp791934 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791935 := hp791934 (Enclosure.sfrac Bool.false 810801 1000) 749551 1000 810801 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791936 := hp791935 (@Eq.refl Real (Enclosure.sfrac Bool.false 810801 1000)) rfl rfl rfl rfl

noncomputable def hp791937 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791938 := @hp791937 Bool.false Bool.false 1168338317454464274863 1180591620717411303424 10521034204879085394819 hp741092 556919581 10737418240 1213 10737418240 (@hp791928 Bool.false 1168338317454464274863 1180591620717411303424 10521034204879085394819 hp741092 (hd4340 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923) hd5013)

noncomputable def hp791939 := hp791938 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791940 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791941 := hp791940 (Enclosure.sfrac Bool.false 812094 1000) 749551 1000 812094 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791942 := hp791941 (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl rfl rfl rfl

noncomputable def hp791943 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791944 := @hp791943 Bool.true Bool.false 186741526178853892521597 75557863725914323419136 hp750852 hp741590 556919581 10737418240 1213 10737418240 (@hp791931 Bool.true 186741526178853892521597 75557863725914323419136 hp750852 hp741590 (hd4359 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923) hd5014)

noncomputable def hp791945 := hp791944 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791947 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) 812094 1000 813386 1000

noncomputable def hp791948 := hp791947 (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl rfl rfl

noncomputable def hp791949 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948))

noncomputable def hp791950 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 812094 1000) 812094 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl rfl

noncomputable def hp791951 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948))

noncomputable def hp791952 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948)) 186741526178853892521597

noncomputable def hp791953 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 812094 1000))

noncomputable def hp791954 := @hp791952 75557863725914323419136 hp750852 hp741590 (@hp791953 Bool.true 186741526178853892521597 75557863725914323419136 hp750852 hp741590 (hd4340 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948) hd5014)

noncomputable def hp791955 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948)) 65765378703299323461187

noncomputable def hp791956 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 813386 1000))

noncomputable def hp791957 := @hp791955 37778931862957161709568 421977255240610470725531 hp751106 (@hp791956 Bool.false 65765378703299323461187 37778931862957161709568 421977255240610470725531 hp751106 (hd4359 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948) hd5015)

noncomputable def hp791958 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948) hp791950 (hp791951 (hp791954 rfl rfl rfl) (hp791957 rfl rfl rfl))

noncomputable def hp791959 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791960 := hp791959 (Enclosure.sfrac Bool.false 812094 1000) 749551 1000 812094 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791961 := hp791960 (@Eq.refl Real (Enclosure.sfrac Bool.false 812094 1000)) rfl rfl rfl rfl

noncomputable def hp791962 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791963 := @hp791962 Bool.true Bool.false 186741526178853892521597 75557863725914323419136 hp750852 hp741590 556919581 10737418240 1213 10737418240 (@hp791953 Bool.true 186741526178853892521597 75557863725914323419136 hp750852 hp741590 (hd4340 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948) hd5014)

noncomputable def hp791964 := hp791963 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791965 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791966 := hp791965 (Enclosure.sfrac Bool.false 813386 1000) 749551 1000 813386 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791967 := hp791966 (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl rfl rfl rfl

noncomputable def hp791968 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791969 := @hp791968 Bool.false Bool.false 65765378703299323461187 37778931862957161709568 421977255240610470725531 hp751106 556919581 10737418240 1213 10737418240 (@hp791956 Bool.false 65765378703299323461187 37778931862957161709568 421977255240610470725531 hp751106 (hd4359 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948) hd5015)

noncomputable def hp791970 := hp791969 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791972 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) 813386 1000 814678 1000

noncomputable def hp791973 := hp791972 (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl rfl rfl

noncomputable def hp791974 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973))

noncomputable def hp791975 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 813386 1000) 813386 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl rfl

noncomputable def hp791976 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973))

noncomputable def hp791977 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973)) 65765378703299323461187

noncomputable def hp791978 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 813386 1000))

noncomputable def hp791979 := @hp791977 37778931862957161709568 421977255240610470725531 hp751106 (@hp791978 Bool.false 65765378703299323461187 37778931862957161709568 421977255240610470725531 hp751106 (hd4340 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973) hd5015)

noncomputable def hp791980 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973)) 13016006086865015373005

noncomputable def hp791981 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 814678 1000))

noncomputable def hp791982 := @hp791980 18889465931478580854784 432132676092571296169351 hp751364 (@hp791981 Bool.true 13016006086865015373005 18889465931478580854784 432132676092571296169351 hp751364 (hd4359 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973) hd5016)

noncomputable def hp791983 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973) hp791975 (hp791976 (hp791979 rfl rfl rfl) (hp791982 rfl rfl rfl))

noncomputable def hp791984 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791985 := hp791984 (Enclosure.sfrac Bool.false 813386 1000) 749551 1000 813386 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791986 := hp791985 (@Eq.refl Real (Enclosure.sfrac Bool.false 813386 1000)) rfl rfl rfl rfl

noncomputable def hp791987 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791988 := @hp791987 Bool.false Bool.false 65765378703299323461187 37778931862957161709568 421977255240610470725531 hp751106 556919581 10737418240 1213 10737418240 (@hp791978 Bool.false 65765378703299323461187 37778931862957161709568 421977255240610470725531 hp751106 (hd4340 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973) hd5015)

noncomputable def hp791989 := hp791988 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791990 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791991 := hp791990 (Enclosure.sfrac Bool.false 814678 1000) 749551 1000 814678 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791992 := hp791991 (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl rfl rfl rfl

noncomputable def hp791993 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791994 := @hp791993 Bool.true Bool.false 13016006086865015373005 18889465931478580854784 432132676092571296169351 hp751364 556919581 10737418240 1213 10737418240 (@hp791981 Bool.true 13016006086865015373005 18889465931478580854784 432132676092571296169351 hp751364 (hd4359 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973) hd5016)

noncomputable def hp791995 := hp791994 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl
open Zeta.Certificates
noncomputable def certificatePairs : List (Σ' I : ZIntervalRS, I.Certified) := [(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 806921 1000) (Enclosure.sfrac Bool.false 808215 1000) hp791848) (hp791849 (hp791858 (hp791861 (hp791864 rfl rfl)) (hp791867 (hp791870 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 808215 1000) (Enclosure.sfrac Bool.false 809508 1000) hp791873) (hp791874 (hp791883 (hp791886 (hp791889 rfl rfl)) (hp791892 (hp791895 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 809508 1000) (Enclosure.sfrac Bool.false 810801 1000) hp791898) (hp791899 (hp791908 (hp791911 (hp791914 rfl rfl)) (hp791917 (hp791920 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 810801 1000) (Enclosure.sfrac Bool.false 812094 1000) hp791923) (hp791924 (hp791933 (hp791936 (hp791939 rfl rfl)) (hp791942 (hp791945 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 812094 1000) (Enclosure.sfrac Bool.false 813386 1000) hp791948) (hp791949 (hp791958 (hp791961 (hp791964 rfl rfl)) (hp791967 (hp791970 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 813386 1000) (Enclosure.sfrac Bool.false 814678 1000) hp791973) (hp791974 (hp791983 (hp791986 (hp791989 rfl rfl)) (hp791992 (hp791995 rfl rfl)))))]

theorem solution : Zeta.Certificates.BatchSpec 6 806921 1000 814678 1000 :=
  ⟨CertifiedZeroIntervals.ofCertifiedRS certificatePairs (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.singleton _)))))), rfl, rfl, rfl⟩
#print axioms solution
