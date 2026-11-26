-- Prove2me | solution 1 for RHHeight1000.rs_main_0523_0528
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:41:52.368509+00:00
-- url     : https://prove2.me/submissions/78603f62-4670-4764-a930-d9b9fc7ea5cd

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

noncomputable def hp630724 := nat_lit 988643523323402220304136834155207460536120982503085435781120

noncomputable def hp630727 := nat_lit 44488958549553099913686157536984335724125444212638844610150400

theorem hd4359 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 a b h))

noncomputable def hp631913 := nat_lit 1901475900342344102245054808064

noncomputable def hp631914 := nat_lit 28522138505135161533675822120960

noncomputable def hp642702 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800

noncomputable def hp642705 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000

noncomputable def hp645312 := nat_lit 57646075230342348800000000000000

noncomputable def hp664746 := nat_lit 7427640235712281649394745344

noncomputable def hp664747 := nat_lit 111414603535684224740921180160

noncomputable def hp681368 := @BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl

noncomputable def hp681432 := @BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl

noncomputable def hp682141 := nat_lit 158456325028528675187087900672

noncomputable def hp682143 := nat_lit 4835703278458516698824704000000000000000

noncomputable def hp682805 := nat_lit 144115188075855872000000000000000

noncomputable def hp684401 := nat_lit 64791741944522487909851911563195676133695224709322207119351480320

noncomputable def hp684404 := nat_lit 2915628387503511955943336020343805426016285111919499320370816614400

noncomputable def hp687514 := nat_lit 30423614405477505635920876929024

noncomputable def hp687515 := nat_lit 456354216082162584538813153935360

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

noncomputable def hp737908 := nat_lit 5947392000000000000000000

noncomputable def hp737934 := nat_lit 282877490902138091004622673603363019119652456796264491099280832830873987773707601701812303598028785564314492868916806270538811366318583631052800

noncomputable def hp737937 := nat_lit 9900712181574833185161793576117705669187835987869257188474829149080589572079766059563430625931007494751007250412088219468858397821150427086848000

noncomputable def hp738018 := @hp731908 1 10680707 67108864 1 67108864 8005734612557 67108864000 749551 67108864000 (Enclosure.Real.IsNear.const Bool.false 749551 1000) hd4949

noncomputable def hp738031 := nat_lit 288230376151711744000000000000000

noncomputable def hp738039 := nat_lit 46199975943266144436568348213124696692647303168343434164427665391357367878632476496239452487680

noncomputable def hp738042 := nat_lit 846999558959879314670419717240619439365200558086296293014507198841551744441595402431056628940800

noncomputable def hp738055 := nat_lit 19342813113834066795298816000000000000000

noncomputable def hp738066 := nat_lit 16586685937797756904922089360178093090225977525586485022553978961920

noncomputable def hp738069 := nat_lit 746400867200899060721494021208014189060168988651391826014929053286400

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

noncomputable def hp739631 := nat_lit 8921088000000000000000000

noncomputable def hp740060 := nat_lit 486777830487640090174734030864384

noncomputable def hp740061 := nat_lit 7301667457314601352621010462965760

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

noncomputable def hp740132 := nat_lit 1982464000000000000000000

noncomputable def hp740177 := nat_lit 21759806992472160846509436431027924547665573599712653161483140986990306751823661669370177199848368120331884066839754328502985489716814125465600

noncomputable def hp740180 := nat_lit 1980142436314966637032358715223541133837567197573851437694965829816117914415953211912686125186201498950201450082417643893771679564230085417369600

noncomputable def hp740893 := nat_lit 2973696000000000000000000

noncomputable def hp742826 := nat_lit 3868562622766813359059763200000000000000

noncomputable def hp746621 := nat_lit 5133330660362904937396483134791632965849700352038159351603073932373040875403608499582161387520

noncomputable def hp746624 := nat_lit 230999879716330722182841741065623483463236515841717170822138326956786839393162382481197262438400

noncomputable def hp754729 := nat_lit 2571328549922521818857472000

noncomputable def hp755229 := nat_lit 102853141996900872754298880000

noncomputable def hp756508 := nat_lit 259730156557830486753280000

noncomputable def hp758057 := nat_lit 1428515861068067677143040000

noncomputable def hp764965 := nat_lit 1285664274961260909428736000

noncomputable def hp769528 := nat_lit 3004067793907357885399040

noncomputable def hp769529 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 12) (@Nat.cast Real Real.instNatCast 1))) Bool.false hp769528 hp630689

noncomputable def hp769530 := BSN.log_rat_reduce_isNear 12 1 3 24 16 13605151 33554432 24973259072661432 36028797018963968 10890000 1000000000000000

noncomputable def hp769531 := BSN.log_dyadic_bound 4 20 6 5 106444800000000000 33554432 10890000 1454330814136320 990904320 13605151 24

noncomputable def hp769532 := hp769531 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp769533 := @BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 20) 0 5 1454330814136320 106444800000000000 990904320 rfl rfl rfl

noncomputable def hp769534 := hp769530 rfl rfl rfl rfl (hp769532 (hp769533 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

theorem hd5087 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 12 1)) Bool.false 11191024608564965 4503599627370496 100000003267 1089000000000000000 := BSN.isNear_log_sfrac 12 1 11191024608564965 4503599627370496 100000003267 1089000000000000000 Bool.false (@hp769529 1000000032670000 10890000000000000000000 11191024608564965 4503599627370496 100000003267 1089000000000000000 (hp769534 rfl rfl rfl) rfl)

noncomputable def hp769535 := @Enclosure.Real.IsNear.recentre' (Real.log (Enclosure.sfrac Bool.false 12 1)) Bool.false 11191024608564965 4503599627370496 100000003267 1089000000000000000 1334074092

theorem hd5088 : Enclosure.Real.IsNear (Real.log (Enclosure.sfrac Bool.false 12 1)) Bool.false 1334074092 536870912 51 536870912 := @hp769535 536870912 51 536870912 hd5087 rfl

noncomputable def hp769536 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12))) Bool.false 19372661 67108864 1 67108864

noncomputable def hp769537 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12))) Bool.false 19372661 67108864 1 67108864

noncomputable def hp769538 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) 232471925 67108864 1 67108864 9686330 9686331

noncomputable def hp769539 := @Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 12) (@Nat.cast Real Real.instNatCast 1))) Bool.false 232471925 67108864

noncomputable def hp769540 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 12) (@Nat.cast Real Real.instNatCast 1))) Bool.false 232471925 67108864

noncomputable def hp769541 := @hp769540 1 67108864 232471925 67108864 1 67108864 (BSN.sqrt_enclosure 12 1 116235962 116235963 33554432 rfl rfl rfl rfl rfl)

noncomputable def hp769542 := @hp769538 33554432 (@hp769539 1 67108864 (BSN.sqrt_natCast_div_one 12) (hp769541 rfl)) rfl rfl rfl rfl rfl rfl

theorem hd5089 : hp769536 := @hp769537 19372661 67108864 1 67108864 hp769542 rfl

noncomputable def hp769543 := Enclosure.Real.IsNear (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12))) Bool.false 154981288 536870912 8 536870912

theorem hd5090 : hp769543 := @hp769537 154981288 536870912 8 536870912 hd5089 rfl

noncomputable def hp769737 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (Enclosure.sfrac Bool.false 1 1) Bool.false 1

noncomputable def hp769801 := nat_lit 90074191459888009107287531

noncomputable def hp769802 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 906639 1000)) Bool.true 652345635981816454823077 151115727451828646838272 hp769801

noncomputable def hp769803 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 906639 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 906639 1000)) Bool.true 652345635981816454823077 151115727451828646838272

noncomputable def hp769804 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 906639 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769805 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp769804 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769806 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 906639 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769807 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp769805 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp769808 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 906639 1000)) hp769807 Bool.true 652345635981816454823077 151115727451828646838272

noncomputable def hp769809 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 906639 1000) 906639 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl

noncomputable def hp769810 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp769805 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp769811 := nat_lit 87556349132194453879368036909056

noncomputable def hp769812 := @hp769810 544755293 134217728 58633 67108864 39005702341090112814245 151115727451828646838272 211423484791770371927531 hp755229 hp769811 652345635981816454823077 151115727451828646838272

noncomputable def hp769813 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) 12)

noncomputable def hp769814 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) 12) hp769813

noncomputable def hp769815 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) 12)

noncomputable def hp769816 := @hp769815 1089510586 536870912 234532 536870912 1089510586 536870912 234532 536870912 1169853083878948864 544755293 134217728

noncomputable def hp769817 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) Real.cos BSN.quadSignPos 11

noncomputable def hp769818 := hp769817 12 906639 1000 288 536870912 268435456 9007199254740992 Bool.false 966438625677 4130 1334074092

noncomputable def hp769819 := hp769818 51 154981288 8 Bool.true 1232753367 219981 Bool.true 210296338 28296951008113761 1 Bool.false

noncomputable def hp769820 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp769821 := hp769820 BSN.quadSignNeg 9 10 11 906639 1000 183 238 536870912 268435456 9007199254740992

noncomputable def hp769822 := hp769821 Bool.false 966438625677 4130 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp769823 := hp769822 Bool.true 1075362684 188847 Bool.true 13687734 Bool.true 23420968 28296951008113761 1 Bool.false 13686251

noncomputable def hp769824 := hp769823 Bool.false Bool.false 536360123 Bool.true Bool.true 1232753367 219981 BSN.abs_quadSignPos (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 13686251 536870912) BSN.abs_quadSignNeg

noncomputable def hp769825 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp769826 := hp769825 BSN.quadSignNeg 7 8 9 906639 1000 54 122 536870912 268435456 9007199254740992

noncomputable def hp769827 := hp769826 Bool.false 966438625677 4130 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp769828 := hp769827 Bool.true 727034152 154230 Bool.true 186604807 Bool.true 171851694 28296951008113761 1 Bool.false 504766177

noncomputable def hp769829 := hp769828 Bool.true Bool.false 509600209 Bool.true Bool.true 1075362684 188847 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 54 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 504766177 536870912) BSN.abs_quadSignNeg

noncomputable def hp769830 := hp769820 BSN.quadSignNeg 5 6 7 906639 1000 111 22 536870912 268435456 9007199254740992

noncomputable def hp769831 := hp769830 Bool.false 966438625677 4130 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp769832 := hp769831 Bool.true 890846313 114610 Bool.false 695153786 Bool.false 717631763 28296951008113761 1 Bool.false 516556219

noncomputable def hp769833 := hp769832 Bool.false Bool.false 124538241 Bool.true Bool.true 727034152 154230 BSN.abs_quadSignPos (BSN.cos_quad_nat3 111 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 516556219 536870912) BSN.abs_quadSignNeg

noncomputable def hp769834 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp769835 := hp769834 BSN.quadSignNeg 3 4 5 906639 1000 345 217 536870912 268435456 9007199254740992

noncomputable def hp769836 := hp769835 Bool.false 966438625677 4130 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp769837 := hp769836 Bool.true 607949337 67739 Bool.false 718857103 Bool.false 48459320 28296951008113761 1 Bool.false 522509464

noncomputable def hp769838 := hp769837 Bool.true Bool.false 48393544 Bool.true Bool.true 890846313 114610 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 345 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 522509464 536870912) BSN.abs_quadSignNeg

noncomputable def hp769839 := hp769834 BSN.quadSignPos 1 2 3 906639 1000 745 511 536870912 268435456 9007199254740992

noncomputable def hp769840 := hp769839 Bool.false 966438625677 4130 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp769841 := hp769840 Bool.true 536870872 4186 Bool.false 780993278 Bool.false 757287241 28296951008113761 1 Bool.false 533257734

noncomputable def hp769842 := hp769841 Bool.true Bool.false 529993161 Bool.false Bool.true 607949337 67739 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 745 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533257734 536870912) BSN.abs_quadSignPos

noncomputable def hp769843 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) 1) Bool.true

noncomputable def hp769844 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)))

noncomputable def hp769845 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000))) Bool.true 67108859 67108864

noncomputable def hp769846 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 120804828209) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 120804828209 67108864

noncomputable def hp769847 := nat_lit 18010714724726767773505512784599413618019262185452043284377

noncomputable def hp769848 := nat_lit 10005217696317175078293851417021622343498574986215424000

noncomputable def hp769849 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) Bool.false hp769847 hp769848 1134068884067354257

noncomputable def hp769850 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 906639 4000) (Real.log (Enclosure.sfrac Bool.false 3287978105284 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1813278))))))

noncomputable def hp769851 := nat_lit 294044835298564973483540821055520000

noncomputable def hp769852 := nat_lit 1599555319608728888607712241899509583680

noncomputable def hp769853 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp769850 (Enclosure.sfrac Bool.false 906639 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 906639 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp769851 hp769852)) Bool.false

noncomputable def hp769854 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 906639 1000) 906639 1000 3287978105284 16000000 1813278

noncomputable def hp769855 := hp769854 4000 2000 hp769851 hp769852 (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl rfl rfl rfl

noncomputable def hp769856 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp769850 (Enclosure.sfrac Bool.false 906639 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 906639 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp769851 hp769852) 32428302459049801325257 18014398509481984000

noncomputable def hp769857 := nat_lit 51870858407213091187695876819646311219895475094101884659005760

noncomputable def hp769858 := @hp769856 1134068884067354257 147456000000000000000000 hp769851 hp769852 0 1 hp769857 hp769847 hp769848 1134068884067354257 147456000000000000000000

noncomputable def hp769859 := @Enclosure.Real.IsNear.subLit_ff_p (hp769850 (Enclosure.sfrac Bool.false 906639 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 906639 2000) (Real.log Real.pi)) 41776485057505902369481 18014398509481984000 94487638720267 36000000000000000000

noncomputable def hp769860 := nat_lit 2176226539475238686363691778048000

noncomputable def hp769861 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 906639 4000) (Real.log (Enclosure.sfrac Bool.false 3287978105284 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1813278))))))

noncomputable def hp769862 := @hp769861 (Enclosure.sfrac Bool.false 906639 2000) 49942763182625020615369 18014398509481984000 94487638720267 36000000000000000000 906639 2000 0

noncomputable def hp769863 := nat_lit 83552970115011804738962000

noncomputable def hp769864 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 906639 4000) (Real.log (Enclosure.sfrac Bool.false 3287978105284 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1813278))))) 49949834936812210143369

noncomputable def hp769865 := nat_lit 112461104829561484856176489252637376512

noncomputable def hp769866 := @hp769864 18014398509481984000 3777668094869269 1452000000000000000000 883969273398691 2251799813685248 200000001089 8712000000000000000 hp769865 49942763182625020615369 18014398509481984000 94487638720267

noncomputable def hp769867 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 906639 4000) (Real.log (Enclosure.sfrac Bool.false 3287978105284 16000000)) 906639 4000 0 1 55093410868948071 4503599627370496

noncomputable def hp769868 := nat_lit 118312198953611453433643008

noncomputable def hp769869 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3287978105284) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp769868 hp617687

noncomputable def hp769870 := BSN.log_rat_reduce_isNear 3287978105284 16000000 17 6575956210568 4194304000000 120713433 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp769871 := nat_lit 80375233994039497454447179820704066928986403564432254648071223395306792842517272509294879413101101940650374863974040495445928507267407934158338993863325122560

noncomputable def hp769872 := nat_lit 1349936302803015899482349908655091790053220409081885558170254410194303600741596553552014955351336540710364567238247398657606514941662603227618095975242924032

noncomputable def hp769873 := nat_lit 84528790308886092651490339351966148253377205600326764600125770559989063276525962725424958479250025395110074345645993955011951515573071027910077317120

noncomputable def hp769874 := BSN.log_dyadic_bound 1190826105284 5385130105284 7 6 hp769871 268435456 87120000 hp769872 hp769873 120713433 6575956210568

noncomputable def hp769875 := hp769874 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp769876 := @BSN.binarySplit_of_base6 (BSN.artanhP 1190826105284) (BSN.artanhQ 5385130105284) 0 6 hp769872 hp769871 hp769873 rfl rfl rfl

noncomputable def hp769877 := hp769870 rfl rfl rfl rfl (hp769875 (hp769876 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp769878 := @hp769867 12500018513 1089000000000000000 49949834936812210143369 18014398509481984000 3777668094869269 1452000000000000000000 (Enclosure.Real.IsNear.const Bool.false 906639 4000) (BSN.isNear_log_sfrac 3287978105284 16000000 55093410868948071 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp769869 1000001481040000 87120000000000000000000 55093410868948071 4503599627370496 12500018513 1089000000000000000 (hp769877 rfl rfl rfl) rfl)) rfl

noncomputable def hp769879 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1813278)))) 1 4

noncomputable def hp769880 := @hp769879 0 1 883969273398691 562949953421312 200000001089 2178000000000000000 883969273398691 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp769881 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1813278))) 884279719003555 562949953421312 1

noncomputable def hp769882 := @hp769881 2000000000000000 18504 33554432 1 10890000 29661086874345786048512 883969273398691 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp769883 := BSN.arctan_dyadic_bound_f 1000 1813278 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp769884 := hp769883 1 18504 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1813278) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1813278) 0 0 rfl)

noncomputable def hp769885 := hp769880 (hp769882 (hp769884 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp769886 := @hp769859 34824693942279 67108864000 2719917 536870912000 hp769860 32428302459049801325257 18014398509481984000 1134068884067354257 147456000000000000000000 (@hp769862 1 hp769863 41776485057505902369481 18014398509481984000 94487638720267 36000000000000000000 (@hp769866 36000000000000000000 hp769878 hp769885 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 906639 2000) rfl rfl)

noncomputable def hp769887 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 906639 2000) (Real.log Real.pi) 906639 2000 0 1 38410761 33554432

noncomputable def hp769888 := hp769886 (@hp769887 3 268435456 34824693942279 67108864000 2719917 536870912000 (Enclosure.Real.IsNear.const Bool.false 906639 2000) hd4909 rfl) rfl

noncomputable def hp769889 := @hp769849 147456000000000000000000 120804828209 67108864 517 67108864 (@hp769853 hp769847 hp769848 1134068884067354257 147456000000000000000000 (hp769855 rfl rfl rfl rfl rfl) (hp769858 (hp769888 rfl) (Enclosure.Real.IsNear.const Bool.true hp769851 hp769852) rfl rfl)) rfl

noncomputable def hp769890 := nat_lit 15188208557063855667150848

noncomputable def hp769891 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 120804828209) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp769890) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp769892 := BSN.sin_reduce_arg_pos_rat_q1 120804828209 67108864 226375608064910080 72057594037927936 286 hp769890 hp617687 rfl rfl rfl rfl

noncomputable def hp769893 := nat_lit 14366723687054118441442278564434093654404191851100207515702450400652233720578202893453704371929769796851465322916037036833784607170454257401856

noncomputable def hp769894 := nat_lit 10221650273798711458704065519836760276004540579511481257159197993589486427763289495459401802757375937307676225205090110504421505741357056

noncomputable def hp769895 := nat_lit 71744440780148679415191411595703276821879638552879637825556568090344739846968005966311552469279467863093336676462532118381141125144976887382016

noncomputable def hp769896 := BSN.sin_dyadic_bound_f 215837425188 137438953472 4 3 67108864 21801270 hp769893 hp737934 hp769894 hp769895 hp737937

noncomputable def hp769897 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215837425188) (BSN.sinEvenQ 137438953472) 0 3 hp769893 hp737934 hp769894 rfl rfl rfl

noncomputable def hp769898 := hp769896 hp769894 67108859 rfl rfl rfl rfl rfl rfl rfl rfl (hp769897 rfl)

noncomputable def hp769899 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215837425188) (BSN.sinOddQ 137438953472) 0 3 hp769895 hp737937 hp769894 rfl rfl rfl

noncomputable def hp769900 := @BSN.sin_arg_round Bool.false 67108859 67108864 hp769890 hp617687 215837425188 137438953472 21801270 21780000 (hp769898 (hp769899 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769901 := hp769891 67108859 67108864 286 1000000000000000 21780000 10890000 hp769892 BSN.pi_near_15 hp769900 rfl rfl

noncomputable def hp769902 := @hp769846 517 67108864 Bool.true 67108859 67108864 1 10890000 hp769889 (Enclosure.sfrac_false_div 120804828209 67108864) (hp769901 rfl rfl) rfl

noncomputable def hp769903 := @hp769843 67108859 67108864 356077429 45675970560000 536870872 536870912 4186 536870912 (@hp769844 Bool.true 67108859 67108864 356077429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000)) (@hp769845 5697238864 730815528960000 67108859 67108864 356077429 45675970560000 (hp769902 rfl) rfl))

noncomputable def hp769904 := @hp769849 147456000000000000000000 966438625677 536870912 4130 536870912 (@hp769853 hp769847 hp769848 1134068884067354257 147456000000000000000000 (hp769855 rfl rfl rfl rfl rfl) (hp769858 (hp769888 rfl) (Enclosure.Real.IsNear.const Bool.true hp769851 hp769852) rfl rfl)) rfl

noncomputable def hp769905 := hp769842 (BSN.cos_quad_nat3 511 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 529993161 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl rfl (hp769903 rfl) hp769904

noncomputable def hp769906 := nat_lit 133441246407325754547106711217186516286665958775479461058746325749093453687095257239068670219100723597281612271616

noncomputable def hp769907 := nat_lit 51495295081610546742567585905333477462684888767596545408615043382193814185872955481546583459370737147580416

noncomputable def hp769908 := nat_lit 666596122198443460046086113227424515028618107842519775578329326534377995001933516624626645278158513345767124504576

noncomputable def hp769909 := BSN.sin_dyadic_bound_f 780993278 536870912 4 3 536870912 268435456 hp769906 hp642702 hp769907 hp769908 hp642705

noncomputable def hp769910 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 780993278) (BSN.sinEvenQ 536870912) 0 3 hp769906 hp642702 hp769907 rfl rfl rfl

noncomputable def hp769911 := hp769909 hp769907 533257734 rfl rfl rfl rfl rfl rfl rfl rfl (hp769910 rfl)

noncomputable def hp769912 := @BSN.binarySplit_of_base3 (BSN.sinOddP 780993278) (BSN.sinOddQ 536870912) 0 3 hp769908 hp642705 hp769907 rfl rfl rfl

noncomputable def hp769913 := nat_lit 117942119636109449146447140248250976946156797041736387337605886047807604867972540369472746453806424335134849216481

noncomputable def hp769914 := nat_lit 35573588511705647637726471698976808321850821200119815074118175123035891207660862021504047293699086186688481

noncomputable def hp769915 := nat_lit 589233840420640505773706571889541456990251491350181411843468919339241689127707793042902776071364954915673842102241

noncomputable def hp769916 := BSN.sin_dyadic_bound_f 757287241 536870912 4 3 536870912 268435456 hp769913 hp642702 hp769914 hp769915 hp642705

noncomputable def hp769917 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 757287241) (BSN.sinEvenQ 536870912) 0 3 hp769913 hp642702 hp769914 rfl rfl rfl

noncomputable def hp769918 := hp769916 hp769914 529993161 rfl rfl rfl rfl rfl rfl rfl rfl (hp769917 rfl)

noncomputable def hp769919 := @BSN.binarySplit_of_base3 (BSN.sinOddP 757287241) (BSN.sinOddQ 536870912) 0 3 hp769915 hp642705 hp769914 rfl rfl rfl

noncomputable def hp769920 := hp769905 hd4911 hd4913 hd4915 hd4917 hd4918 (hp769911 (hp769912 rfl) rfl rfl rfl rfl) (hp769918 (hp769919 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769921 := hp769838 (BSN.cos_quad_nat1 217 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 48393544 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl rfl (hp769920 rfl rfl rfl rfl rfl) hp769904

noncomputable def hp769922 := nat_lit 95739203090264983244166382639356356691439831292331441900084879013984635347813808741155577882851274584591557343041

noncomputable def hp769923 := nat_lit 19041923677736038934753734264789891065744091330604313453249148224745754629684899721259803602373616250795841

noncomputable def hp769924 := nat_lit 478381726710543857406440837362378219558989589924978677056219733091469480794075081138004264759657054052762337032001

noncomputable def hp769925 := BSN.sin_dyadic_bound_f 718857103 536870912 4 3 536870912 268435456 hp769922 hp642702 hp769923 hp769924 hp642705

noncomputable def hp769926 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 718857103) (BSN.sinEvenQ 536870912) 0 3 hp769922 hp642702 hp769923 rfl rfl rfl

noncomputable def hp769927 := hp769925 hp769923 522509464 rfl rfl rfl rfl rfl rfl rfl rfl (hp769926 rfl)

noncomputable def hp769928 := @BSN.binarySplit_of_base3 (BSN.sinOddP 718857103) (BSN.sinOddQ 536870912) 0 3 hp769924 hp642705 hp769923 rfl rfl rfl

noncomputable def hp769929 := nat_lit 5514539636523179297754933760000

noncomputable def hp769930 := BSN.sin_dyadic_bound_f 48459320 536870912 2 1 536870912 268435456 hp769929 hp708890 hp769929 hp769929 hp708891

noncomputable def hp769931 := @BSN.binarySplit_of_base (BSN.sinEvenP 48459320) (BSN.sinEvenQ 536870912) 0 1 hp769929 hp708890 hp769929 rfl rfl rfl

noncomputable def hp769932 := hp769930 hp769929 48393544 rfl rfl rfl rfl rfl rfl rfl rfl (hp769931 rfl)

noncomputable def hp769933 := @BSN.binarySplit_of_base (BSN.sinOddP 48459320) (BSN.sinOddQ 536870912) 0 1 hp769929 hp708891 hp769929 rfl rfl rfl

noncomputable def hp769934 := hp769921 hd4920 hd4922 hd4924 hd4926 hd4918 (hp769927 (hp769928 rfl) rfl rfl rfl rfl) (hp769932 (hp769933 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769935 := hp769833 (BSN.cos_quad_nat2 22 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124538241 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl rfl (hp769934 rfl rfl rfl rfl rfl) hp769904

noncomputable def hp769936 := nat_lit 83711514887798322005221512405428855762779589085099333207074827887591183849791288824557818285736215386569636253696

noncomputable def hp769937 := nat_lit 12734171916386692831069550697395503569580870123962529915294438439531362827479844016188500766256413027536896

noncomputable def hp769938 := nat_lit 418317236570739427584011063440358036973778152797399585575783104152858263990032424843545005556362914453589978976256

noncomputable def hp769939 := BSN.sin_dyadic_bound_f 695153786 536870912 4 3 536870912 268435456 hp769936 hp642702 hp769937 hp769938 hp642705

noncomputable def hp769940 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 695153786) (BSN.sinEvenQ 536870912) 0 3 hp769936 hp642702 hp769937 rfl rfl rfl

noncomputable def hp769941 := hp769939 hp769937 516556219 rfl rfl rfl rfl rfl rfl rfl rfl (hp769940 rfl)

noncomputable def hp769942 := @BSN.binarySplit_of_base3 (BSN.sinOddP 695153786) (BSN.sinOddQ 536870912) 0 3 hp769938 hp642705 hp769937 rfl rfl rfl

noncomputable def hp769943 := nat_lit 36602946496845495177308752852789836564194293171837735008330695468781753174807073926990746038911295112487296282161

noncomputable def hp769944 := nat_lit 18656055819857184031049625026648753747700864656343333534862038630297479625331649327296787809765898582994481

noncomputable def hp769945 := nat_lit 221776999685160910378036813402300656813416484076459947987471881876229368304377210436260438282358250941755847323185

noncomputable def hp769946 := BSN.cos_dyadic_bound_f 717631763 536870912 4 3 536870912 268435456 hp769943 hp716712 hp769944 hp769945 hp716714

noncomputable def hp769947 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 717631763) (BSN.cosEvenQ 536870912) 0 3 hp769943 hp716712 hp769944 rfl rfl rfl

noncomputable def hp769948 := hp769946 hp769944 124538241 rfl rfl rfl rfl rfl rfl rfl rfl (hp769947 rfl)

noncomputable def hp769949 := @BSN.binarySplit_of_base3 (BSN.cosOddP 717631763) (BSN.cosOddQ 536870912) 0 3 hp769945 hp716714 hp769944 rfl rfl rfl

noncomputable def hp769950 := hp769935 hd4928 hd4930 hd4932 hd4934 hd4918 (hp769941 (hp769942 rfl) rfl rfl rfl rfl) (hp769948 (hp769949 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769951 := hp769829 (BSN.cos_quad_nat2 122 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 509600209 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl rfl (hp769950 rfl rfl rfl rfl rfl) hp769904

noncomputable def hp769952 := nat_lit 169232535098848847299907104590574802628605338784333800188050315546316481

noncomputable def hp769953 := nat_lit 1470220983857613415906855347725854337379532517221520327109927096001

noncomputable def hp769954 := nat_lit 507694664854578826672889500061028956177141257287966957523496726784757441

noncomputable def hp769955 := BSN.cos_dyadic_bound_f 186604807 536870912 3 2 536870912 268435456 hp769952 hp708868 hp769953 hp769954 hp708870

noncomputable def hp769956 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 186604807) (BSN.cosEvenQ 536870912) 0 2 hp769952 hp708868 hp769953 rfl rfl rfl

noncomputable def hp769957 := hp769955 hp769953 504766177 rfl rfl rfl rfl rfl rfl rfl rfl (hp769956 rfl)

noncomputable def hp769958 := @BSN.binarySplit_of_base2 (BSN.cosOddP 186604807) (BSN.cosOddQ 536870912) 0 2 hp769954 hp708870 hp769953 rfl rfl rfl

noncomputable def hp769959 := nat_lit 121732562094326812374702932425668915999902612669269681915113645021348096

noncomputable def hp769960 := nat_lit 760729993877571642633259492144205547682172171069074798638977270016

noncomputable def hp769961 := nat_lit 365196164822992681980823530758022459588612473663466907595743657109504256

noncomputable def hp769962 := BSN.cos_dyadic_bound_f 171851694 536870912 3 2 536870912 268435456 hp769959 hp708868 hp769960 hp769961 hp708870

noncomputable def hp769963 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 171851694) (BSN.cosEvenQ 536870912) 0 2 hp769959 hp708868 hp769960 rfl rfl rfl

noncomputable def hp769964 := hp769962 hp769960 509600209 rfl rfl rfl rfl rfl rfl rfl rfl (hp769963 rfl)

noncomputable def hp769965 := @BSN.binarySplit_of_base2 (BSN.cosOddP 171851694) (BSN.cosOddQ 536870912) 0 2 hp769961 hp708870 hp769960 rfl rfl rfl

noncomputable def hp769966 := hp769951 hd4936 hd4938 hd4940 hd4942 hd4918 (hp769957 (hp769958 rfl) rfl rfl rfl rfl) (hp769964 (hp769965 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp769967 := hp769824 (BSN.cos_quad_nat2 238 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536360123 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl rfl (hp769966 rfl rfl rfl rfl rfl) hp769904

noncomputable def hp769968 := BSN.sin_dyadic_bound_f 13687734 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp769969 := hp769968 1 13686251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 13687734) (BSN.sinEvenQ 536870912) 0 0 rfl)

noncomputable def hp769970 := hp769969 (@BSN.binarySplit_of_le (BSN.sinOddP 13687734) (BSN.sinOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp769971 := nat_lit 300898042778954652594867736576

noncomputable def hp769972 := BSN.cos_dyadic_bound_f 23420968 536870912 2 1 536870912 268435456 hp769971 hp708767 hp769971 hp769971 hp708768

noncomputable def hp769973 := @BSN.binarySplit_of_base (BSN.cosEvenP 23420968) (BSN.cosEvenQ 536870912) 0 1 hp769971 hp708767 hp769971 rfl rfl rfl

noncomputable def hp769974 := hp769972 hp769971 536360123 rfl rfl rfl rfl rfl rfl rfl rfl (hp769973 rfl)

noncomputable def hp769975 := @BSN.binarySplit_of_base (BSN.cosOddP 23420968) (BSN.cosOddQ 536870912) 0 1 hp769971 hp708768 hp769971 rfl rfl rfl

noncomputable def hp769976 := hp769967 hd4944 hd4946 hd4961 hd4963 hd4918 hp769970 (hp769974 (hp769975 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp769977 := hp769819 496207534 Bool.false Bool.true 1089510586 234532 BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 496207534 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl (hp769976 rfl rfl rfl rfl)

noncomputable def hp769978 := nat_lit 272974264932774450154794372341161871571825151839980263020530179450552576

noncomputable def hp769979 := nat_lit 3825195896773581819883955690212459878639620559684556808953179095296

noncomputable def hp769980 := nat_lit 818915144406529803300743349112105189795718176278821419947972631993467136

noncomputable def hp769981 := BSN.cos_dyadic_bound_f 210296338 536870912 3 2 536870912 268435456 hp769978 hp708868 hp769979 hp769980 hp708870

noncomputable def hp769982 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 210296338) (BSN.cosEvenQ 536870912) 0 2 hp769978 hp708868 hp769979 rfl rfl rfl

noncomputable def hp769983 := hp769981 hp769979 496207534 rfl rfl rfl rfl rfl rfl rfl rfl (hp769982 rfl)

noncomputable def hp769984 := @BSN.binarySplit_of_base2 (BSN.cosOddP 210296338) (BSN.cosOddQ 536870912) 0 2 hp769980 hp708870 hp769979 rfl rfl rfl

noncomputable def hp769985 := hp769977 hp769904 hd5088 hd5090 hd4918 (hp769983 (hp769984 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp769986 := @hp769814 Bool.true 544755293 134217728 58633 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 906639 1000)) (Enclosure.sfrac Bool.false 906639 1000) 12) (@hp769816 58633 67108864 (hp769985 rfl rfl rfl) (hp769985 rfl rfl rfl) rfl rfl)

noncomputable def hp769987 := @Enclosure.Real.IsNear.mulLit_ff hp769805 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1))) 19362715 67108864 1

noncomputable def hp769988 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp769804 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769989 := @hp769988 1 1 0 1 19362715 67108864 1 67108864 19362715 67108864 1

noncomputable def hp769990 := @Enclosure.Real.IsNear.of_eq (hp769804 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp769991 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 906639 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769992 := @hp769990 (@Inv.inv Real Real.instInv (Real.sqrt hp769806)) Bool.false 19362715 67108864 1 67108864 (hp769991 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 906639 1000) 906639 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000))))

noncomputable def hp769993 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp769806)) Bool.false 19362715 67108864 1 67108864 19362715 67108864

noncomputable def hp769994 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp769806) Bool.false 232591326 67108864 6 67108864 116295663 33554432 3 33554432

noncomputable def hp769995 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 906639 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769996 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 906639 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp769997 := @hp769996 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 906639 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9683545513773

noncomputable def hp769998 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 906639 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 906639 1000 0

noncomputable def hp769999 := @hp769998 1 10680707 67108864 1 67108864 9683545513773 67108864000 906639 67108864000 (Enclosure.Real.IsNear.const Bool.false 906639 1000) hd4949

noncomputable def hp770000 := @hp769997 67108864000 906639 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 906639 1000) 906639 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000))) (hp769999 rfl)

noncomputable def hp770001 := @hp769995 9683545513773 67108864000 906639 67108864000 403066892 403066930 33554432 hp770000 rfl rfl rfl

noncomputable def hp770002 := @Enclosure.Real.IsNear.recentre' hp769806 Bool.false 806133822 67108864 38 67108864 403066911 33554432 19 33554432 (hp770001 rfl rfl rfl)

noncomputable def hp770003 := @Enclosure.Real.IsNear.sqrt_image hp769806 403066911 33554432 19 33554432 116295660 116295666 33554432 (hp770002 rfl) rfl rfl

noncomputable def hp770004 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp769806) 116295663 33554432 3 33554432 9681357 9681358 33554432 (hp769994 (hp770003 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp770005 := @hp769989 67108864 (@hp769737 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (hp769992 (@hp769993 1 67108864 (hp770004 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp770006 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770007 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp770008 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1))) (hp770006 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770007 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp770009 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 906639 1000) 906639 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl

noncomputable def hp770010 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770011 := @hp770010 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770007 (Enclosure.sfrac Bool.false 1 16)))) 67310759

noncomputable def hp770012 := @hp770011 67108864 249 67108864 29927977 33554432 85814027 22837985280000 2014474847204543 2251799813685248 10848291264969841 1532631248189521920000

noncomputable def hp770013 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770014 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)))) 33453787

noncomputable def hp770015 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)))) Bool.false

noncomputable def hp770016 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2599523) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp770017 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1))) Bool.false 365850395304183799485

noncomputable def hp770018 := nat_lit 512735432775390751517154757

noncomputable def hp770019 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)) 884279719003555 140737488355328 1

noncomputable def hp770020 := @Enclosure.Real.IsNear.subLit_ff_p hp769806 (Enclosure.sfrac Bool.false 12 1) 403066911 33554432 19 33554432 12 1 0

noncomputable def hp770021 := @hp770019 500000000000000 413727 33554432 19 33554432 365850395304183799485 4722366482869645213696 hp770018 hp682805 hd4948 (@hp770020 1 413727 413727 33554432 19 33554432 (hp770002 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770022 := @hp770016 2599523 33554432 15 4194304 Bool.false 33453787 33554432 1 10890000 (@hp770017 4722366482869645213696 hp770018 hp682805 2599523 33554432 15 4194304 (hp770021 rfl) rfl) (Enclosure.sfrac_false_div 2599523 33554432)

noncomputable def hp770023 := nat_lit 45664074219447565906245841

noncomputable def hp770024 := BSN.cos_dyadic_bound_f 2599523 33554432 2 1 33554432 10890000 hp770023 hp687514 hp770023 hp770023 hp687515

noncomputable def hp770025 := @BSN.binarySplit_of_base (BSN.cosEvenP 2599523) (BSN.cosEvenQ 33554432) 0 1 hp770023 hp687514 hp770023 rfl rfl rfl

noncomputable def hp770026 := hp770024 hp770023 33453787 rfl rfl rfl rfl rfl rfl rfl rfl (hp770025 rfl)

noncomputable def hp770027 := @BSN.binarySplit_of_base (BSN.cosOddP 2599523) (BSN.cosOddQ 33554432) 0 1 hp770023 hp687515 hp770023 rfl rfl rfl

noncomputable def hp770028 := hp770022 (hp770026 (hp770027 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp770029 := @hp770014 33554432 10471519 2854748160000 33655255 33655504 33554432 (@hp770015 33453787 33554432 167544304 45675970560000 33453787 33554432 10471519 2854748160000 hp770028 rfl)

noncomputable def hp770030 := @hp770013 Bool.false 67310759 67108864 249 67108864 67310759 67108864 249 67108864 (hp770029 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp770031 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770007 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp770032 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770007 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 31488531)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp770033 := nat_lit 74350193352967109446479132445

noncomputable def hp770034 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770007 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp770033

noncomputable def hp770035 := nat_lit 17628820940417422980725801543404373

noncomputable def hp770036 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770007 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp770037 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp770038 := @hp770037 (Enclosure.sfrac Bool.false 1 16) 13711204457535 1125899906842624 653256195 1125899906842624 1 16 0

noncomputable def hp770039 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)) 171170030529

noncomputable def hp770040 := @hp770039 1125899906842624 15721987 1125899906842624 413727 33554432 19 33554432 460071677608455045120 13711204457535 1125899906842624 653256195

noncomputable def hp770041 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)) 413727 33554432 19

noncomputable def hp770042 := @hp770041 33554432 413727 33554432 19 33554432 171170030529 1125899906842624 15721987 1125899906842624 (@hp770020 1 413727 413727 33554432 19 33554432 (hp770002 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770043 := hp770042 (@hp770020 1 413727 413727 33554432 19 33554432 (hp770002 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770044 := @hp770040 1125899906842624 (hp770043 rfl) (@hp770020 1 413727 413727 33554432 19 33554432 (hp770002 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770045 := @hp770036 500000000000000 84079948635199 1125899906842624 653256195 1125899906842624 hp770033 hp682141 hp770035 hp682143 hd4948 (@hp770038 1 1345279178163184 84079948635199 1125899906842624 653256195 1125899906842624 (hp770044 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp770046 := @hp770032 31488531 67108864 123 33554432 Bool.false 29927977 33554432 1 10890000 (@hp770034 hp682141 hp770035 hp682143 31488531 67108864 123 33554432 (hp770045 rfl) rfl) (Enclosure.sfrac_true_div 31488531 67108864)

noncomputable def hp770047 := nat_lit 33500474836302943593075204692161796327316178730904900041486469921

noncomputable def hp770048 := nat_lit 966538601585308489952018187267271820135268939334669107825441

noncomputable def hp770049 := nat_lit 100499491431705660162245710040110854438308265654836030786243758881

noncomputable def hp770050 := BSN.cos_dyadic_bound_f 31488531 67108864 3 2 33554432 10890000 hp770047 hp738066 hp770048 hp770049 hp738069

noncomputable def hp770051 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 31488531) (BSN.cosEvenQ 67108864) 0 2 hp770047 hp738066 hp770048 rfl rfl rfl

noncomputable def hp770052 := hp770050 hp770048 29927977 rfl rfl rfl rfl rfl rfl rfl rfl (hp770051 rfl)

noncomputable def hp770053 := @BSN.binarySplit_of_base2 (BSN.cosOddP 31488531) (BSN.cosOddQ 67108864) 0 2 hp770049 hp738069 hp770048 rfl rfl rfl

noncomputable def hp770054 := hp770046 (BSN.cos_neg_of_bound 31488531 67108864 Bool.false 29927977 33554432 1 10890000 (hp770052 (hp770053 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp770055 := hp770012 hp770030 (@hp770031 29927977 33554432 1373024432 365407764480000 29927977 33554432 85814027 22837985280000 (hp770054 rfl) rfl)

noncomputable def hp770056 := @hp769987 67108864 2014474847204543 2251799813685248 10848291264969841 1532631248189521920000 39005702341090112814245 151115727451828646838272 211423484791770371927531 hp755229 (hp770005 rfl) (@hp770008 Bool.false 2014474847204543 2251799813685248 10848291264969841 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp769806 (Enclosure.sfrac Bool.false 12 1)) (hp770009 rfl (hp769809 rfl rfl))) (hp770055 rfl))

noncomputable def hp770057 := @hp769803 hp769801 hp755229 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 906639 1000))) (@hp769808 hp769801 hp755229 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 906639 1000) 12 (hp769809 rfl rfl)) (@hp769812 hp769801 hp755229 hp769986 (hp770056 rfl) rfl rfl))

theorem hd5092 : hp769802 hp755229 := hp770057

noncomputable def hp770058 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 907903 1000)) Bool.false 26527206859214920030045 37778931862957161709568 227783628409128725737721

noncomputable def hp770059 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 907903 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 907903 1000)) Bool.false 26527206859214920030045 37778931862957161709568

noncomputable def hp770060 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 907903 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770061 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp770060 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp770062 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 907903 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770063 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp770061 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp770064 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 907903 1000)) hp770063 Bool.false 26527206859214920030045 37778931862957161709568

noncomputable def hp770065 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 907903 1000) 907903 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl

noncomputable def hp770066 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp770061 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp770067 := nat_lit 3560421434829842430134331637760

noncomputable def hp770068 := @hp770066 128123311 134217728 234863 268435456 9536299120602215671971 37778931862957161709568 537180906896600297721 hp756508 hp770067 26527206859214920030045 37778931862957161709568

noncomputable def hp770069 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) 12)

noncomputable def hp770070 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) 12) hp770069

noncomputable def hp770071 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) 12)

noncomputable def hp770072 := @hp770071 256246622 536870912 234863 536870912 256246622 536870912 234863 536870912 275142715300118528 128123311 134217728

noncomputable def hp770073 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) Real.cos BSN.quadSignPos 11

noncomputable def hp770074 := hp770073 12 907903 1000 288 536870912 268435456 9007199254740992 Bool.false 968125828861 4136 1334074092

noncomputable def hp770075 := hp770074 51 154981288 8 Bool.false 112901176 220292 Bool.true 209362806 28296951008113761 1 Bool.false

noncomputable def hp770076 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp770077 := hp770076 BSN.quadSignNeg 9 10 11 907903 1000 182 237 536870912 268435456 9007199254740992

noncomputable def hp770078 := hp770077 Bool.false 968125828861 4136 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp770079 := hp770078 Bool.false 309241154 189114 Bool.true 732344775 Bool.true 806755959 28296951008113761 1 Bool.false 110181586

noncomputable def hp770080 := hp770079 Bool.true Bool.false 535626630 Bool.true Bool.false 112901176 220292 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 110181586 536870912) BSN.abs_quadSignNeg

noncomputable def hp770081 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp770082 := hp770081 BSN.quadSignNeg 7 8 9 907903 1000 53 121 536870912 268435456 9007199254740992

noncomputable def hp770083 := hp770082 Bool.false 968125828861 4136 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp770084 := hp770083 Bool.false 675197077 154449 Bool.true 753835558 Bool.true 819010565 28296951008113761 1 Bool.false 529431481

noncomputable def hp770085 := hp770084 Bool.true Bool.false 536320875 Bool.true Bool.false 309241154 189114 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 529431481 536870912) BSN.abs_quadSignNeg

noncomputable def hp770086 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp770087 := hp770086 BSN.quadSignPos 5 6 7 907903 1000 112 23 536870912 268435456 9007199254740992

noncomputable def hp770088 := hp770087 Bool.false 968125828861 4136 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp770089 := hp770088 Bool.false 406472560 114773 Bool.false 323145488 Bool.false 241016079 28296951008113761 1 Bool.false 442520284

noncomputable def hp770090 := hp770089 Bool.false Bool.false 233001703 Bool.false Bool.false 675197077 154449 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 442520284 536870912) BSN.abs_quadSignPos

noncomputable def hp770091 := hp770076 BSN.quadSignNeg 3 4 5 907903 1000 346 217 536870912 268435456 9007199254740992

noncomputable def hp770092 := hp770091 Bool.false 968125828861 4136 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp770093 := hp770092 Bool.false 737678977 67836 Bool.false 621999395 Bool.false 643490178 28296951008113761 1 Bool.false 215100285

noncomputable def hp770094 := hp770093 Bool.true Bool.false 500110629 Bool.true Bool.false 406472560 114773 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 346 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 215100285 536870912) BSN.abs_quadSignNeg

noncomputable def hp770095 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp770096 := hp770095 BSN.quadSignNeg 1 2 3 907903 1000 747 513 536870912 268435456 9007199254740992

noncomputable def hp770097 := hp770096 Bool.false 968125828861 4136 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp770098 := hp770097 Bool.false 536870776 4194 Bool.false 311193741 Bool.false 12337110 28296951008113761 1 Bool.false 294058003

noncomputable def hp770099 := hp770098 Bool.false Bool.false 12336024 Bool.true Bool.false 737678977 67836 BSN.abs_quadSignPos (BSN.cos_quad_nat3 747 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 294058003 536870912) BSN.abs_quadSignNeg

noncomputable def hp770100 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) 1) Bool.false

noncomputable def hp770101 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)))

noncomputable def hp770102 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000))) Bool.false 67108847 67108864

noncomputable def hp770103 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 121015728607) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 121015728607 67108864

noncomputable def hp770104 := nat_lit 163742459712811509704419170652072247814074894381815625571793

noncomputable def hp770105 := nat_lit 90802828577032411019000881022191712487782120605876224000

noncomputable def hp770106 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) Bool.false hp770104 hp770105 15268119315628253841

noncomputable def hp770107 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 907903 4000) (Real.log (Enclosure.sfrac Bool.false 3297152429636 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1815806))))))

noncomputable def hp770108 := nat_lit 296100285952190133410193039876640000

noncomputable def hp770109 := nat_lit 1612982255797000359702779821841142515520

noncomputable def hp770110 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp770107 (Enclosure.sfrac Bool.false 907903 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 907903 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp770108 hp770109)) Bool.false

noncomputable def hp770111 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 907903 1000) 907903 1000 3297152429636 16000000 1815806

noncomputable def hp770112 := hp770111 4000 2000 hp770108 hp770109 (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl rfl rfl rfl

noncomputable def hp770113 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp770107 (Enclosure.sfrac Bool.false 907903 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 907903 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp770108 hp770109) 32484915598949192161113 18014398509481984000

noncomputable def hp770114 := nat_lit 52397587108099683105414134608663119300503966202181000182973760

noncomputable def hp770115 := @hp770113 15268119315628253841 hp740132 hp770108 hp770109 0 1 hp770114 hp770104 hp770105 15268119315628253841 hp740132

noncomputable def hp770116 := @Enclosure.Real.IsNear.subLit_ff_p (hp770107 (Enclosure.sfrac Bool.false 907903 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 907903 2000) (Real.log Real.pi)) 41846131061427741513561 18014398509481984000 1272089367616971 484000000000000000000

noncomputable def hp770117 := nat_lit 2180025782981359879649998405632000

noncomputable def hp770118 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 907903 4000) (Real.log (Enclosure.sfrac Bool.false 3297152429636 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1815806))))))

noncomputable def hp770119 := @hp770118 (Enclosure.sfrac Bool.false 907903 2000) 50023794286404852373337 18014398509481984000 1272089367616971 484000000000000000000 907903 2000 0

noncomputable def hp770120 := nat_lit 83692262122855483027122000

noncomputable def hp770121 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 907903 4000) (Real.log (Enclosure.sfrac Bool.false 3297152429636 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1815806))))) 50030866043947485101337

noncomputable def hp770122 := nat_lit 112643570653955620003743215065105432576

noncomputable def hp770123 := @hp770121 18014398509481984000 11348804308008239 4356000000000000000000 883969692829091 2251799813685248 200000001089 8712000000000000000 hp770122 50023794286404852373337 18014398509481984000 1272089367616971

noncomputable def hp770124 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 907903 4000) (Real.log (Enclosure.sfrac Bool.false 3297152429636 16000000)) 907903 4000 0 1 55105959605759079 4503599627370496

noncomputable def hp770125 := nat_lit 118339147160716148780040192

noncomputable def hp770126 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3297152429636) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp770125 hp617687

noncomputable def hp770127 := BSN.log_rat_reduce_isNear 3297152429636 16000000 17 6594304859272 4194304000000 121461396 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp770128 := nat_lit 82033884058743895991637682058385256386692155693977153699887959394651963261846850861129204348761609139814923350918381402866242357611926971652786394424630312960

noncomputable def hp770129 := nat_lit 1394862987826645218020890674251989163412887328886543083509276926055066249724386523188840084579756904636140703692862961101620169483121264150419063616057638912

noncomputable def hp770130 := nat_lit 92683262359355501201480516055491451543669309340999942696762252054180918945509315766366018851752917938381018779407006933502926164137265050433796177920

noncomputable def hp770131 := BSN.log_dyadic_bound 1200000429636 5394304429636 7 6 hp770128 268435456 87120000 hp770129 hp770130 121461396 6594304859272

noncomputable def hp770132 := hp770131 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp770133 := @BSN.binarySplit_of_base6 (BSN.artanhP 1200000429636) (BSN.artanhQ 5394304429636) 0 6 hp770129 hp770128 hp770130 rfl rfl rfl

noncomputable def hp770134 := hp770127 rfl rfl rfl rfl (hp770132 (hp770133 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp770135 := @hp770124 12500018513 1089000000000000000 50030866043947485101337 18014398509481984000 11348804308008239 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 907903 4000) (BSN.isNear_log_sfrac 3297152429636 16000000 55105959605759079 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp770126 1000001481040000 87120000000000000000000 55105959605759079 4503599627370496 12500018513 1089000000000000000 (hp770134 rfl rfl rfl) rfl)) rfl

noncomputable def hp770136 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1815806)))) 1 4

noncomputable def hp770137 := @hp770136 0 1 883969692829091 562949953421312 200000001089 2178000000000000000 883969692829091 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp770138 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1815806))) 884279719003555 562949953421312 1

noncomputable def hp770139 := @hp770138 2000000000000000 18479 33554432 1 10890000 29661100948094621581312 883969692829091 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp770140 := BSN.arctan_dyadic_bound_f 1000 1815806 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp770141 := hp770140 1 18479 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1815806) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1815806) 0 0 rfl)

noncomputable def hp770142 := hp770137 (hp770139 (hp770141 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp770143 := @hp770116 34873245144183 67108864000 2723709 536870912000 hp770117 32484915598949192161113 18014398509481984000 15268119315628253841 hp740132 (@hp770119 1 hp770120 41846131061427741513561 18014398509481984000 1272089367616971 484000000000000000000 (@hp770123 484000000000000000000 hp770135 hp770142 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 907903 2000) rfl rfl)

noncomputable def hp770144 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 907903 2000) (Real.log Real.pi) 907903 2000 0 1 38410761 33554432

noncomputable def hp770145 := hp770143 (@hp770144 3 268435456 34873245144183 67108864000 2723709 536870912000 (Enclosure.Real.IsNear.const Bool.false 907903 2000) hd4909 rfl) rfl

noncomputable def hp770146 := @hp770106 hp740132 121015728607 67108864 259 33554432 (@hp770110 hp770104 hp770105 15268119315628253841 hp740132 (hp770112 rfl rfl rfl rfl rfl) (hp770115 (hp770145 rfl) (Enclosure.Real.IsNear.const Bool.true hp770108 hp770109) rfl rfl)) rfl

noncomputable def hp770147 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 121015728607) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 6729396470652069740544) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp770148 := BSN.sin_reduce_arg_pos_rat_q0 121015728607 67108864 226375608064910080 72057594037927936 287 6729396470652069740544 hp617687 rfl rfl rfl rfl

noncomputable def hp770149 := BSN.cos_dyadic_bound_f 95630475 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp770150 := hp770149 1 67108847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 95630475) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp770151 := hp770150 (@BSN.binarySplit_of_le (BSN.cosOddP 95630475) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp770152 := @BSN.cos_arg_round Bool.false 67108847 67108864 6729396470652069740544 hp617687 95630475 137438953472 21801270 21780000 hp770151 rfl

noncomputable def hp770153 := hp770147 67108847 67108864 287 1000000000000000 21780000 10890000 hp770148 BSN.pi_near_15 hp770152 rfl rfl

noncomputable def hp770154 := @hp770103 259 33554432 Bool.false 67108847 67108864 1 10890000 hp770146 (Enclosure.sfrac_false_div 121015728607 67108864) (hp770153 rfl rfl) rfl

noncomputable def hp770155 := @hp770100 67108847 67108864 178379027 22837985280000 536870776 536870912 4194 536870912 (@hp770101 Bool.false 67108847 67108864 178379027 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000)) (@hp770102 2854064432 365407764480000 67108847 67108864 178379027 22837985280000 (hp770154 rfl) rfl))

noncomputable def hp770156 := @hp770106 hp740132 968125828861 536870912 4136 536870912 (@hp770110 hp770104 hp770105 15268119315628253841 hp740132 (hp770112 rfl rfl rfl rfl rfl) (hp770115 (hp770145 rfl) (Enclosure.Real.IsNear.const Bool.true hp770108 hp770109) rfl rfl)) rfl

noncomputable def hp770157 := hp770099 (BSN.cos_quad_nat1 513 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 12336024 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl rfl (hp770155 rfl) hp770156

noncomputable def hp770158 := nat_lit 2356139010327505714680209410782496329397833689376898746856761311477179425

noncomputable def hp770159 := nat_lit 87952224459223009477336530366860433412481321798990600084980975346721

noncomputable def hp770160 := nat_lit 6170697866303866701194728007190705945816420407180393590319951560861099041

noncomputable def hp770161 := BSN.sin_dyadic_bound_f 311193741 536870912 3 2 536870912 268435456 hp770158 hp708845 hp770159 hp770160 hp708848

noncomputable def hp770162 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 311193741) (BSN.sinEvenQ 536870912) 0 2 hp770158 hp708845 hp770159 rfl rfl rfl

noncomputable def hp770163 := hp770161 hp770159 294058003 rfl rfl rfl rfl rfl rfl rfl rfl (hp770162 rfl)

noncomputable def hp770164 := @BSN.binarySplit_of_base2 (BSN.sinOddP 311193741) (BSN.sinOddQ 536870912) 0 2 hp770160 hp708848 hp770159 rfl rfl rfl

noncomputable def hp770165 := BSN.sin_dyadic_bound_f 12337110 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp770166 := hp770165 1 12336024 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 12337110) (BSN.sinEvenQ 536870912) 0 0 rfl)

noncomputable def hp770167 := hp770166 (@BSN.binarySplit_of_le (BSN.sinOddP 12337110) (BSN.sinOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp770168 := hp770157 hd4911 hd4913 hd4915 hd4917 hd4918 (hp770163 (hp770164 rfl) rfl rfl rfl rfl) hp770167 rfl

noncomputable def hp770169 := hp770094 (BSN.cos_quad_nat1 217 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 500110629 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl rfl (hp770168 rfl rfl rfl rfl rfl) hp770156

noncomputable def hp770170 := nat_lit 20640021206605791011523251228066472234509340055165251631247873206128435602696083236446439797979227105323880640625

noncomputable def hp770171 := nat_lit 3353355116763929132537019738479164880553689554407326544303789115079359366492763344820167359841758056640625

noncomputable def hp770172 := nat_lit 125126683458835933652759048349558710925990602559597204580222750847803656344042871970138419189088483626353922240625

noncomputable def hp770173 := BSN.cos_dyadic_bound_f 621999395 536870912 4 3 536870912 268435456 hp770170 hp716712 hp770171 hp770172 hp716714

noncomputable def hp770174 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 621999395) (BSN.cosEvenQ 536870912) 0 3 hp770170 hp716712 hp770171 rfl rfl rfl

noncomputable def hp770175 := hp770173 hp770171 215100285 rfl rfl rfl rfl rfl rfl rfl rfl (hp770174 rfl)

noncomputable def hp770176 := @BSN.binarySplit_of_base3 (BSN.cosOddP 621999395) (BSN.cosOddQ 536870912) 0 3 hp770172 hp716714 hp770171 rfl rfl rfl

noncomputable def hp770177 := nat_lit 61450029676906943451454780870725928747130743485000256261778494946950359924911252350295599572363443933369068425216

noncomputable def hp770178 := nat_lit 5040841807298066190871064196978941920429951884986872205417931313019829601829795814886399130342973290582016

noncomputable def hp770179 := nat_lit 307120583896461037353314538458080702065236776680625955033641310733524911758070667689541131204990369441970341810176

noncomputable def hp770180 := BSN.sin_dyadic_bound_f 643490178 536870912 4 3 536870912 268435456 hp770177 hp642702 hp770178 hp770179 hp642705

noncomputable def hp770181 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 643490178) (BSN.sinEvenQ 536870912) 0 3 hp770177 hp642702 hp770178 rfl rfl rfl

noncomputable def hp770182 := hp770180 hp770178 500110629 rfl rfl rfl rfl rfl rfl rfl rfl (hp770181 rfl)

noncomputable def hp770183 := @BSN.binarySplit_of_base3 (BSN.sinOddP 643490178) (BSN.sinOddQ 536870912) 0 3 hp770179 hp642705 hp770178 rfl rfl rfl

noncomputable def hp770184 := hp770169 hd4920 hd4922 hd4924 hd4926 hd4918 (hp770175 (hp770176 rfl) rfl rfl rfl rfl) (hp770182 (hp770183 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770185 := hp770090 (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 233001703 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl rfl (hp770184 rfl rfl rfl rfl rfl) hp770156

noncomputable def hp770186 := nat_lit 1522001544540254402143553064932801255356401366647179818009437304285822976

noncomputable def hp770187 := nat_lit 118900798398720104355946265038973115056484388284100998592910061469696

noncomputable def hp770188 := nat_lit 4565766832023965766221947302268325819839091131164971252031126092734529536

noncomputable def hp770189 := BSN.cos_dyadic_bound_f 323145488 536870912 3 2 536870912 268435456 hp770186 hp708868 hp770187 hp770188 hp708870

noncomputable def hp770190 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 323145488) (BSN.cosEvenQ 536870912) 0 2 hp770186 hp708868 hp770187 rfl rfl rfl

noncomputable def hp770191 := hp770189 hp770187 442520284 rfl rfl rfl rfl rfl rfl rfl rfl (hp770190 rfl)

noncomputable def hp770192 := @BSN.binarySplit_of_base2 (BSN.cosOddP 323145488) (BSN.cosOddQ 536870912) 0 2 hp770188 hp708870 hp770187 rfl rfl rfl

noncomputable def hp770193 := nat_lit 847717569351713236507744041951476425763968882762670420395046280962716545

noncomputable def hp770194 := nat_lit 11385920166632973339757605651336074849167581851636056003628118258561

noncomputable def hp770195 := nat_lit 2220194247288502975563446216606621809070162707341138928372543909377553281

noncomputable def hp770196 := BSN.sin_dyadic_bound_f 241016079 536870912 3 2 536870912 268435456 hp770193 hp708845 hp770194 hp770195 hp708848

noncomputable def hp770197 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 241016079) (BSN.sinEvenQ 536870912) 0 2 hp770193 hp708845 hp770194 rfl rfl rfl

noncomputable def hp770198 := hp770196 hp770194 233001703 rfl rfl rfl rfl rfl rfl rfl rfl (hp770197 rfl)

noncomputable def hp770199 := @BSN.binarySplit_of_base2 (BSN.sinOddP 241016079) (BSN.sinOddQ 536870912) 0 2 hp770195 hp708848 hp770194 rfl rfl rfl

noncomputable def hp770200 := hp770185 hd4928 hd4930 hd4932 hd4934 hd4918 (hp770191 (hp770192 rfl) rfl rfl rfl rfl) (hp770198 (hp770199 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770201 := hp770085 (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536320875 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl rfl (hp770200 rfl rfl rfl rfl rfl) hp770156

noncomputable def hp770202 := nat_lit 115803732981179588386483336617602156708547968681075921912903598322349758699563694062126179813272610720677292609536

noncomputable def hp770203 := nat_lit 33675916831488208667906693466914135232131283760599671048190249851413800619194247502076967968234183151783936

noncomputable def hp770204 := nat_lit 578559019146781549517558210478426685831852546082295669205892804913176114662574454628623599535729140396151319760896

noncomputable def hp770205 := BSN.sin_dyadic_bound_f 753835558 536870912 4 3 536870912 268435456 hp770202 hp642702 hp770203 hp770204 hp642705

noncomputable def hp770206 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 753835558) (BSN.sinEvenQ 536870912) 0 3 hp770202 hp642702 hp770203 rfl rfl rfl

noncomputable def hp770207 := hp770205 hp770203 529431481 rfl rfl rfl rfl rfl rfl rfl rfl (hp770206 rfl)

noncomputable def hp770208 := @BSN.binarySplit_of_base3 (BSN.sinOddP 753835558) (BSN.sinOddQ 536870912) 0 3 hp770204 hp642705 hp770203 rfl rfl rfl

noncomputable def hp770209 := nat_lit 161433422229929197363937191682058625716309924534362549693045064950666341463252216148994539979137110082055578540625

noncomputable def hp770210 := nat_lit 91090701961644445750522090680971650198169098747876278140173390144605387070011610872581307253905000244140625

noncomputable def hp770211 := nat_lit 806274676559792480338649719687041597794068594862642529215240220886239602599682038173756078286690663280772916140625

noncomputable def hp770212 := BSN.sin_dyadic_bound_f 819010565 536870912 4 3 536870912 268435456 hp770209 hp642702 hp770210 hp770211 hp642705

noncomputable def hp770213 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 819010565) (BSN.sinEvenQ 536870912) 0 3 hp770209 hp642702 hp770210 rfl rfl rfl

noncomputable def hp770214 := hp770212 hp770210 536320875 rfl rfl rfl rfl rfl rfl rfl rfl (hp770213 rfl)

noncomputable def hp770215 := @BSN.binarySplit_of_base3 (BSN.sinOddP 819010565) (BSN.sinOddQ 536870912) 0 3 hp770211 hp642705 hp770210 rfl rfl rfl

noncomputable def hp770216 := hp770201 hd4936 hd4938 hd4940 hd4942 hd4918 (hp770207 (hp770208 rfl) rfl rfl rfl rfl) (hp770214 (hp770215 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770217 := hp770080 (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535626630 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl rfl (hp770216 rfl rfl rfl rfl rfl) hp770156

noncomputable def hp770218 := nat_lit 39704659596054639739494669204564337959482454080604900810418067831740232124521327604176216417326193462828525390625

noncomputable def hp770219 := nat_lit 23800553037119231589805631046375080983400708343887754726229891772851300642413501892869834959506988525390625

noncomputable def hp770220 := nat_lit 240544536396029504070919567064487716806582204380152214069404399024697402303283471871600586207043698839084525390625

noncomputable def hp770221 := BSN.cos_dyadic_bound_f 732344775 536870912 4 3 536870912 268435456 hp770218 hp716712 hp770219 hp770220 hp716714

noncomputable def hp770222 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 732344775) (BSN.cosEvenQ 536870912) 0 3 hp770218 hp716712 hp770219 rfl rfl rfl

noncomputable def hp770223 := hp770221 hp770219 110181586 rfl rfl rfl rfl rfl rfl rfl rfl (hp770222 rfl)

noncomputable def hp770224 := @BSN.binarySplit_of_base3 (BSN.cosOddP 732344775) (BSN.cosOddQ 536870912) 0 3 hp770220 hp716714 hp770219 rfl rfl rfl

noncomputable def hp770225 := nat_lit 151970291775552483148446072804651235764170413241268634165023197565429080671842626954223664996158902912202657594081

noncomputable def hp770226 := nat_lit 76016204843152267654083868043260948780303746827256332756586703516417687606152774621274779044507428933434081

noncomputable def hp770227 := nat_lit 759060438919912350079540506282430685576002845566139436504416536033496910102985952605916763557051446272721516591841

noncomputable def hp770228 := BSN.sin_dyadic_bound_f 806755959 536870912 4 3 536870912 268435456 hp770225 hp642702 hp770226 hp770227 hp642705

noncomputable def hp770229 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 806755959) (BSN.sinEvenQ 536870912) 0 3 hp770225 hp642702 hp770226 rfl rfl rfl

noncomputable def hp770230 := hp770228 hp770226 535626630 rfl rfl rfl rfl rfl rfl rfl rfl (hp770229 rfl)

noncomputable def hp770231 := @BSN.binarySplit_of_base3 (BSN.sinOddP 806755959) (BSN.sinOddQ 536870912) 0 3 hp770227 hp642705 hp770226 rfl rfl rfl

noncomputable def hp770232 := hp770217 hd4944 hd4946 hd4961 hd4963 hd4918 (hp770223 (hp770224 rfl) rfl rfl rfl rfl) (hp770230 (hp770231 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770233 := hp770075 496563176 Bool.false Bool.false 256246622 234863 BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 496563176 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl (hp770232 rfl rfl rfl rfl rfl)

noncomputable def hp770234 := nat_lit 268159309438930633461630580460555228892466947439877948493277810662564096

noncomputable def hp770235 := nat_lit 3691443644723599313718094728632385234161705764788537143990605046016

noncomputable def hp770236 := nat_lit 804470545429502453186264305192208421906932518908104268405545450777600256

noncomputable def hp770237 := BSN.cos_dyadic_bound_f 209362806 536870912 3 2 536870912 268435456 hp770234 hp708868 hp770235 hp770236 hp708870

noncomputable def hp770238 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 209362806) (BSN.cosEvenQ 536870912) 0 2 hp770234 hp708868 hp770235 rfl rfl rfl

noncomputable def hp770239 := hp770237 hp770235 496563176 rfl rfl rfl rfl rfl rfl rfl rfl (hp770238 rfl)

noncomputable def hp770240 := @BSN.binarySplit_of_base2 (BSN.cosOddP 209362806) (BSN.cosOddQ 536870912) 0 2 hp770236 hp708870 hp770235 rfl rfl rfl

noncomputable def hp770241 := hp770233 hp770156 hd5088 hd5090 hd4918 (hp770239 (hp770240 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp770242 := @hp770070 Bool.false 128123311 134217728 234863 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 907903 1000)) (Enclosure.sfrac Bool.false 907903 1000) 12) (@hp770072 234863 268435456 (hp770241 rfl rfl rfl) (hp770241 rfl rfl rfl) rfl rfl)

noncomputable def hp770243 := @Enclosure.Real.IsNear.mulLit_ff hp770061 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1))) 4838993 16777216 1

noncomputable def hp770244 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp770060 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp770245 := @hp770244 1 1 0 1 4838993 16777216 1 33554432 4838993 16777216 1

noncomputable def hp770246 := @Enclosure.Real.IsNear.of_eq (hp770060 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp770247 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 907903 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770248 := @hp770246 (@Inv.inv Real Real.instInv (Real.sqrt hp770062)) Bool.false 4838993 16777216 1 33554432 (hp770247 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 907903 1000) 907903 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000))))

noncomputable def hp770249 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp770062)) Bool.false 19355972 67108864 2 67108864 4838993 16777216

noncomputable def hp770250 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp770062) Bool.false 232672351 67108864 7 67108864 232672351 67108864 7 67108864

noncomputable def hp770251 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 907903 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770252 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 907903 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770253 := @hp770252 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 907903 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9697045927421

noncomputable def hp770254 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 907903 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 907903 1000 0

noncomputable def hp770255 := @hp770254 1 10680707 67108864 1 67108864 9697045927421 67108864000 907903 67108864000 (Enclosure.Real.IsNear.const Bool.false 907903 1000) hd4949

noncomputable def hp770256 := @hp770253 67108864000 907903 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 907903 1000) 907903 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000))) (hp770255 rfl)

noncomputable def hp770257 := @hp770251 9697045927421 67108864000 907903 67108864000 403347764 403347802 33554432 hp770256 rfl rfl rfl

noncomputable def hp770258 := @Enclosure.Real.IsNear.recentre' hp770062 Bool.false 806695566 67108864 38 67108864 403347783 33554432 19 33554432 (hp770257 rfl rfl rfl)

noncomputable def hp770259 := @Enclosure.Real.IsNear.sqrt_image hp770062 403347783 33554432 19 33554432 116336172 116336179 33554432 (hp770258 rfl) rfl rfl

noncomputable def hp770260 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp770062) 232672351 67108864 7 67108864 9677985 9677987 33554432 (hp770250 (hp770259 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp770261 := @hp770245 33554432 (@hp769737 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (hp770248 (@hp770249 1 33554432 (hp770260 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp770262 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770263 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp770264 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1))) (hp770262 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770263 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp770265 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 907903 1000) 907903 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl

noncomputable def hp770266 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770267 := @hp770266 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770263 (Enclosure.sfrac Bool.false 1 16)))) 67680541

noncomputable def hp770268 := @hp770267 67108864 251 67108864 29117967 33554432 173669929 45675970560000 1970719759380147 2251799813685248 1205720184365001 170292360909946880000

noncomputable def hp770269 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770270 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)))) 1039719

noncomputable def hp770271 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)))) Bool.false

noncomputable def hp770272 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2182147) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false

noncomputable def hp770273 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1))) Bool.false 614219808540150299445

noncomputable def hp770274 := nat_lit 512735432777803423625878981

noncomputable def hp770275 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)) 884279719003555 140737488355328 1

noncomputable def hp770276 := @Enclosure.Real.IsNear.subLit_ff_p hp770062 (Enclosure.sfrac Bool.false 12 1) 403347783 33554432 19 33554432 12 1 0

noncomputable def hp770277 := @hp770275 500000000000000 694599 33554432 19 33554432 614219808540150299445 4722366482869645213696 hp770274 hp682805 hd4948 (@hp770276 1 694599 694599 33554432 19 33554432 (hp770258 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770278 := @hp770272 2182147 16777216 15 4194304 Bool.false 33271008 33554432 1 10890000 (@hp770273 4722366482869645213696 hp770274 hp682805 2182147 16777216 15 4194304 (hp770277 rfl) rfl) (Enclosure.sfrac_false_div 2182147 16777216)

noncomputable def hp770279 := nat_lit 22674410958972480255692881

noncomputable def hp770280 := BSN.cos_dyadic_bound_f 2182147 16777216 2 1 33554432 10890000 hp770279 hp631913 hp770279 hp770279 hp631914

noncomputable def hp770281 := @BSN.binarySplit_of_base (BSN.cosEvenP 2182147) (BSN.cosEvenQ 16777216) 0 1 hp770279 hp631913 hp770279 rfl rfl rfl

noncomputable def hp770282 := hp770280 hp770279 33271008 rfl rfl rfl rfl rfl rfl rfl rfl (hp770281 rfl)

noncomputable def hp770283 := @BSN.binarySplit_of_base (BSN.cosOddP 2182147) (BSN.cosOddQ 16777216) 0 1 hp770279 hp631914 hp770279 rfl rfl rfl

noncomputable def hp770284 := hp770278 (hp770282 (hp770283 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp770285 := @hp770270 1048576 10471519 2854748160000 33840145 33840396 33554432 (@hp770271 33271008 33554432 167544304 45675970560000 1039719 1048576 10471519 2854748160000 hp770284 rfl)

noncomputable def hp770286 := @hp770269 Bool.false 67680541 67108864 251 67108864 67680541 67108864 251 67108864 (hp770285 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp770287 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770263 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp770288 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770263 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 17450745)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp770289 := nat_lit 82408813661979081516630288205

noncomputable def hp770290 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770263 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp770289

noncomputable def hp770291 := nat_lit 17916846993442687522841911527846629

noncomputable def hp770292 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770263 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp770293 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp770294 := @hp770293 (Enclosure.sfrac Bool.false 1 16) 22824407141967 1125899906842624 663929331 1125899906842624 1 16 0

noncomputable def hp770295 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)) 482467770801

noncomputable def hp770296 := @hp770295 1125899906842624 26395123 1125899906842624 694599 33554432 19 33554432 765860017385446047744 22824407141967 1125899906842624 663929331

noncomputable def hp770297 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)) 694599 33554432 19

noncomputable def hp770298 := @hp770297 33554432 694599 33554432 19 33554432 482467770801 1125899906842624 26395123 1125899906842624 (@hp770276 1 694599 694599 33554432 19 33554432 (hp770258 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770299 := hp770298 (@hp770276 1 694599 694599 33554432 19 33554432 (hp770258 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770300 := @hp770296 1125899906842624 (hp770299 rfl) (@hp770276 1 694599 694599 33554432 19 33554432 (hp770258 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770301 := @hp770292 500000000000000 93193151319631 1125899906842624 663929331 1125899906842624 hp770289 hp682141 hp770291 hp682143 hd4948 (@hp770294 1 1491090421114096 93193151319631 1125899906842624 663929331 1125899906842624 (hp770300 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp770302 := @hp770288 17450745 33554432 249 67108864 Bool.false 29117967 33554432 1 10890000 (@hp770290 hp682141 hp770291 hp682143 17450745 33554432 249 67108864 (hp770301 rfl) rfl) (Enclosure.sfrac_true_div 17450745 33554432)

noncomputable def hp770303 := nat_lit 197507526035195049056257235573415416831886019277646078452690625

noncomputable def hp770304 := nat_lit 8600263929181960984989478663156738311344118217659687890625

noncomputable def hp770305 := nat_lit 592505377577726783246801727762919937019035369596502915982290625

noncomputable def hp770306 := BSN.cos_dyadic_bound_f 17450745 33554432 3 2 33554432 10890000 hp770303 hp684401 hp770304 hp770305 hp684404

noncomputable def hp770307 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 17450745) (BSN.cosEvenQ 33554432) 0 2 hp770303 hp684401 hp770304 rfl rfl rfl

noncomputable def hp770308 := hp770306 hp770304 29117967 rfl rfl rfl rfl rfl rfl rfl rfl (hp770307 rfl)

noncomputable def hp770309 := @BSN.binarySplit_of_base2 (BSN.cosOddP 17450745) (BSN.cosOddQ 33554432) 0 2 hp770305 hp684404 hp770304 rfl rfl rfl

noncomputable def hp770310 := hp770302 (BSN.cos_neg_of_bound 17450745 33554432 Bool.false 29117967 33554432 1 10890000 (hp770308 (hp770309 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp770311 := hp770268 hp770286 (@hp770287 29117967 33554432 2778718864 730815528960000 29117967 33554432 173669929 45675970560000 (hp770310 rfl) rfl)

noncomputable def hp770312 := @hp770243 33554432 1970719759380147 2251799813685248 1205720184365001 170292360909946880000 9536299120602215671971 37778931862957161709568 537180906896600297721 hp756508 (hp770261 rfl) (@hp770264 Bool.false 1970719759380147 2251799813685248 1205720184365001 170292360909946880000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770062 (Enclosure.sfrac Bool.false 12 1)) (hp770265 rfl (hp770065 rfl rfl))) (hp770311 rfl))

noncomputable def hp770313 := @hp770059 227783628409128725737721 hp756508 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 907903 1000))) (@hp770064 227783628409128725737721 hp756508 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 907903 1000) 12 (hp770065 rfl rfl)) (@hp770068 227783628409128725737721 hp756508 hp770242 (hp770312 rfl) rfl rfl))

theorem hd5093 : hp770058 hp756508 := hp770313

noncomputable def hp770314 := nat_lit 22582265709564408911737219

noncomputable def hp770315 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 909166 1000)) Bool.true 133258922115036277105549 37778931862957161709568 hp770314

noncomputable def hp770316 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 909166 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 909166 1000)) Bool.true 133258922115036277105549 37778931862957161709568

noncomputable def hp770317 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 909166 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770318 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp770317 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp770319 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 909166 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770320 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp770318 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp770321 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 909166 1000)) hp770320 Bool.true 133258922115036277105549 37778931862957161709568

noncomputable def hp770322 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 909166 1000) 909166 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl

noncomputable def hp770323 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp770318 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp770324 := nat_lit 17885709762009123750685202972672

noncomputable def hp770325 := @hp770323 440299279 134217728 235179 268435456 9325692812792648688525 37778931862957161709568 54597939691685435257219 hp740088 hp770324 133258922115036277105549 37778931862957161709568

noncomputable def hp770326 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) 12)

noncomputable def hp770327 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) 12) hp770326

noncomputable def hp770328 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) 12)

noncomputable def hp770329 := @hp770328 880598558 536870912 235179 536870912 880598558 536870912 235179 536870912 945535501878689792 440299279 134217728

noncomputable def hp770330 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) Real.cos BSN.quadSignPos 11

noncomputable def hp770331 := hp770330 12 909166 1000 288 536870912 268435456 9007199254740992 Bool.false 969812168649 4141 1334074092

noncomputable def hp770332 := hp770331 51 154981288 8 Bool.true 1024097615 220588 Bool.true 207958596 28296951008113761 1 Bool.false

noncomputable def hp770333 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp770334 := hp770333 BSN.quadSignNeg 9 10 11 909166 1000 182 237 536870912 268435456 9007199254740992

noncomputable def hp770335 := hp770334 Bool.false 969812168649 4141 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp770336 := hp770335 Bool.true 792608275 189368 Bool.true 607314164 Bool.true 746352129 28296951008113761 1 Bool.false 228473174

noncomputable def hp770337 := hp770336 Bool.true Bool.false 528138606 Bool.true Bool.true 1024097615 220588 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 228473174 536870912) BSN.abs_quadSignNeg

noncomputable def hp770338 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp770339 := hp770338 BSN.quadSignNeg 7 8 9 909166 1000 53 121 536870912 268435456 9007199254740992

noncomputable def hp770340 := hp770339 Bool.false 969812168649 4141 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp770341 := hp770340 Bool.true 481143388 154655 Bool.true 477498456 Bool.true 622538349 28296951008113761 1 Bool.false 416987838

noncomputable def hp770342 := hp770341 Bool.true Bool.false 492112264 Bool.true Bool.true 792608275 189368 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 416987838 536870912) BSN.abs_quadSignNeg

noncomputable def hp770343 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp770344 := hp770343 BSN.quadSignPos 5 6 7 909166 1000 112 23 536870912 268435456 9007199254740992

noncomputable def hp770345 := hp770344 Bool.false 969812168649 4141 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp770346 := hp770345 Bool.true 684743847 114925 Bool.false 794550593 Bool.false 607896557 28296951008113761 1 Bool.false 48697238

noncomputable def hp770347 := hp770346 Bool.false Bool.false 486077143 Bool.false Bool.true 481143388 154655 BSN.abs_quadSignPos (BSN.cos_quad_nat0 112 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 48697238 536870912) BSN.abs_quadSignPos

noncomputable def hp770348 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp770349 := hp770348 BSN.quadSignNeg 3 4 5 909166 1000 347 218 536870912 268435456 9007199254740992

noncomputable def hp770350 := hp770349 Bool.false 969812168649 4141 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp770351 := hp770350 Bool.true 729440382 67924 Bool.false 525022552 Bool.false 395206845 28296951008113761 1 Bool.false 445250106

noncomputable def hp770352 := hp770351 Bool.false Bool.false 397860237 Bool.true Bool.true 684743847 114925 BSN.abs_quadSignPos (BSN.cos_quad_nat3 347 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 445250106 536870912) BSN.abs_quadSignNeg

noncomputable def hp770353 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp770354 := hp770353 BSN.quadSignNeg 1 2 3 909166 1000 748 514 536870912 268435456 9007199254740992

noncomputable def hp770355 := hp770354 Bool.false 969812168649 4141 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp770356 := hp770355 Bool.true 536870904 4194 Bool.false 684217796 Bool.false 110428253 28296951008113761 1 Bool.false 156778660

noncomputable def hp770357 := hp770356 Bool.false Bool.false 525553976 Bool.true Bool.true 729440382 67924 BSN.abs_quadSignPos (BSN.cos_quad_nat0 748 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 156778660 536870912) BSN.abs_quadSignNeg

noncomputable def hp770358 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) 1) Bool.true

noncomputable def hp770359 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)))

noncomputable def hp770360 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000))) Bool.true 67108863 67108864

noncomputable def hp770361 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 121226521081) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 121226521081 67108864

noncomputable def hp770362 := nat_lit 1292199507106667057765436138088691661836139971630151246581

noncomputable def hp770363 := nat_lit 715338856628900063785722998454970998113783808786432000

noncomputable def hp770364 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) Bool.false hp770362 hp770363 22933943634692523403

noncomputable def hp770365 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 909166 4000) (Real.log (Enclosure.sfrac Bool.false 3306332262224 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1818332))))))

noncomputable def hp770366 := nat_lit 298165575304149073827151945876480000

noncomputable def hp770367 := nat_lit 1626492250190722333595028882098110894080

noncomputable def hp770368 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp770365 (Enclosure.sfrac Bool.false 909166 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 909166 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp770366 hp770367)) Bool.false

noncomputable def hp770369 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 909166 1000) 909166 1000 3306332262224 16000000 1818332

noncomputable def hp770370 := hp770369 4000 2000 hp770366 hp770367 (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl rfl rfl rfl

noncomputable def hp770371 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp770365 (Enclosure.sfrac Bool.false 909166 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 909166 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp770366 hp770367) 16270749884039160730561 9007199254740992000

noncomputable def hp770372 := nat_lit 26464245905544541343036132108056405234404146618985497529978880

noncomputable def hp770373 := @hp770371 22933943634692523403 hp740893 hp770366 hp770367 0 1 hp770372 hp770362 hp770363 22933943634692523403 hp740893

noncomputable def hp770374 := @Enclosure.Real.IsNear.subLit_ff_p (hp770365 (Enclosure.sfrac Bool.false 909166 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 909166 2000) (Real.log Real.pi)) 20957868891884587389889 9007199254740992000 1910765305322443 726000000000000000000

noncomputable def hp770375 := nat_lit 545955770572999904070679396352000

noncomputable def hp770376 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 909166 4000) (Real.log (Enclosure.sfrac Bool.false 3306332262224 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1818332))))))

noncomputable def hp770377 := @hp770376 (Enclosure.sfrac Bool.false 909166 2000) 1002095542028100470249 360287970189639680 1910765305322443 726000000000000000000 909166 2000 0

noncomputable def hp770378 := nat_lit 1676629511350766991191120

noncomputable def hp770379 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 909166 4000) (Real.log (Enclosure.sfrac Bool.false 3306332262224 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1818332))))) 1002236977248746343369

noncomputable def hp770380 := nat_lit 2256518554833694245635582054474186752

noncomputable def hp770381 := @hp770379 360287970189639680 5682295915695079 2178000000000000000000 883970129036707 2251799813685248 200000001089 8712000000000000000 hp770380 1002095542028100470249 360287970189639680 1910765305322443

noncomputable def hp770382 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 909166 4000) (Real.log (Enclosure.sfrac Bool.false 3306332262224 16000000)) 909166 4000 0 1 55118480962153575 4503599627370496

noncomputable def hp770383 := nat_lit 118366036568824109177241600

noncomputable def hp770384 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3306332262224) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp770383 hp617687

noncomputable def hp770385 := BSN.log_rat_reduce_isNear 3306332262224 16000000 17 6612664524448 4194304000000 122207727 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp770386 := nat_lit 83724880611942190990586771149503722589517266098419797512228361269386455317360470325307157700669881632871456915766294756352491889917153489791070413931686133760

noncomputable def hp770387 := nat_lit 1441104453880737094298506230167989283369417472378694548911302707858920877431246568277594705122843597092153354801702808726350671028566815440674029436164636672

noncomputable def hp770388 := nat_lit 101558689265872988107357032519181916288095003993954732129761818122213441407843743544428296684912014349607377484745951905210789091374707539072012779520

noncomputable def hp770389 := BSN.log_dyadic_bound 1209180262224 5403484262224 7 6 hp770386 268435456 87120000 hp770387 hp770388 122207727 6612664524448

noncomputable def hp770390 := hp770389 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp770391 := @BSN.binarySplit_of_base6 (BSN.artanhP 1209180262224) (BSN.artanhQ 5403484262224) 0 6 hp770387 hp770386 hp770388 rfl rfl rfl

noncomputable def hp770392 := hp770385 rfl rfl rfl rfl (hp770390 (hp770391 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp770393 := @hp770382 12500018513 1089000000000000000 1002236977248746343369 360287970189639680 5682295915695079 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 909166 4000) (BSN.isNear_log_sfrac 3306332262224 16000000 55118480962153575 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp770384 1000001481040000 87120000000000000000000 55118480962153575 4503599627370496 12500018513 1089000000000000000 (hp770392 rfl rfl rfl) rfl)) rfl

noncomputable def hp770394 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1818332)))) 1 4

noncomputable def hp770395 := @hp770394 0 1 883970129036707 562949953421312 200000001089 2178000000000000000 883970129036707 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp770396 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1818332))) 884279719003555 562949953421312 1

noncomputable def hp770397 := @hp770396 2000000000000000 18453 33554432 1 10890000 29661115584793410535424 883970129036707 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp770398 := BSN.arctan_dyadic_bound_f 1000 1818332 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp770399 := hp770398 1 18453 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1818332) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1818332) 0 0 rfl)

noncomputable def hp770400 := hp770395 (hp770397 (hp770399 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp770401 := @hp770374 17460878967663 33554432000 1363749 268435456000 hp770375 16270749884039160730561 9007199254740992000 22933943634692523403 hp740893 (@hp770377 1 hp770378 20957868891884587389889 9007199254740992000 1910765305322443 726000000000000000000 (@hp770381 726000000000000000000 hp770393 hp770400 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 909166 2000) rfl rfl)

noncomputable def hp770402 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 909166 2000) (Real.log Real.pi) 909166 2000 0 1 38410761 33554432

noncomputable def hp770403 := hp770401 (@hp770402 3 268435456 17460878967663 33554432000 1363749 268435456000 (Enclosure.Real.IsNear.const Bool.false 909166 2000) hd4909 rfl) rfl

noncomputable def hp770404 := @hp770364 hp740893 121226521081 67108864 259 33554432 (@hp770368 hp770362 hp770363 22933943634692523403 hp740893 (hp770370 rfl rfl rfl rfl rfl) (hp770373 (hp770403 rfl) (Enclosure.Real.IsNear.const Bool.true hp770366 hp770367) rfl rfl)) rfl

noncomputable def hp770405 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 121226521081) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1506642864903534149632) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp770406 := BSN.sin_reduce_arg_pos_rat_q2 121226521081 67108864 226375608064910080 72057594037927936 287 1506642864903534149632 hp617687 rfl rfl rfl rfl

noncomputable def hp770407 := BSN.cos_dyadic_bound_f 21410682 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp770408 := hp770407 1 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 21410682) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp770409 := hp770408 (@BSN.binarySplit_of_le (BSN.cosOddP 21410682) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp770410 := @BSN.cos_arg_round Bool.false 67108863 67108864 1506642864903534149632 hp617687 21410682 137438953472 21801270 21780000 hp770409 rfl

noncomputable def hp770411 := hp770405 67108863 67108864 287 1000000000000000 21780000 10890000 hp770406 BSN.pi_near_15 hp770410 rfl rfl

noncomputable def hp770412 := @hp770361 259 33554432 Bool.true 67108863 67108864 1 10890000 hp770404 (Enclosure.sfrac_false_div 121226521081 67108864) (hp770411 rfl rfl) rfl

noncomputable def hp770413 := @hp770358 67108863 67108864 178379027 22837985280000 536870904 536870912 4194 536870912 (@hp770359 Bool.true 67108863 67108864 178379027 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000)) (@hp770360 2854064432 365407764480000 67108863 67108864 178379027 22837985280000 (hp770412 rfl) rfl))

noncomputable def hp770414 := @hp770364 hp740893 969812168649 536870912 4141 536870912 (@hp770368 hp770362 hp770363 22933943634692523403 hp740893 (hp770370 rfl rfl rfl rfl rfl) (hp770373 (hp770403 rfl) (Enclosure.Real.IsNear.const Bool.true hp770366 hp770367) rfl rfl)) rfl

noncomputable def hp770415 := hp770357 (BSN.cos_quad_nat2 514 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 525553976 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl rfl (hp770413 rfl) hp770414

noncomputable def hp770416 := nat_lit 30237353522875333445210801312795762954351496723521868731103422403653605750379900218419327039426431791405723549696

noncomputable def hp770417 := nat_lit 10527673030032216791047114027435833067714793679201208689557209676855122557428047382761540322621113621282816

noncomputable def hp770418 := nat_lit 183248152683434716651168087732552950522540858036356298527201858866036384738058061502476077107193172296125099540480

noncomputable def hp770419 := BSN.cos_dyadic_bound_f 684217796 536870912 4 3 536870912 268435456 hp770416 hp716712 hp770417 hp770418 hp716714

noncomputable def hp770420 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 684217796) (BSN.cosEvenQ 536870912) 0 3 hp770416 hp716712 hp770417 rfl rfl rfl

noncomputable def hp770421 := hp770419 hp770417 156778660 rfl rfl rfl rfl rfl rfl rfl rfl (hp770420 rfl)

noncomputable def hp770422 := @BSN.binarySplit_of_base3 (BSN.cosOddP 684217796) (BSN.cosOddQ 536870912) 0 3 hp770418 hp716714 hp770417 rfl rfl rfl

noncomputable def hp770423 := nat_lit 148703368449942823511422515376081

noncomputable def hp770424 := BSN.cos_dyadic_bound_f 110428253 536870912 2 1 536870912 268435456 hp770423 hp708767 hp770423 hp770423 hp708768

noncomputable def hp770425 := @BSN.binarySplit_of_base (BSN.cosEvenP 110428253) (BSN.cosEvenQ 536870912) 0 1 hp770423 hp708767 hp770423 rfl rfl rfl

noncomputable def hp770426 := hp770424 hp770423 525553976 rfl rfl rfl rfl rfl rfl rfl rfl (hp770425 rfl)

noncomputable def hp770427 := @BSN.binarySplit_of_base (BSN.cosOddP 110428253) (BSN.cosOddQ 536870912) 0 1 hp770423 hp708768 hp770423 rfl rfl rfl

noncomputable def hp770428 := hp770415 hd4911 hd4913 hd4915 hd4917 hd4918 (hp770421 (hp770422 rfl) rfl rfl rfl rfl) (hp770426 (hp770427 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770429 := hp770352 (BSN.cos_quad_nat2 218 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 397860237 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl rfl (hp770428 rfl rfl rfl rfl rfl) hp770414

noncomputable def hp770430 := nat_lit 19094331141657541527108900571498441892518043072878019247399636949459271680

noncomputable def hp770431 := nat_lit 5773293933556132076117262464768009974388704682072530984296970983571456

noncomputable def hp770432 := nat_lit 49999615276067803595257216405172009130922054907100028216833996914610405376

noncomputable def hp770433 := BSN.sin_dyadic_bound_f 525022552 536870912 3 2 536870912 268435456 hp770430 hp708845 hp770431 hp770432 hp708848

noncomputable def hp770434 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 525022552) (BSN.sinEvenQ 536870912) 0 2 hp770430 hp708845 hp770431 rfl rfl rfl

noncomputable def hp770435 := hp770433 hp770431 445250106 rfl rfl rfl rfl rfl rfl rfl rfl (hp770434 rfl)

noncomputable def hp770436 := @BSN.binarySplit_of_base2 (BSN.sinOddP 525022552) (BSN.sinOddQ 536870912) 0 2 hp770432 hp708848 hp770431 rfl rfl rfl

noncomputable def hp770437 := nat_lit 3405355943263190615906183006755590155099127242828173217149132595164190625

noncomputable def hp770438 := nat_lit 595107829186592244472114165968862378624225968505693583793263375390625

noncomputable def hp770439 := nat_lit 10214877614131198663229604791934832740540133276547508264279811258741790625

noncomputable def hp770440 := BSN.cos_dyadic_bound_f 395206845 536870912 3 2 536870912 268435456 hp770437 hp708868 hp770438 hp770439 hp708870

noncomputable def hp770441 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 395206845) (BSN.cosEvenQ 536870912) 0 2 hp770437 hp708868 hp770438 rfl rfl rfl

noncomputable def hp770442 := hp770440 hp770438 397860237 rfl rfl rfl rfl rfl rfl rfl rfl (hp770441 rfl)

noncomputable def hp770443 := @BSN.binarySplit_of_base2 (BSN.cosOddP 395206845) (BSN.cosOddQ 536870912) 0 2 hp770439 hp708870 hp770438 rfl rfl rfl

noncomputable def hp770444 := hp770429 hd4920 hd4922 hd4924 hd4926 hd4918 (hp770435 (hp770436 rfl) rfl rfl rfl rfl) (hp770442 (hp770443 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770445 := hp770347 (BSN.cos_quad_nat3 23 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 486077143 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl rfl (hp770444 rfl rfl rfl rfl rfl) hp770414

noncomputable def hp770446 := nat_lit 55056657841691317631700583969340199868268061623399953432445898902810617636583257648245765489669710949204571303681

noncomputable def hp770447 := nat_lit 63308011625799608666171946043396990923457089552053319076186742117910914212507455428534296012846099197177601

noncomputable def hp770448 := nat_lit 333376014665046340443084290690437153438176357211253676871120113250597567979105765074691728281618693032176458772225

noncomputable def hp770449 := BSN.cos_dyadic_bound_f 794550593 536870912 4 3 536870912 268435456 hp770446 hp716712 hp770447 hp770448 hp716714

noncomputable def hp770450 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 794550593) (BSN.cosEvenQ 536870912) 0 3 hp770446 hp716712 hp770447 rfl rfl rfl

noncomputable def hp770451 := hp770449 hp770447 48697238 rfl rfl rfl rfl rfl rfl rfl rfl (hp770450 rfl)

noncomputable def hp770452 := @BSN.binarySplit_of_base3 (BSN.cosOddP 794550593) (BSN.cosOddQ 536870912) 0 3 hp770448 hp716714 hp770447 rfl rfl rfl

noncomputable def hp770453 := nat_lit 34325433032596695093478667155470529339560297386916967490118249337318488865

noncomputable def hp770454 := nat_lit 18648223650847852954209142767851399371897040861450791547667288352308001

noncomputable def hp770455 := nat_lit 89869751294699495387661122985560579337960564613863994525899191702311353121

noncomputable def hp770456 := BSN.sin_dyadic_bound_f 607896557 536870912 3 2 536870912 268435456 hp770453 hp708845 hp770454 hp770455 hp708848

noncomputable def hp770457 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 607896557) (BSN.sinEvenQ 536870912) 0 2 hp770453 hp708845 hp770454 rfl rfl rfl

noncomputable def hp770458 := hp770456 hp770454 486077143 rfl rfl rfl rfl rfl rfl rfl rfl (hp770457 rfl)

noncomputable def hp770459 := @BSN.binarySplit_of_base2 (BSN.sinOddP 607896557) (BSN.sinOddQ 536870912) 0 2 hp770455 hp708848 hp770454 rfl rfl rfl

noncomputable def hp770460 := hp770445 hd4928 hd4930 hd4932 hd4934 hd4918 (hp770451 (hp770452 rfl) rfl rfl rfl rfl) (hp770458 (hp770459 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770461 := hp770342 (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 492112264 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl rfl (hp770460 rfl rfl rfl rfl rfl) hp770414

noncomputable def hp770462 := nat_lit 13062882796107243813878122195725539962764148835350655358582294824783708160

noncomputable def hp770463 := nat_lit 2702562665905879238751461511044943668889868654327818995602414387593216

noncomputable def hp770464 := nat_lit 34207936507393219517579960527310912850823139543335185660770273013044084736

noncomputable def hp770465 := BSN.sin_dyadic_bound_f 477498456 536870912 3 2 536870912 268435456 hp770462 hp708845 hp770463 hp770464 hp708848

noncomputable def hp770466 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 477498456) (BSN.sinEvenQ 536870912) 0 2 hp770462 hp708845 hp770463 rfl rfl rfl

noncomputable def hp770467 := hp770465 hp770463 416987838 rfl rfl rfl rfl rfl rfl rfl rfl (hp770466 rfl)

noncomputable def hp770468 := @BSN.binarySplit_of_base2 (BSN.sinOddP 477498456) (BSN.sinOddQ 536870912) 0 2 hp770464 hp708848 hp770463 rfl rfl rfl

noncomputable def hp770469 := nat_lit 53824759989201548946443053307726972349790502933807267372992182407542315820647709098479520471827813892885558833201

noncomputable def hp770470 := nat_lit 3388389403639021757068297843307686166504286158720024748457618861417063304725112739346083847086983958474801

noncomputable def hp770471 := nat_lit 269024380554855351047968658428489900731526485533673127095668558045111061116071682294156815358664396604531950989361

noncomputable def hp770472 := BSN.sin_dyadic_bound_f 622538349 536870912 4 3 536870912 268435456 hp770469 hp642702 hp770470 hp770471 hp642705

noncomputable def hp770473 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 622538349) (BSN.sinEvenQ 536870912) 0 3 hp770469 hp642702 hp770470 rfl rfl rfl

noncomputable def hp770474 := hp770472 hp770470 492112264 rfl rfl rfl rfl rfl rfl rfl rfl (hp770473 rfl)

noncomputable def hp770475 := @BSN.binarySplit_of_base3 (BSN.sinOddP 622538349) (BSN.sinOddQ 536870912) 0 3 hp770471 hp642705 hp770470 rfl rfl rfl

noncomputable def hp770476 := hp770461 hd4936 hd4938 hd4940 hd4942 hd4918 (hp770467 (hp770468 rfl) rfl rfl rfl rfl) (hp770474 (hp770475 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770477 := hp770337 (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 528138606 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl rfl (hp770476 rfl rfl rfl rfl rfl) hp770414

noncomputable def hp770478 := nat_lit 18756919281697085332444659995231826315038708867214519160644131341248209072670588152386506191921081920215870078976

noncomputable def hp770479 := nat_lit 2517450385650487323228709494414504164547568474332128870271098126883792535016608817452209037979134770282496

noncomputable def hp770480 := nat_lit 113718095242288891603046751477612475081098539405322405155413227466282832592385052586761995607968203045687934320640

noncomputable def hp770481 := BSN.cos_dyadic_bound_f 607314164 536870912 4 3 536870912 268435456 hp770478 hp716712 hp770479 hp770480 hp716714

noncomputable def hp770482 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 607314164) (BSN.cosEvenQ 536870912) 0 3 hp770478 hp716712 hp770479 rfl rfl rfl

noncomputable def hp770483 := hp770481 hp770479 228473174 rfl rfl rfl rfl rfl rfl rfl rfl (hp770482 rfl)

noncomputable def hp770484 := @BSN.binarySplit_of_base3 (BSN.cosOddP 607314164) (BSN.cosOddQ 536870912) 0 3 hp770480 hp716714 hp770479 rfl rfl rfl

noncomputable def hp770485 := nat_lit 111267765244788153467499826641880060001129645090066247858928718388638284966168423964597567955302248811230457047041

noncomputable def hp770486 := nat_lit 29876196829493485276027326652955567926272276926866948823087855592279321698311430201283794629890215885219841

noncomputable def hp770487 := nat_lit 555914445612545962212707842812129893524531473212656107569107955580279220993475641270423692990126347017037302016001

noncomputable def hp770488 := BSN.sin_dyadic_bound_f 746352129 536870912 4 3 536870912 268435456 hp770485 hp642702 hp770486 hp770487 hp642705

noncomputable def hp770489 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 746352129) (BSN.sinEvenQ 536870912) 0 3 hp770485 hp642702 hp770486 rfl rfl rfl

noncomputable def hp770490 := hp770488 hp770486 528138606 rfl rfl rfl rfl rfl rfl rfl rfl (hp770489 rfl)

noncomputable def hp770491 := @BSN.binarySplit_of_base3 (BSN.sinOddP 746352129) (BSN.sinOddQ 536870912) 0 3 hp770487 hp642705 hp770486 rfl rfl rfl

noncomputable def hp770492 := hp770477 hd4944 hd4946 hd4961 hd4963 hd4918 (hp770483 (hp770484 rfl) rfl rfl rfl rfl) (hp770490 (hp770491 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770493 := hp770332 497095300 Bool.false Bool.true 880598558 235179 BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 497095300 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl (hp770492 rfl rfl rfl rfl rfl)

noncomputable def hp770494 := nat_lit 261037021407400277516486950915773310677662070717273930937479740449161216

noncomputable def hp770495 := nat_lit 3497961407009603709861773602583368099530403145778381751714630926336

noncomputable def hp770496 := nat_lit 783104068299386813342041129200114765296787151345530236048935792085630976

noncomputable def hp770497 := BSN.cos_dyadic_bound_f 207958596 536870912 3 2 536870912 268435456 hp770494 hp708868 hp770495 hp770496 hp708870

noncomputable def hp770498 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 207958596) (BSN.cosEvenQ 536870912) 0 2 hp770494 hp708868 hp770495 rfl rfl rfl

noncomputable def hp770499 := hp770497 hp770495 497095300 rfl rfl rfl rfl rfl rfl rfl rfl (hp770498 rfl)

noncomputable def hp770500 := @BSN.binarySplit_of_base2 (BSN.cosOddP 207958596) (BSN.cosOddQ 536870912) 0 2 hp770496 hp708870 hp770495 rfl rfl rfl

noncomputable def hp770501 := hp770493 hp770414 hd5088 hd5090 hd4918 (hp770499 (hp770500 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp770502 := @hp770327 Bool.true 440299279 134217728 235179 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 909166 1000)) (Enclosure.sfrac Bool.false 909166 1000) 12) (@hp770329 235179 268435456 (hp770501 rfl rfl rfl) (hp770501 rfl rfl rfl) rfl rfl)

noncomputable def hp770503 := @Enclosure.Real.IsNear.mulLit_ff hp770318 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1))) 19349247 67108864 1

noncomputable def hp770504 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp770317 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp770505 := @hp770504 1 1 0 1 19349247 67108864 1 67108864 19349247 67108864 1

noncomputable def hp770506 := @Enclosure.Real.IsNear.of_eq (hp770317 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp770507 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 909166 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770508 := @hp770506 (@Inv.inv Real Real.instInv (Real.sqrt hp770319)) Bool.false 19349247 67108864 1 67108864 (hp770507 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 909166 1000) 909166 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000))))

noncomputable def hp770509 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp770319)) Bool.false 19349247 67108864 1 67108864 19349247 67108864

noncomputable def hp770510 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp770319) Bool.false 232753228 67108864 6 67108864 58188307 16777216 3 33554432

noncomputable def hp770511 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 909166 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770512 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 909166 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770513 := @hp770512 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 909166 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4855267830181

noncomputable def hp770514 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 909166 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 909166 1000 0

noncomputable def hp770515 := @hp770514 1 10680707 67108864 1 67108864 4855267830181 33554432000 454583 33554432000 (Enclosure.Real.IsNear.const Bool.false 909166 1000) hd4949

noncomputable def hp770516 := @hp770513 33554432000 454583 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 909166 1000) 909166 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000))) (hp770515 rfl)

noncomputable def hp770517 := @hp770511 4855267830181 33554432000 454583 33554432000 403628218 403628257 33554432 hp770516 rfl rfl rfl

noncomputable def hp770518 := @Enclosure.Real.IsNear.recentre' hp770319 Bool.false 807256475 67108864 39 67108864 807256475 67108864 39 67108864 (hp770517 rfl rfl rfl)

noncomputable def hp770519 := @Enclosure.Real.IsNear.sqrt_image hp770319 807256475 67108864 39 67108864 116376611 116376617 33554432 (hp770518 rfl) rfl rfl

noncomputable def hp770520 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp770319) 58188307 16777216 3 33554432 9674623 9674624 33554432 (hp770510 (hp770519 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp770521 := @hp770505 67108864 (@hp769737 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (hp770508 (@hp770509 1 67108864 (hp770520 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp770522 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770523 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp770524 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1))) (hp770522 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770523 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp770525 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 909166 1000) 909166 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl

noncomputable def hp770526 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770527 := @hp770526 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770523 (Enclosure.sfrac Bool.false 1 16)))) 34121597

noncomputable def hp770528 := @hp770527 33554432 131 33554432 14124975 16777216 45289201 11418992640000 481966704585075 562949953421312 2804755053187453 383157812047380480000

noncomputable def hp770529 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770530 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)))) 16498347

noncomputable def hp770531 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)))) Bool.false

noncomputable def hp770532 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 12252883) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp770533 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1))) Bool.false 1724440069986865630385

noncomputable def hp770534 := nat_lit 1052456940969469064328991057

noncomputable def hp770535 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)) 884279719003555 140737488355328 1

noncomputable def hp770536 := @Enclosure.Real.IsNear.subLit_ff_p hp770319 (Enclosure.sfrac Bool.false 12 1) 807256475 67108864 39 67108864 12 1 0

noncomputable def hp770537 := @hp770535 500000000000000 1950107 67108864 39 67108864 1724440069986865630385 9444732965739290427392 hp770534 hp738031 hd4948 (@hp770536 1 1950107 1950107 67108864 39 67108864 (hp770518 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770538 := @hp770532 12252883 67108864 123 33554432 Bool.false 32996694 33554432 1 10890000 (@hp770533 9444732965739290427392 hp770534 hp738031 12252883 67108864 123 33554432 (hp770537 rfl) rfl) (Enclosure.sfrac_false_div 12252883 67108864)

noncomputable def hp770539 := nat_lit 22539960270248719829137032721

noncomputable def hp770540 := BSN.cos_dyadic_bound_f 12252883 67108864 2 1 33554432 10890000 hp770539 hp740060 hp770539 hp770539 hp740061

noncomputable def hp770541 := @BSN.binarySplit_of_base (BSN.cosEvenP 12252883) (BSN.cosEvenQ 67108864) 0 1 hp770539 hp740060 hp770539 rfl rfl rfl

noncomputable def hp770542 := hp770540 hp770539 32996694 rfl rfl rfl rfl rfl rfl rfl rfl (hp770541 rfl)

noncomputable def hp770543 := @BSN.binarySplit_of_base (BSN.cosOddP 12252883) (BSN.cosOddQ 67108864) 0 1 hp770539 hp740061 hp770539 rfl rfl rfl

noncomputable def hp770544 := hp770538 (hp770542 (hp770543 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp770545 := @hp770530 16777216 85814027 22837985280000 34121466 34121728 33554432 (@hp770531 32996694 33554432 1373024432 365407764480000 16498347 16777216 85814027 22837985280000 hp770544 rfl)

noncomputable def hp770546 := @hp770529 Bool.false 68243194 67108864 262 67108864 34121597 33554432 131 33554432 (hp770545 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp770547 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770523 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp770548 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770523 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 19125209)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp770549 := nat_lit 361264984793568246329778413525

noncomputable def hp770550 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770523 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp770549

noncomputable def hp770551 := nat_lit 74734038061082972769854345080995181

noncomputable def hp770552 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770523 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp770553 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp770554 := @hp770553 (Enclosure.sfrac Bool.false 1 16) 127066548136999 4503599627370496 2769355563 4503599627370496 1 16 0

noncomputable def hp770555 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)) 3802917311449

noncomputable def hp770556 := @hp770555 4503599627370496 152109867 4503599627370496 1950107 67108864 39 67108864 8527291697875319259136 127066548136999 4503599627370496 2769355563

noncomputable def hp770557 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)) 1950107 67108864 39

noncomputable def hp770558 := @hp770557 67108864 1950107 67108864 39 67108864 3802917311449 4503599627370496 152109867 4503599627370496 (@hp770536 1 1950107 1950107 67108864 39 67108864 (hp770518 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770559 := hp770558 (@hp770536 1 1950107 1950107 67108864 39 67108864 (hp770518 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770560 := @hp770556 4503599627370496 (hp770559 rfl) (@hp770536 1 1950107 1950107 67108864 39 67108864 (hp770518 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770561 := @hp770552 500000000000000 408541524847655 4503599627370496 2769355563 4503599627370496 hp770549 hp627574 hp770551 hp738055 hd4948 (@hp770554 1 6536664397562480 408541524847655 4503599627370496 2769355563 4503599627370496 (hp770560 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp770562 := @hp770548 19125209 33554432 65 16777216 Bool.false 28249950 33554432 1 10890000 (@hp770550 hp627574 hp770551 hp738055 19125209 33554432 65 16777216 (hp770561 rfl) rfl) (Enclosure.sfrac_true_div 19125209 33554432)

noncomputable def hp770563 := nat_lit 284944901145326490166730809013741546575967687989687586266545601

noncomputable def hp770564 := nat_lit 17899855230157333004608063880223183389633581297942818717121

noncomputable def hp770565 := nat_lit 854798903725519155834183210913464193361123796806466873162202561

noncomputable def hp770566 := BSN.cos_dyadic_bound_f 19125209 33554432 3 2 33554432 10890000 hp770563 hp684401 hp770564 hp770565 hp684404

noncomputable def hp770567 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 19125209) (BSN.cosEvenQ 33554432) 0 2 hp770563 hp684401 hp770564 rfl rfl rfl

noncomputable def hp770568 := hp770566 hp770564 28249950 rfl rfl rfl rfl rfl rfl rfl rfl (hp770567 rfl)

noncomputable def hp770569 := @BSN.binarySplit_of_base2 (BSN.cosOddP 19125209) (BSN.cosOddQ 33554432) 0 2 hp770565 hp684404 hp770564 rfl rfl rfl

noncomputable def hp770570 := hp770562 (BSN.cos_neg_of_bound 19125209 33554432 Bool.false 28249950 33554432 1 10890000 (hp770568 (hp770569 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp770571 := hp770528 hp770546 (@hp770547 28249950 33554432 724627216 182703882240000 14124975 16777216 45289201 11418992640000 (hp770570 rfl) rfl)

noncomputable def hp770572 := @hp770503 67108864 481966704585075 562949953421312 2804755053187453 383157812047380480000 9325692812792648688525 37778931862957161709568 54597939691685435257219 hp740088 (hp770521 rfl) (@hp770524 Bool.false 481966704585075 562949953421312 2804755053187453 383157812047380480000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770319 (Enclosure.sfrac Bool.false 12 1)) (hp770525 rfl (hp770322 rfl rfl))) (hp770571 rfl))

noncomputable def hp770573 := @hp770316 hp770314 hp740088 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 909166 1000))) (@hp770321 hp770314 hp740088 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 909166 1000) 12 (hp770322 rfl rfl)) (@hp770325 hp770314 hp740088 hp770502 (hp770572 rfl) rfl rfl))

theorem hd5094 : hp770315 hp740088 := hp770573

noncomputable def hp770574 := nat_lit 1256360027169350855186779

noncomputable def hp770575 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 910429 1000)) Bool.false 15478527489335219082355 18889465931478580854784 hp770574

noncomputable def hp770576 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 910429 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 910429 1000)) Bool.false 15478527489335219082355 18889465931478580854784

noncomputable def hp770577 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 910429 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770578 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp770577 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp770579 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 910429 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770580 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp770578 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp770581 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 910429 1000)) hp770580 Bool.false 15478527489335219082355 18889465931478580854784

noncomputable def hp770582 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 910429 1000) 910429 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl

noncomputable def hp770583 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp770578 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp770584 := nat_lit 1038746396202058667807966494720

noncomputable def hp770585 := @hp770583 71190337 67108864 117755 134217728 4559770959763533048717 18889465931478580854784 3061467234926176786779 hp758057 hp770584 15478527489335219082355 18889465931478580854784

noncomputable def hp770586 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) 12)

noncomputable def hp770587 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) 12) hp770586

noncomputable def hp770588 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) 12)

noncomputable def hp770589 := @hp770588 284761348 536870912 235510 536870912 284761348 536870912 235510 536870912 305760169206218752 71190337 67108864

noncomputable def hp770590 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) Real.cos BSN.quadSignPos 11

noncomputable def hp770591 := hp770590 12 910429 1000 288 536870912 268435456 9007199254740992 Bool.false 971498979905 4147 1334074092

noncomputable def hp770592 := hp770591 51 154981288 8 Bool.false 141058636 220899 Bool.true 206082919 28296951008113761 1 Bool.false

noncomputable def hp770593 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp770594 := hp770593 BSN.quadSignNeg 9 10 11 910429 1000 182 237 536870912 268435456 9007199254740992

noncomputable def hp770595 := hp770594 Bool.false 971498979905 4147 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp770596 := hp770595 Bool.false 401858254 189635 Bool.true 481812086 Bool.true 685476831 28296951008113761 1 Bool.false 334797736

noncomputable def hp770597 := hp770596 Bool.true Bool.false 513835657 Bool.true Bool.false 141058636 220899 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 334797736 536870912) BSN.abs_quadSignNeg

noncomputable def hp770598 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp770599 := hp770598 BSN.quadSignNeg 7 8 9 910429 1000 53 121 536870912 268435456 9007199254740992

noncomputable def hp770600 := hp770599 Bool.false 971498979905 4147 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp770601 := hp770600 Bool.false 598638147 154873 Bool.true 200689887 Bool.true 425594666 28296951008113761 1 Bool.false 196048469

noncomputable def hp770602 := hp770601 Bool.true Bool.false 382398876 Bool.true Bool.false 401858254 189635 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 53 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 196048469 536870912) BSN.abs_quadSignNeg

noncomputable def hp770603 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp770604 := hp770603 BSN.quadSignPos 5 6 7 910429 1000 113 24 536870912 268435456 9007199254740992

noncomputable def hp770605 := hp770604 Bool.false 971498979905 4147 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp770606 := hp770605 Bool.false 557217142 115087 Bool.false 423112311 Bool.false 131933648 28296951008113761 1 Bool.false 380652424

noncomputable def hp770607 := hp770606 Bool.true Bool.false 520741276 Bool.false Bool.false 598638147 154873 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 113 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 380652424 536870912) BSN.abs_quadSignPos

noncomputable def hp770608 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp770609 := hp770608 BSN.quadSignPos 3 4 5 910429 1000 348 219 536870912 268435456 9007199254740992

noncomputable def hp770610 := hp770609 Bool.false 971498979905 4147 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp770611 := hp770610 Bool.false 304753258 68020 Bool.false 428517178 Bool.false 147394979 28296951008113761 1 Bool.false 374743630

noncomputable def hp770612 := hp770611 Bool.false Bool.false 145550302 Bool.false Bool.false 557217142 115087 BSN.abs_quadSignPos (BSN.cos_quad_nat0 348 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 374743630 536870912) BSN.abs_quadSignPos

noncomputable def hp770613 := hp770593 BSN.quadSignPos 1 2 3 910429 1000 750 515 536870912 268435456 9007199254740992

noncomputable def hp770614 := hp770613 Bool.false 971498979905 4147 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp770615 := hp770614 Bool.false 536870840 4202 Bool.false 214398462 Bool.false 208990863 28296951008113761 1 Bool.false 494627009

noncomputable def hp770616 := hp770615 Bool.true Bool.false 203752449 Bool.false Bool.false 304753258 68020 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 750 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 494627009 536870912) BSN.abs_quadSignPos

noncomputable def hp770617 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) 1) Bool.false

noncomputable def hp770618 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)))

noncomputable def hp770619 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000))) Bool.false 67108855 67108864

noncomputable def hp770620 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 15179671561) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 15179671561 8388608

noncomputable def hp770621 := nat_lit 167075065610034061490251920502674741141465249578067484388443

noncomputable def hp770622 := nat_lit 92329219795240660417645390920353341741227349037285376000

noncomputable def hp770623 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) Bool.false hp770621 hp770622 45931416591885332089

noncomputable def hp770624 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 910429 4000) (Real.log (Enclosure.sfrac Bool.false 3315524856164 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1820858))))))

noncomputable def hp770625 := nat_lit 300242372872283840465529147111520000

noncomputable def hp770626 := nat_lit 1640096410597647399101457759946380252480

noncomputable def hp770627 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp770624 (Enclosure.sfrac Bool.false 910429 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 910429 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp770625 hp770626)) Bool.false

noncomputable def hp770628 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 910429 1000) 910429 1000 3315524856164 16000000 1820858

noncomputable def hp770629 := hp770628 4000 2000 hp770625 hp770626 (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl rfl rfl rfl

noncomputable def hp770630 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp770624 (Enclosure.sfrac Bool.false 910429 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 910429 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp770625 hp770626) 32598099757083478095787 18014398509481984000

noncomputable def hp770631 := nat_lit 53464020995210899676880614560855917165268879864981595004301760

noncomputable def hp770632 := @hp770630 45931416591885332089 hp737908 hp770625 hp770626 0 1 hp770631 hp770621 hp770622 45931416591885332089 hp737908

noncomputable def hp770633 := @Enclosure.Real.IsNear.subLit_ff_p (hp770624 (Enclosure.sfrac Bool.false 910429 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 910429 2000) (Real.log Real.pi)) 41985360325986635380651 18014398509481984000 3826793118438859 1452000000000000000000

noncomputable def hp770634 := nat_lit 2187621443256548168177148755968000

noncomputable def hp770635 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 910429 4000) (Real.log (Enclosure.sfrac Bool.false 3315524856164 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1820858))))))

noncomputable def hp770636 := @hp770635 (Enclosure.sfrac Bool.false 910429 2000) 50185775736281221986219 18014398509481984000 3826793118438859 1452000000000000000000 910429 2000 0

noncomputable def hp770637 := nat_lit 83970720651973270761302000

noncomputable def hp770638 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 910429 4000) (Real.log (Enclosure.sfrac Bool.false 3315524856164 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1820858))))) 50192847500803176570219

noncomputable def hp770639 := nat_lit 113008320452607695435714667580659597312

noncomputable def hp770640 := @hp770638 18014398509481984000 11380379354772077 4356000000000000000000 883970565244323 2251799813685248 200000001089 8712000000000000000 hp770639 50185775736281221986219 18014398509481984000 3826793118438859

noncomputable def hp770641 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 910429 4000) (Real.log (Enclosure.sfrac Bool.false 3315524856164 16000000)) 910429 4000 0 1 55130984954129511 4503599627370496

noncomputable def hp770642 := nat_lit 118392888687127154946736128

noncomputable def hp770643 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3315524856164) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp770642 hp617687

noncomputable def hp770644 := BSN.log_rat_reduce_isNear 3315524856164 16000000 17 6631049712328 4194304000000 122953023 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp770645 := nat_lit 85450192420432150756268276209249824331995941145179339768957567764472446263960070147477025032603870094887280831070627576240998120731169689686531460012399656960

noncomputable def hp770646 := nat_lit 1488733004756849668318917549081555389597925758977948847101705536127644372438830128263695421846150714803786245986928160366443667659370381542891552742112755712

noncomputable def hp770647 := nat_lit 111221070897915766022122627404213744280157075722913093448433340571617574152932311700978558354559151645757635679631679624688050130364484962905667665920

noncomputable def hp770648 := BSN.log_dyadic_bound 1218372856164 5412676856164 7 6 hp770645 268435456 87120000 hp770646 hp770647 122953023 6631049712328

noncomputable def hp770649 := hp770648 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp770650 := @BSN.binarySplit_of_base6 (BSN.artanhP 1218372856164) (BSN.artanhQ 5412676856164) 0 6 hp770646 hp770645 hp770647 rfl rfl rfl

noncomputable def hp770651 := hp770644 rfl rfl rfl rfl (hp770649 (hp770650 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp770652 := @hp770641 12500018513 1089000000000000000 50192847500803176570219 18014398509481984000 11380379354772077 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 910429 4000) (BSN.isNear_log_sfrac 3315524856164 16000000 55130984954129511 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp770643 1000001481040000 87120000000000000000000 55130984954129511 4503599627370496 12500018513 1089000000000000000 (hp770651 rfl rfl rfl) rfl)) rfl

noncomputable def hp770653 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1820858)))) 1 4

noncomputable def hp770654 := @hp770653 0 1 883970565244323 562949953421312 200000001089 2178000000000000000 883970565244323 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp770655 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1820858))) 884279719003555 562949953421312 1

noncomputable def hp770656 := @hp770655 2000000000000000 18427 33554432 1 10890000 29661130221492199489536 883970565244323 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp770657 := BSN.arctan_dyadic_bound_f 1000 1820858 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp770658 := hp770657 1 18427 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1820858) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1820858) 0 0 rfl)

noncomputable def hp770659 := hp770654 (hp770656 (hp770658 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp770660 := @hp770633 34970270726469 67108864000 2731287 536870912000 hp770634 32598099757083478095787 18014398509481984000 45931416591885332089 hp737908 (@hp770636 1 hp770637 41985360325986635380651 18014398509481984000 3826793118438859 1452000000000000000000 (@hp770640 1452000000000000000000 hp770652 hp770659 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 910429 2000) rfl rfl)

noncomputable def hp770661 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 910429 2000) (Real.log Real.pi) 910429 2000 0 1 38410761 33554432

noncomputable def hp770662 := hp770660 (@hp770661 3 268435456 34970270726469 67108864000 2731287 536870912000 (Enclosure.Real.IsNear.const Bool.false 910429 2000) hd4909 rfl) rfl

noncomputable def hp770663 := @hp770623 hp737908 15179671561 8388608 519 67108864 (@hp770627 hp770621 hp770622 45931416591885332089 hp737908 (hp770629 rfl rfl rfl rfl rfl) (hp770632 (hp770662 rfl) (Enclosure.Real.IsNear.const Bool.true hp770625 hp770626) rfl rfl)) rfl

noncomputable def hp770664 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 15179671561) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 597128704753676582912) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp770665 := BSN.sin_reduce_arg_pos_rat_q0 15179671561 8388608 226375608064910080 72057594037927936 288 597128704753676582912 hp630689 rfl rfl rfl rfl

noncomputable def hp770666 := BSN.cos_dyadic_bound_f 67885674 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp770667 := hp770666 1 67108855 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 67885674) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp770668 := hp770667 (@BSN.binarySplit_of_le (BSN.cosOddP 67885674) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp770669 := @BSN.cos_arg_round Bool.false 67108855 67108864 597128704753676582912 hp630689 67885674 137438953472 21801270 21780000 hp770668 rfl

noncomputable def hp770670 := hp770664 67108855 67108864 288 1000000000000000 21780000 10890000 hp770665 BSN.pi_near_15 hp770669 rfl rfl

noncomputable def hp770671 := @hp770620 519 67108864 Bool.false 67108855 67108864 1 10890000 hp770663 (Enclosure.sfrac_false_div 15179671561 8388608) (hp770670 rfl rfl) rfl

noncomputable def hp770672 := @hp770617 67108855 67108864 357438679 45675970560000 536870840 536870912 4202 536870912 (@hp770618 Bool.false 67108855 67108864 357438679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000)) (@hp770619 5719018864 730815528960000 67108855 67108864 357438679 45675970560000 (hp770671 rfl) rfl))

noncomputable def hp770673 := @hp770623 hp737908 971498979905 536870912 4147 536870912 (@hp770627 hp770621 hp770622 45931416591885332089 hp737908 (hp770629 rfl rfl rfl rfl rfl) (hp770632 (hp770662 rfl) (Enclosure.Real.IsNear.const Bool.true hp770625 hp770626) rfl rfl)) rfl

noncomputable def hp770674 := hp770616 (BSN.cos_quad_nat3 515 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 203752449 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl rfl (hp770672 rfl) hp770673

noncomputable def hp770675 := nat_lit 294904918489708310160309960940781693606321025616670772729694430253547776

noncomputable def hp770676 := nat_lit 4464505113818378773429532896414228650040848966915836711650776842496

noncomputable def hp770677 := nat_lit 884705826458897293723383023756552252361662995152078486515659989206958336

noncomputable def hp770678 := BSN.cos_dyadic_bound_f 214398462 536870912 3 2 536870912 268435456 hp770675 hp708868 hp770676 hp770677 hp708870

noncomputable def hp770679 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 214398462) (BSN.cosEvenQ 536870912) 0 2 hp770675 hp708868 hp770676 rfl rfl rfl

noncomputable def hp770680 := hp770678 hp770676 494627009 rfl rfl rfl rfl rfl rfl rfl rfl (hp770679 rfl)

noncomputable def hp770681 := @BSN.binarySplit_of_base2 (BSN.cosOddP 214398462) (BSN.cosOddQ 536870912) 0 2 hp770677 hp708870 hp770676 rfl rfl rfl

noncomputable def hp770682 := nat_lit 1907696124163259474024187546983361

noncomputable def hp770683 := BSN.sin_dyadic_bound_f 208990863 536870912 2 1 536870912 268435456 hp770682 hp708890 hp770682 hp770682 hp708891

noncomputable def hp770684 := @BSN.binarySplit_of_base (BSN.sinEvenP 208990863) (BSN.sinEvenQ 536870912) 0 1 hp770682 hp708890 hp770682 rfl rfl rfl

noncomputable def hp770685 := hp770683 hp770682 203752449 rfl rfl rfl rfl rfl rfl rfl rfl (hp770684 rfl)

noncomputable def hp770686 := @BSN.binarySplit_of_base (BSN.sinOddP 208990863) (BSN.sinOddQ 536870912) 0 1 hp770682 hp708891 hp770682 rfl rfl rfl

noncomputable def hp770687 := hp770674 hd4911 hd4913 hd4915 hd4917 hd4918 (hp770680 (hp770681 rfl) rfl rfl rfl rfl) (hp770685 (hp770686 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770688 := hp770612 (BSN.cos_quad_nat3 219 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 145550302 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl rfl (hp770687 rfl rfl rfl rfl rfl) hp770673

noncomputable def hp770689 := nat_lit 4707243163317483647712397461898511504515390762980443319394408525768335616

noncomputable def hp770690 := nat_lit 1136961842559470256454896174647406269340585831727517909698434732564736

noncomputable def hp770691 := nat_lit 14119455566267332002624282593346239701007491117277874922363828707839877376

noncomputable def hp770692 := BSN.cos_dyadic_bound_f 428517178 536870912 3 2 536870912 268435456 hp770689 hp708868 hp770690 hp770691 hp708870

noncomputable def hp770693 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 428517178) (BSN.cosEvenQ 536870912) 0 2 hp770689 hp708868 hp770690 rfl rfl rfl

noncomputable def hp770694 := hp770692 hp770690 374743630 rfl rfl rfl rfl rfl rfl rfl rfl (hp770693 rfl)

noncomputable def hp770695 := @BSN.binarySplit_of_base2 (BSN.cosOddP 428517178) (BSN.cosOddQ 536870912) 0 2 hp770691 hp708870 hp770690 rfl rfl rfl

noncomputable def hp770696 := nat_lit 471987783883440958716862049814481

noncomputable def hp770697 := BSN.sin_dyadic_bound_f 147394979 536870912 2 1 536870912 268435456 hp770696 hp708890 hp770696 hp770696 hp708891

noncomputable def hp770698 := @BSN.binarySplit_of_base (BSN.sinEvenP 147394979) (BSN.sinEvenQ 536870912) 0 1 hp770696 hp708890 hp770696 rfl rfl rfl

noncomputable def hp770699 := hp770697 hp770696 145550302 rfl rfl rfl rfl rfl rfl rfl rfl (hp770698 rfl)

noncomputable def hp770700 := @BSN.binarySplit_of_base (BSN.sinOddP 147394979) (BSN.sinOddQ 536870912) 0 1 hp770696 hp708891 hp770696 rfl rfl rfl

noncomputable def hp770701 := hp770688 hd4920 hd4922 hd4924 hd4926 hd4918 (hp770694 (hp770695 rfl) rfl rfl rfl rfl) (hp770699 (hp770700 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770702 := hp770607 (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 520741276 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl rfl (hp770701 rfl rfl rfl rfl rfl) hp770673

noncomputable def hp770703 := nat_lit 8052659438764202558887496823116974333960186430147303427709149643489411905

noncomputable def hp770704 := nat_lit 1027177020472467937142561967376856254607660600966878791898334368105281

noncomputable def hp770705 := nat_lit 21088635481587384610902356103073465488340647295127086411670413667781051201

noncomputable def hp770706 := BSN.sin_dyadic_bound_f 423112311 536870912 3 2 536870912 268435456 hp770703 hp708845 hp770704 hp770705 hp708848

noncomputable def hp770707 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 423112311) (BSN.sinEvenQ 536870912) 0 2 hp770703 hp708845 hp770704 rfl rfl rfl

noncomputable def hp770708 := hp770706 hp770704 380652424 rfl rfl rfl rfl rfl rfl rfl rfl (hp770707 rfl)

noncomputable def hp770709 := @BSN.binarySplit_of_base2 (BSN.sinOddP 423112311) (BSN.sinOddQ 536870912) 0 2 hp770705 hp708848 hp770704 rfl rfl rfl

noncomputable def hp770710 := nat_lit 302985806202985587900174623113216

noncomputable def hp770711 := BSN.cos_dyadic_bound_f 131933648 536870912 2 1 536870912 268435456 hp770710 hp708767 hp770710 hp770710 hp708768

noncomputable def hp770712 := @BSN.binarySplit_of_base (BSN.cosEvenP 131933648) (BSN.cosEvenQ 536870912) 0 1 hp770710 hp708767 hp770710 rfl rfl rfl

noncomputable def hp770713 := hp770711 hp770710 520741276 rfl rfl rfl rfl rfl rfl rfl rfl (hp770712 rfl)

noncomputable def hp770714 := @BSN.binarySplit_of_base (BSN.cosOddP 131933648) (BSN.cosOddQ 536870912) 0 1 hp770710 hp708768 hp770710 rfl rfl rfl

noncomputable def hp770715 := hp770702 hd4928 hd4930 hd4932 hd4934 hd4918 (hp770708 (hp770709 rfl) rfl rfl rfl rfl) (hp770713 (hp770714 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770716 := hp770602 (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 382398876 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl rfl (hp770715 rfl rfl rfl rfl rfl) hp770673

noncomputable def hp770717 := nat_lit 1622190873482090144713625567327361

noncomputable def hp770718 := BSN.sin_dyadic_bound_f 200689887 536870912 2 1 536870912 268435456 hp770717 hp708890 hp770717 hp770717 hp708891

noncomputable def hp770719 := @BSN.binarySplit_of_base (BSN.sinEvenP 200689887) (BSN.sinEvenQ 536870912) 0 1 hp770717 hp708890 hp770717 rfl rfl rfl

noncomputable def hp770720 := hp770718 hp770717 196048469 rfl rfl rfl rfl rfl rfl rfl rfl (hp770719 rfl)

noncomputable def hp770721 := @BSN.binarySplit_of_base (BSN.sinOddP 200689887) (BSN.sinOddQ 536870912) 0 1 hp770717 hp708891 hp770717 rfl rfl rfl

noncomputable def hp770722 := nat_lit 8243330295030127208809258142276082828541724484646691321652699323537056000

noncomputable def hp770723 := nat_lit 1076389395023293095007133369254412430503962748777645675868573029130496

noncomputable def hp770724 := nat_lit 21587931856534581167584712156696662168912271996290932511329472919597506816

noncomputable def hp770725 := BSN.sin_dyadic_bound_f 425594666 536870912 3 2 536870912 268435456 hp770722 hp708845 hp770723 hp770724 hp708848

noncomputable def hp770726 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 425594666) (BSN.sinEvenQ 536870912) 0 2 hp770722 hp708845 hp770723 rfl rfl rfl

noncomputable def hp770727 := hp770725 hp770723 382398876 rfl rfl rfl rfl rfl rfl rfl rfl (hp770726 rfl)

noncomputable def hp770728 := @BSN.binarySplit_of_base2 (BSN.sinOddP 425594666) (BSN.sinOddQ 536870912) 0 2 hp770724 hp708848 hp770723 rfl rfl rfl

noncomputable def hp770729 := hp770716 hd4936 hd4938 hd4940 hd4942 hd4918 (hp770720 (hp770721 rfl) rfl rfl rfl rfl) (hp770727 (hp770728 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770730 := hp770597 (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 513835657 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl rfl (hp770729 rfl rfl rfl rfl rfl) hp770673

noncomputable def hp770731 := nat_lit 7524318928398090980178103121005586469504222975362622468103522918573793536

noncomputable def hp770732 := nat_lit 2904166548804190933271151372533269358141547001631103466773999568281856

noncomputable def hp770733 := nat_lit 22567148452096664558667767060271692869796385832084605197377020756584816896

noncomputable def hp770734 := BSN.cos_dyadic_bound_f 481812086 536870912 3 2 536870912 268435456 hp770731 hp708868 hp770732 hp770733 hp708870

noncomputable def hp770735 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 481812086) (BSN.cosEvenQ 536870912) 0 2 hp770731 hp708868 hp770732 rfl rfl rfl

noncomputable def hp770736 := hp770734 hp770732 334797736 rfl rfl rfl rfl rfl rfl rfl rfl (hp770735 rfl)

noncomputable def hp770737 := @BSN.binarySplit_of_base2 (BSN.cosOddP 481812086) (BSN.cosOddQ 536870912) 0 2 hp770733 hp708870 hp770732 rfl rfl rfl

noncomputable def hp770738 := nat_lit 79142679952510110143028534170409592457721633616307318833323190858149549881501683910492231974260171521416445720961

noncomputable def hp770739 := nat_lit 10762504933226914455744438517578119541675423332994535543587187145303763201324140597246977309834698925439361

noncomputable def hp770740 := nat_lit 395498561174849498729447319655660061564208413210322731343721632097484394229895321444857156756475321187290907048321

noncomputable def hp770741 := BSN.sin_dyadic_bound_f 685476831 536870912 4 3 536870912 268435456 hp770738 hp642702 hp770739 hp770740 hp642705

noncomputable def hp770742 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 685476831) (BSN.sinEvenQ 536870912) 0 3 hp770738 hp642702 hp770739 rfl rfl rfl

noncomputable def hp770743 := hp770741 hp770739 513835657 rfl rfl rfl rfl rfl rfl rfl rfl (hp770742 rfl)

noncomputable def hp770744 := @BSN.binarySplit_of_base3 (BSN.sinOddP 685476831) (BSN.sinOddQ 536870912) 0 3 hp770740 hp642705 hp770739 rfl rfl rfl

noncomputable def hp770745 := hp770730 hd4944 hd4946 hd4961 hd4963 hd4918 (hp770736 (hp770737 rfl) rfl rfl rfl rfl) (hp770743 (hp770744 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770746 := hp770592 497800781 Bool.false Bool.false 284761348 235510 BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 497800781 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl (hp770745 rfl rfl rfl rfl rfl)

noncomputable def hp770747 := nat_lit 251745884746933135374371302366952236283032071756813332386379950449193921

noncomputable def hp770748 := nat_lit 3253388875016906892075020174075110003966483940861831076803418747841

noncomputable def hp770749 := nat_lit 755231147463049372309329757060508558629088282302558273496986244510086081

noncomputable def hp770750 := BSN.cos_dyadic_bound_f 206082919 536870912 3 2 536870912 268435456 hp770747 hp708868 hp770748 hp770749 hp708870

noncomputable def hp770751 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 206082919) (BSN.cosEvenQ 536870912) 0 2 hp770747 hp708868 hp770748 rfl rfl rfl

noncomputable def hp770752 := hp770750 hp770748 497800781 rfl rfl rfl rfl rfl rfl rfl rfl (hp770751 rfl)

noncomputable def hp770753 := @BSN.binarySplit_of_base2 (BSN.cosOddP 206082919) (BSN.cosOddQ 536870912) 0 2 hp770749 hp708870 hp770748 rfl rfl rfl

noncomputable def hp770754 := hp770746 hp770673 hd5088 hd5090 hd4918 (hp770752 (hp770753 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp770755 := @hp770587 Bool.false 71190337 67108864 117755 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 910429 1000)) (Enclosure.sfrac Bool.false 910429 1000) 12) (@hp770589 117755 134217728 (hp770754 rfl rfl rfl) (hp770754 rfl rfl rfl) rfl rfl)

noncomputable def hp770756 := @Enclosure.Real.IsNear.mulLit_ff hp770578 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1))) 19342533 67108864 1

noncomputable def hp770757 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp770577 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp770758 := @hp770757 1 1 0 1 19342533 67108864 1 67108864 19342533 67108864 1

noncomputable def hp770759 := @Enclosure.Real.IsNear.of_eq (hp770577 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp770760 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 910429 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770761 := @hp770759 (@Inv.inv Real Real.instInv (Real.sqrt hp770579)) Bool.false 19342533 67108864 1 67108864 (hp770760 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 910429 1000) 910429 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000))))

noncomputable def hp770762 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp770579)) Bool.false 19342533 67108864 1 67108864 19342533 67108864

noncomputable def hp770763 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp770579) Bool.false 232834020 67108864 6 67108864 58208505 16777216 3 33554432

noncomputable def hp770764 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 910429 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770765 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 910429 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770766 := @hp770765 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 910429 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9724025393303

noncomputable def hp770767 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 910429 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 910429 1000 0

noncomputable def hp770768 := @hp770767 1 10680707 67108864 1 67108864 9724025393303 67108864000 910429 67108864000 (Enclosure.Real.IsNear.const Bool.false 910429 1000) hd4949

noncomputable def hp770769 := @hp770766 67108864000 910429 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 910429 1000) 910429 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000))) (hp770768 rfl)

noncomputable def hp770770 := @hp770764 9724025393303 67108864000 910429 67108864000 403908478 403908517 33554432 hp770769 rfl rfl rfl

noncomputable def hp770771 := @Enclosure.Real.IsNear.recentre' hp770579 Bool.false 807816995 67108864 39 67108864 807816995 67108864 39 67108864 (hp770770 rfl rfl rfl)

noncomputable def hp770772 := @Enclosure.Real.IsNear.sqrt_image hp770579 807816995 67108864 39 67108864 116417007 116417013 33554432 (hp770771 rfl) rfl rfl

noncomputable def hp770773 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp770579) 58208505 16777216 3 33554432 9671266 9671267 33554432 (hp770763 (hp770772 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp770774 := @hp770758 67108864 (@hp769737 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (hp770761 (@hp770762 1 67108864 (hp770773 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp770775 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770776 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp770777 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1))) (hp770775 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770776 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp770778 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 910429 1000) 910429 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl

noncomputable def hp770779 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770780 := @hp770779 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770776 (Enclosure.sfrac Bool.false 1 16)))) 17251637

noncomputable def hp770781 := @hp770780 16777216 67 16777216 13664677 16777216 22984913 5709496320000 235738047326249 281474976710656 157354747061431 21286545113743360000

noncomputable def hp770782 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp770783 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)))) 32631683

noncomputable def hp770784 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)))) Bool.false

noncomputable def hp770785 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 7887367) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp770786 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1))) Bool.false 2220096538082738278985

noncomputable def hp770787 := nat_lit 1052456940974283894466498897

noncomputable def hp770788 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)) 884279719003555 140737488355328 1

noncomputable def hp770789 := @Enclosure.Real.IsNear.subLit_ff_p hp770579 (Enclosure.sfrac Bool.false 12 1) 807816995 67108864 39 67108864 12 1 0

noncomputable def hp770790 := @hp770788 500000000000000 2510627 67108864 39 67108864 2220096538082738278985 9444732965739290427392 hp770787 hp738031 hd4948 (@hp770789 1 2510627 2510627 67108864 39 67108864 (hp770771 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770791 := @hp770785 7887367 33554432 123 33554432 Bool.false 32631683 33554432 1 10890000 (@hp770786 9444732965739290427392 hp770787 hp738031 7887367 33554432 123 33554432 (hp770790 rfl) rfl) (Enclosure.sfrac_false_div 7887367 33554432)

noncomputable def hp770792 := nat_lit 3870153550645944458053050721

noncomputable def hp770793 := BSN.cos_dyadic_bound_f 7887367 33554432 2 1 33554432 10890000 hp770792 hp687514 hp770792 hp770792 hp687515

noncomputable def hp770794 := @BSN.binarySplit_of_base (BSN.cosEvenP 7887367) (BSN.cosEvenQ 33554432) 0 1 hp770792 hp687514 hp770792 rfl rfl rfl

noncomputable def hp770795 := hp770793 hp770792 32631683 rfl rfl rfl rfl rfl rfl rfl rfl (hp770794 rfl)

noncomputable def hp770796 := @BSN.binarySplit_of_base (BSN.cosOddP 7887367) (BSN.cosOddQ 33554432) 0 1 hp770792 hp687515 hp770792 rfl rfl rfl

noncomputable def hp770797 := hp770791 (hp770795 (hp770796 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp770798 := @hp770783 33554432 85814027 22837985280000 34503140 34503408 33554432 (@hp770784 32631683 33554432 1373024432 365407764480000 32631683 33554432 85814027 22837985280000 hp770797 rfl)

noncomputable def hp770799 := @hp770782 Bool.false 69006548 67108864 268 67108864 17251637 16777216 67 16777216 (hp770798 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp770800 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770776 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp770801 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770776 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 41538171)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp770802 := nat_lit 392316935642179328482715531525

noncomputable def hp770803 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770776 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp770802

noncomputable def hp770804 := nat_lit 75913884390470247606202296249195901

noncomputable def hp770805 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp770776 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp770806 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp770807 := @hp770806 (Enclosure.sfrac Bool.false 1 16) 162182077964599 4503599627370496 2813076123 4503599627370496 1 16 0

noncomputable def hp770808 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)) 6303247933129

noncomputable def hp770809 := @hp770808 4503599627370496 195830427 4503599627370496 2510627 67108864 39 67108864 10883855013363671105536 162182077964599 4503599627370496 2813076123

noncomputable def hp770810 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)) 2510627 67108864 39

noncomputable def hp770811 := @hp770810 67108864 2510627 67108864 39 67108864 6303247933129 4503599627370496 195830427 4503599627370496 (@hp770789 1 2510627 2510627 67108864 39 67108864 (hp770771 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770812 := hp770811 (@hp770789 1 2510627 2510627 67108864 39 67108864 (hp770771 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770813 := @hp770809 4503599627370496 (hp770812 rfl) (@hp770789 1 2510627 2510627 67108864 39 67108864 (hp770771 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp770814 := @hp770805 500000000000000 443657054675255 4503599627370496 2813076123 4503599627370496 hp770802 hp627574 hp770804 hp738055 hd4948 (@hp770807 1 7098512874804080 443657054675255 4503599627370496 2813076123 4503599627370496 (hp770813 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp770815 := @hp770801 41538171 67108864 33 8388608 Bool.false 27329354 33554432 1 10890000 (@hp770803 hp627574 hp770804 hp738055 41538171 67108864 33 8388608 (hp770814 rfl) rfl) (Enclosure.sfrac_true_div 41538171 67108864)

noncomputable def hp770816 := nat_lit 101450981426732957732768213566009571778187178813351675173779599841

noncomputable def hp770817 := nat_lit 8862963460923892643415942706407649275789934314540457475502561

noncomputable def hp770818 := nat_lit 304335218353277025413017808812615900036009956571425944606387794401

noncomputable def hp770819 := BSN.cos_dyadic_bound_f 41538171 67108864 3 2 33554432 10890000 hp770816 hp738066 hp770817 hp770818 hp738069

noncomputable def hp770820 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 41538171) (BSN.cosEvenQ 67108864) 0 2 hp770816 hp738066 hp770817 rfl rfl rfl

noncomputable def hp770821 := hp770819 hp770817 27329354 rfl rfl rfl rfl rfl rfl rfl rfl (hp770820 rfl)

noncomputable def hp770822 := @BSN.binarySplit_of_base2 (BSN.cosOddP 41538171) (BSN.cosOddQ 67108864) 0 2 hp770818 hp738069 hp770817 rfl rfl rfl

noncomputable def hp770823 := hp770815 (BSN.cos_neg_of_bound 41538171 67108864 Bool.false 27329354 33554432 1 10890000 (hp770821 (hp770822 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp770824 := hp770781 hp770799 (@hp770800 27329354 33554432 367758608 91351941120000 13664677 16777216 22984913 5709496320000 (hp770823 rfl) rfl)

noncomputable def hp770825 := @hp770756 67108864 235738047326249 281474976710656 157354747061431 21286545113743360000 4559770959763533048717 18889465931478580854784 3061467234926176786779 hp758057 (hp770774 rfl) (@hp770777 Bool.false 235738047326249 281474976710656 157354747061431 21286545113743360000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770579 (Enclosure.sfrac Bool.false 12 1)) (hp770778 rfl (hp770582 rfl rfl))) (hp770824 rfl))

noncomputable def hp770826 := @hp770576 hp770574 hp758057 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 910429 1000))) (@hp770581 hp770574 hp758057 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 910429 1000) 12 (hp770582 rfl rfl)) (@hp770585 hp770574 hp758057 hp770755 (hp770825 rfl) rfl rfl))

theorem hd5095 : hp770575 hp758057 := hp770826

noncomputable def hp770827 := nat_lit 2265373731289007116273583

noncomputable def hp770828 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912007 1000)) Bool.true 2610499849347264810517 4722366482869645213696 hp770827

noncomputable def hp770829 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912007 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912007 1000)) Bool.true 2610499849347264810517 4722366482869645213696

noncomputable def hp770830 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 912007 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770831 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp770830 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp770832 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 912007 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp770833 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp770831 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp770834 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912007 1000)) hp770833 Bool.true 2610499849347264810517 4722366482869645213696

noncomputable def hp770835 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 912007 1000) 912007 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl

noncomputable def hp770836 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp770831 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp770837 := nat_lit 700750717447464331763884490752

noncomputable def hp770838 := @hp770836 85376167 268435456 117961 134217728 1108546435724134977045 4722366482869645213696 5489797942954676209583 hp754729 hp770837 2610499849347264810517 4722366482869645213696

noncomputable def hp770839 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) 12)

noncomputable def hp770840 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) 12) hp770839

noncomputable def hp770841 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) 12)

noncomputable def hp770842 := @hp770841 85376167 536870912 235922 536870912 85376167 536870912 235922 536870912 91671961280708608 85376167 268435456

noncomputable def hp770843 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) Real.cos BSN.quadSignPos 11

noncomputable def hp770844 := hp770843 12 912007 1000 288 536870912 268435456 9007199254740992 Bool.false 973607152733 4155 1334074092

noncomputable def hp770845 := hp770844 51 154981288 8 Bool.true 229401379 221285 Bool.true 203079008 28296951008113761 1 Bool.false

noncomputable def hp770846 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp770847 := hp770846 BSN.quadSignNeg 9 10 11 912007 1000 182 237 536870912 268435456 9007199254740992

noncomputable def hp770848 := hp770847 Bool.false 973607152733 4155 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp770849 := hp770848 Bool.false 56987971 189966 Bool.true 324348586 Bool.true 608758430 28296951008113761 1 Bool.false 441837962

noncomputable def hp770850 := hp770849 Bool.true Bool.false 486442453 Bool.true Bool.true 229401379 221285 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 441837962 536870912) BSN.abs_quadSignNeg

noncomputable def hp770851 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp770852 := hp770851 BSN.quadSignNeg 7 8 9 912007 1000 52 121 536870912 268435456 9007199254740992

noncomputable def hp770853 := hp770852 Bool.false 973607152733 4155 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp770854 := hp770853 Bool.false 64592312 155144 Bool.true 697497981 Bool.true 178871584 28296951008113761 1 Bool.false 144030674

noncomputable def hp770855 := hp770854 Bool.false Bool.false 175580626 Bool.true Bool.false 56987971 189966 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 144030674 536870912) BSN.abs_quadSignNeg

noncomputable def hp770856 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp770857 := hp770856 BSN.quadSignPos 5 6 7 912007 1000 114 24 536870912 268435456 9007199254740992

noncomputable def hp770858 := hp770857 Bool.false 973607152733 4155 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp770859 := hp770858 Bool.false 181166159 115289 Bool.false 170023387 Bool.false 591565866 28296951008113761 1 Bool.false 510172548

noncomputable def hp770860 := hp770859 Bool.true Bool.false 242623920 Bool.false Bool.false 64592312 155144 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 510172548 536870912) BSN.abs_quadSignPos

noncomputable def hp770861 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp770862 := hp770861 BSN.quadSignPos 3 4 5 912007 1000 349 220 536870912 268435456 9007199254740992

noncomputable def hp770863 := hp770862 Bool.false 973607152733 4155 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp770864 := hp770863 Bool.false 162968970 68140 Bool.false 518931127 Bool.false 48765665 28296951008113761 1 Bool.false 441817998

noncomputable def hp770865 := hp770864 Bool.true Bool.false 534657665 Bool.false Bool.false 181166159 115289 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 349 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 441817998 536870912) BSN.abs_quadSignPos

noncomputable def hp770866 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp770867 := hp770866 BSN.quadSignPos 1 2 3 912007 1000 752 516 536870912 268435456 9007199254740992

noncomputable def hp770868 := hp770867 Bool.false 973607152733 4155 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp770869 := hp770868 Bool.true 379518368 4210 Bool.false 48719578 Bool.false 543123959 28296951008113761 1 Bool.false 534661843

noncomputable def hp770870 := hp770869 Bool.false Bool.false 284791278 Bool.false Bool.false 162968970 68140 BSN.abs_quadSignPos (BSN.cos_quad_nat0 752 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 534661843 536870912) BSN.abs_quadSignPos

noncomputable def hp770871 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) 1) Bool.true

noncomputable def hp770872 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)))

noncomputable def hp770873 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000))) Bool.true 47439796 67108864

noncomputable def hp770874 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 121700894091) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 121700894091 67108864

noncomputable def hp770875 := nat_lit 169186450374215110366369972190098601982602960276260584630361

noncomputable def hp770876 := nat_lit 93293566769105377134769425138198986432867655739244544000

noncomputable def hp770877 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) Bool.false hp770875 hp770876 1394266379386660539

noncomputable def hp770878 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912007 4000) (Real.log (Enclosure.sfrac Bool.false 3327028072196 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1824014))))))

noncomputable def hp770879 := nat_lit 302853381164035608699737188867360000

noncomputable def hp770880 := nat_lit 1657226654023442640358066759954862349120

noncomputable def hp770881 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp770878 (Enclosure.sfrac Bool.false 912007 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912007 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp770879 hp770880)) Bool.false

noncomputable def hp770882 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 912007 1000) 912007 1000 3327028072196 16000000 1824014

noncomputable def hp770883 := hp770882 4000 2000 hp770879 hp770880 (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl rfl rfl rfl

noncomputable def hp770884 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp770878 (Enclosure.sfrac Bool.false 912007 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912007 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp770879 hp770880) 32668838293198541400721 18014398509481984000

noncomputable def hp770885 := nat_lit 54139664119748835317238391100831552634432947288403387081715520

noncomputable def hp770886 := @hp770884 1394266379386660539 180224000000000000000000 hp770879 hp770880 0 1 hp770885 hp770875 hp770876 1394266379386660539 180224000000000000000000

noncomputable def hp770887 := @Enclosure.Real.IsNear.subLit_ff_p (hp770878 (Enclosure.sfrac Bool.false 912007 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912007 2000) (Real.log Real.pi)) 42072369320509470386833 18014398509481984000 116162670550809 44000000000000000000

noncomputable def hp770888 := nat_lit 2192368626056253039859355090944000

noncomputable def hp770889 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912007 4000) (Real.log (Enclosure.sfrac Bool.false 3327028072196 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1824014))))))

noncomputable def hp770890 := @hp770889 (Enclosure.sfrac Bool.false 912007 2000) 50286998091228038277777 18014398509481984000 116162670550809 44000000000000000000 912007 2000 0

noncomputable def hp770891 := nat_lit 84144738641018940773666000

noncomputable def hp770892 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912007 4000) (Real.log (Enclosure.sfrac Bool.false 3327028072196 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1824014))))) 50294069860044960157777

noncomputable def hp770893 := nat_lit 113236252932617718402272921429471133696

noncomputable def hp770894 := @hp770892 18014398509481984000 11400104383985591 4356000000000000000000 883971102115235 2251799813685248 200000001089 8712000000000000000 hp770893 50286998091228038277777 18014398509481984000 116162670550809

noncomputable def hp770895 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 912007 4000) (Real.log (Enclosure.sfrac Bool.false 3327028072196 16000000)) 912007 4000 0 1 55146583151275111 4503599627370496

noncomputable def hp770896 := nat_lit 118426385560435611221884928

noncomputable def hp770897 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3327028072196) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp770896 hp617687

noncomputable def hp770898 := BSN.log_rat_reduce_isNear 3327028072196 16000000 17 6654056144392 4194304000000 123882748 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp770899 := nat_lit 87655068184887682945879274789096937772741840388352905415323484781506076943610916144206846993757748879300607688139819310948576268113753628343971015773294428160

noncomputable def hp770900 := nat_lit 1550247859891206960821289078804026977185848144487073964518926698853546242019684851554230344929317032070145295701577944457549181654385272826373041104567140352

noncomputable def hp770901 := nat_lit 124497525631672862828530605986162045095674089264994354225752730670885673982504771843012484192297827215533172271594429507104764029839449369140862648320

noncomputable def hp770902 := BSN.log_dyadic_bound 1229876072196 5424180072196 7 6 hp770899 268435456 87120000 hp770900 hp770901 123882748 6654056144392

noncomputable def hp770903 := hp770902 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp770904 := @BSN.binarySplit_of_base6 (BSN.artanhP 1229876072196) (BSN.artanhQ 5424180072196) 0 6 hp770900 hp770899 hp770901 rfl rfl rfl

noncomputable def hp770905 := hp770898 rfl rfl rfl rfl (hp770903 (hp770904 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp770906 := @hp770895 12500018513 1089000000000000000 50294069860044960157777 18014398509481984000 11400104383985591 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 912007 4000) (BSN.isNear_log_sfrac 3327028072196 16000000 55146583151275111 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp770897 1000001481040000 87120000000000000000000 55146583151275111 4503599627370496 12500018513 1089000000000000000 (hp770905 rfl rfl rfl) rfl)) rfl

noncomputable def hp770907 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1824014)))) 1 4

noncomputable def hp770908 := @hp770907 0 1 883971102115235 562949953421312 200000001089 2178000000000000000 883971102115235 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp770909 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1824014))) 884279719003555 562949953421312 1

noncomputable def hp770910 := @hp770909 2000000000000000 18395 33554432 1 10890000 29661148235890708971520 883971102115235 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp770911 := BSN.arctan_dyadic_bound_f 1000 1824014 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp770912 := hp770911 1 18395 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1824014) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1824014) 0 0 rfl)

noncomputable def hp770913 := hp770908 (hp770910 (hp770912 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp770914 := @hp770887 35030882907327 67108864000 2736021 536870912000 hp770888 32668838293198541400721 18014398509481984000 1394266379386660539 180224000000000000000000 (@hp770890 1 hp770891 42072369320509470386833 18014398509481984000 116162670550809 44000000000000000000 (@hp770894 44000000000000000000 hp770906 hp770913 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 912007 2000) rfl rfl)

noncomputable def hp770915 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 912007 2000) (Real.log Real.pi) 912007 2000 0 1 38410761 33554432

noncomputable def hp770916 := hp770914 (@hp770915 3 268435456 35030882907327 67108864000 2736021 536870912000 (Enclosure.Real.IsNear.const Bool.false 912007 2000) hd4909 rfl) rfl

noncomputable def hp770917 := @hp770877 180224000000000000000000 121700894091 67108864 65 8388608 (@hp770881 hp770875 hp770876 1394266379386660539 180224000000000000000000 (hp770883 rfl rfl rfl rfl rfl) (hp770886 (hp770916 rfl) (Enclosure.Real.IsNear.const Bool.true hp770879 hp770880) rfl rfl)) rfl

noncomputable def hp770918 := nat_lit 7598622618943346937167872

noncomputable def hp770919 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 121700894091) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp770918) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp770920 := BSN.sin_reduce_arg_pos_rat_q2 121700894091 67108864 226375608064910080 72057594037927936 288 hp770918 hp617687 rfl rfl rfl rfl

noncomputable def hp770921 := nat_lit 81520612752867808076820873453039075663663994396801947074689404131327042601139741840240167361

noncomputable def hp770922 := nat_lit 18485900205100310623089088495048707434992743418690322764979782261295178815508946711366081

noncomputable def hp770923 := nat_lit 244524866458193223609216442182127129576121997703568460578538252829458537445788207627297769921

noncomputable def hp770924 := BSN.cos_dyadic_bound_f 107982922073 137438953472 3 2 67108864 21801270 hp770921 hp746621 hp770922 hp770923 hp746624

noncomputable def hp770925 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 107982922073) (BSN.cosEvenQ 137438953472) 0 2 hp770921 hp746621 hp770922 rfl rfl rfl

noncomputable def hp770926 := hp770924 hp770922 47439796 rfl rfl rfl rfl rfl rfl rfl rfl (hp770925 rfl)

noncomputable def hp770927 := @BSN.binarySplit_of_base2 (BSN.cosOddP 107982922073) (BSN.cosOddQ 137438953472) 0 2 hp770923 hp746624 hp770922 rfl rfl rfl

noncomputable def hp770928 := @BSN.cos_arg_round Bool.false 47439796 67108864 hp770918 hp617687 107982922073 137438953472 21801270 21780000 (hp770926 (hp770927 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770929 := hp770919 47439796 67108864 288 1000000000000000 21780000 10890000 hp770920 BSN.pi_near_15 hp770928 rfl rfl

noncomputable def hp770930 := @hp770874 65 8388608 Bool.true 47439796 67108864 1 10890000 hp770917 (Enclosure.sfrac_false_div 121700894091 67108864) (hp770929 rfl rfl) rfl

noncomputable def hp770931 := @hp770871 11859949 16777216 44764913 5709496320000 379518368 536870912 4210 536870912 (@hp770872 Bool.true 11859949 16777216 44764913 5709496320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000)) (@hp770873 716238608 91351941120000 11859949 16777216 44764913 5709496320000 (hp770930 rfl) rfl))

noncomputable def hp770932 := @hp770877 180224000000000000000000 973607152733 536870912 4155 536870912 (@hp770881 hp770875 hp770876 1394266379386660539 180224000000000000000000 (hp770883 rfl rfl rfl rfl rfl) (hp770886 (hp770916 rfl) (Enclosure.Real.IsNear.const Bool.true hp770879 hp770880) rfl rfl)) rfl

noncomputable def hp770933 := hp770870 (BSN.cos_quad_nat0 516 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 284791278 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl rfl (hp770931 rfl) hp770932

noncomputable def hp770934 := nat_lit 5633964049987900055471127671056

noncomputable def hp770935 := BSN.cos_dyadic_bound_f 48719578 536870912 2 1 536870912 268435456 hp770934 hp708767 hp770934 hp770934 hp708768

noncomputable def hp770936 := @BSN.binarySplit_of_base (BSN.cosEvenP 48719578) (BSN.cosEvenQ 536870912) 0 1 hp770934 hp708767 hp770934 rfl rfl rfl

noncomputable def hp770937 := hp770935 hp770934 534661843 rfl rfl rfl rfl rfl rfl rfl rfl (hp770936 rfl)

noncomputable def hp770938 := @BSN.binarySplit_of_base (BSN.cosOddP 48719578) (BSN.cosOddQ 536870912) 0 1 hp770934 hp708768 hp770934 rfl rfl rfl

noncomputable def hp770939 := nat_lit 11993647091229532770616443596099623800804618835238557107987041921631637759137727363245540403669387120491835457761

noncomputable def hp770940 := nat_lit 658851496362748399563230626263152346984863642164671957364877026817685773624533386945221270093998345978081

noncomputable def hp770941 := nat_lit 72731232060364235850485794915129383439153223702447003592557645703160727858976773788945303628096656324954971996385

noncomputable def hp770942 := BSN.cos_dyadic_bound_f 543123959 536870912 4 3 536870912 268435456 hp770939 hp716712 hp770940 hp770941 hp716714

noncomputable def hp770943 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 543123959) (BSN.cosEvenQ 536870912) 0 3 hp770939 hp716712 hp770940 rfl rfl rfl

noncomputable def hp770944 := hp770942 hp770940 284791278 rfl rfl rfl rfl rfl rfl rfl rfl (hp770943 rfl)

noncomputable def hp770945 := @BSN.binarySplit_of_base3 (BSN.cosOddP 543123959) (BSN.cosOddQ 536870912) 0 3 hp770941 hp716714 hp770940 rfl rfl rfl

noncomputable def hp770946 := hp770933 hd4911 hd4913 hd4915 hd4917 hd4918 (hp770937 (hp770938 rfl) rfl rfl rfl rfl) (hp770944 (hp770945 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770947 := hp770865 (BSN.cos_quad_nat0 220 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 534657665 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl rfl (hp770946 rfl rfl rfl rfl rfl) hp770932

noncomputable def hp770948 := nat_lit 18223236585928031762865521605546130241845780282225862952535149930649104705

noncomputable def hp770949 := nat_lit 5258692468950484518971918810276575555852231199242452913076200551362881

noncomputable def hp770950 := nat_lit 47719010318195115737331363955499417130124711412459438999542316922235924801

noncomputable def hp770951 := BSN.sin_dyadic_bound_f 518931127 536870912 3 2 536870912 268435456 hp770948 hp708845 hp770949 hp770950 hp708848

noncomputable def hp770952 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 518931127) (BSN.sinEvenQ 536870912) 0 2 hp770948 hp708845 hp770949 rfl rfl rfl

noncomputable def hp770953 := hp770951 hp770949 441817998 rfl rfl rfl rfl rfl rfl rfl rfl (hp770952 rfl)

noncomputable def hp770954 := @BSN.binarySplit_of_base2 (BSN.sinOddP 518931127) (BSN.sinOddQ 536870912) 0 2 hp770950 hp708848 hp770949 rfl rfl rfl

noncomputable def hp770955 := nat_lit 5655312442350349571620965450625

noncomputable def hp770956 := BSN.cos_dyadic_bound_f 48765665 536870912 2 1 536870912 268435456 hp770955 hp708767 hp770955 hp770955 hp708768

noncomputable def hp770957 := @BSN.binarySplit_of_base (BSN.cosEvenP 48765665) (BSN.cosEvenQ 536870912) 0 1 hp770955 hp708767 hp770955 rfl rfl rfl

noncomputable def hp770958 := hp770956 hp770955 534657665 rfl rfl rfl rfl rfl rfl rfl rfl (hp770957 rfl)

noncomputable def hp770959 := @BSN.binarySplit_of_base (BSN.cosOddP 48765665) (BSN.cosOddQ 536870912) 0 1 hp770955 hp708768 hp770955 rfl rfl rfl

noncomputable def hp770960 := hp770947 hd4920 hd4922 hd4924 hd4926 hd4918 (hp770953 (hp770954 rfl) rfl rfl rfl rfl) (hp770958 (hp770959 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770961 := hp770860 (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 242623920 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl rfl (hp770960 rfl rfl rfl rfl rfl) hp770932

noncomputable def hp770962 := nat_lit 116634231659133326198975573409848642266738283897359118771893878101541601

noncomputable def hp770963 := nat_lit 698343841103771611234142934247841409859264102033549138433350468321

noncomputable def hp770964 := nat_lit 349901298289717771053704251943677431117395133163873289217404767603688161

noncomputable def hp770965 := BSN.cos_dyadic_bound_f 170023387 536870912 3 2 536870912 268435456 hp770962 hp708868 hp770963 hp770964 hp708870

noncomputable def hp770966 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 170023387) (BSN.cosEvenQ 536870912) 0 2 hp770962 hp708868 hp770963 rfl rfl rfl

noncomputable def hp770967 := hp770965 hp770963 510172548 rfl rfl rfl rfl rfl rfl rfl rfl (hp770966 rfl)

noncomputable def hp770968 := @BSN.binarySplit_of_base2 (BSN.cosOddP 170023387) (BSN.cosOddQ 536870912) 0 2 hp770964 hp708870 hp770963 rfl rfl rfl

noncomputable def hp770969 := nat_lit 16884107028764117763728568434991014832052563335129024730455589430085752483155120568868975671199981905946978881536

noncomputable def hp770970 := nat_lit 1836696004968349350789659572931412043940587678495846863266073361173319610501450384556113385324344428793856

noncomputable def hp770971 := nat_lit 102370374081202889422563148142840592883479704251529295893397929493531740448485883700089174123381516691561856962560

noncomputable def hp770972 := BSN.cos_dyadic_bound_f 591565866 536870912 4 3 536870912 268435456 hp770969 hp716712 hp770970 hp770971 hp716714

noncomputable def hp770973 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 591565866) (BSN.cosEvenQ 536870912) 0 3 hp770969 hp716712 hp770970 rfl rfl rfl

noncomputable def hp770974 := hp770972 hp770970 242623920 rfl rfl rfl rfl rfl rfl rfl rfl (hp770973 rfl)

noncomputable def hp770975 := @BSN.binarySplit_of_base3 (BSN.cosOddP 591565866) (BSN.cosOddQ 536870912) 0 3 hp770971 hp716714 hp770970 rfl rfl rfl

noncomputable def hp770976 := hp770961 hd4928 hd4930 hd4932 hd4934 hd4918 (hp770967 (hp770968 rfl) rfl rfl rfl rfl) (hp770974 (hp770975 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770977 := hp770855 (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 175580626 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl rfl (hp770976 rfl rfl rfl rfl rfl) hp770932

noncomputable def hp770978 := nat_lit 32658225173233248252466705058065985181202942058450427682852761710869697917454191412484710599362351863372005971441

noncomputable def hp770979 := nat_lit 13259143103515329368662583035845693792667260231837094593238039784662455629497378886219724321140894910322161

noncomputable def hp770980 := nat_lit 197902885149253700343639687399741817821641986904169838953113848134153871602494577869987500674332259192234345960945

noncomputable def hp770981 := BSN.cos_dyadic_bound_f 697497981 536870912 4 3 536870912 268435456 hp770978 hp716712 hp770979 hp770980 hp716714

noncomputable def hp770982 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 697497981) (BSN.cosEvenQ 536870912) 0 3 hp770978 hp716712 hp770979 rfl rfl rfl

noncomputable def hp770983 := hp770981 hp770979 144030674 rfl rfl rfl rfl rfl rfl rfl rfl (hp770982 rfl)

noncomputable def hp770984 := @BSN.binarySplit_of_base3 (BSN.cosOddP 697497981) (BSN.cosOddQ 536870912) 0 3 hp770980 hp716714 hp770979 rfl rfl rfl

noncomputable def hp770985 := nat_lit 1023682812577090599575282579931136

noncomputable def hp770986 := BSN.sin_dyadic_bound_f 178871584 536870912 2 1 536870912 268435456 hp770985 hp708890 hp770985 hp770985 hp708891

noncomputable def hp770987 := @BSN.binarySplit_of_base (BSN.sinEvenP 178871584) (BSN.sinEvenQ 536870912) 0 1 hp770985 hp708890 hp770985 rfl rfl rfl

noncomputable def hp770988 := hp770986 hp770985 175580626 rfl rfl rfl rfl rfl rfl rfl rfl (hp770987 rfl)

noncomputable def hp770989 := @BSN.binarySplit_of_base (BSN.sinOddP 178871584) (BSN.sinOddQ 536870912) 0 1 hp770985 hp708891 hp770985 rfl rfl rfl

noncomputable def hp770990 := hp770977 hd4936 hd4938 hd4940 hd4942 hd4918 (hp770983 (hp770984 rfl) rfl rfl rfl rfl) (hp770988 (hp770989 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp770991 := hp770850 (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 486442453 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl rfl (hp770990 rfl rfl rfl rfl rfl) hp770932

noncomputable def hp770992 := nat_lit 1544796410603583884678580715022967717773919654249187664461505128609505536

noncomputable def hp770993 := nat_lit 122488713053133273175239690290317515309429010554246114371504559513856

noncomputable def hp770994 := nat_lit 4634144254384645387489391665688322518291140104726454501155772376709488896

noncomputable def hp770995 := BSN.cos_dyadic_bound_f 324348586 536870912 3 2 536870912 268435456 hp770992 hp708868 hp770993 hp770994 hp708870

noncomputable def hp770996 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 324348586) (BSN.cosEvenQ 536870912) 0 2 hp770992 hp708868 hp770993 rfl rfl rfl

noncomputable def hp770997 := hp770995 hp770993 441837962 rfl rfl rfl rfl rfl rfl rfl rfl (hp770996 rfl)

noncomputable def hp770998 := @BSN.binarySplit_of_base2 (BSN.cosOddP 324348586) (BSN.cosOddQ 536870912) 0 2 hp770994 hp708870 hp770993 rfl rfl rfl

noncomputable def hp770999 := nat_lit 34520619780640682162256119431088018444006668316581722364829236549716640000

noncomputable def hp771000 := nat_lit 18860791169478051179323110853137988008456054079345488225444240100000000

noncomputable def hp771001 := nat_lit 90380610525498822151618551568611158229908535789204618260282995527191200000

noncomputable def hp771002 := BSN.sin_dyadic_bound_f 608758430 536870912 3 2 536870912 268435456 hp770999 hp708845 hp771000 hp771001 hp708848

noncomputable def hp771003 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 608758430) (BSN.sinEvenQ 536870912) 0 2 hp770999 hp708845 hp771000 rfl rfl rfl

noncomputable def hp771004 := hp771002 hp771000 486442453 rfl rfl rfl rfl rfl rfl rfl rfl (hp771003 rfl)

noncomputable def hp771005 := @BSN.binarySplit_of_base2 (BSN.sinOddP 608758430) (BSN.sinOddQ 536870912) 0 2 hp771001 hp708848 hp771000 rfl rfl rfl

noncomputable def hp771006 := hp770991 hd4944 hd4946 hd4961 hd4963 hd4918 (hp770997 (hp770998 rfl) rfl rfl rfl rfl) (hp771004 (hp771005 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771007 := hp770845 498917953 Bool.false Bool.true 85376167 235922 BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 498917953 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl (hp771006 rfl rfl rfl rfl rfl)

noncomputable def hp771008 := nat_lit 237385509030155651983496696190244372361389896814417809571904261032247296

noncomputable def hp771009 := nat_lit 2892812373208330813106725465596834303735278865060680071919976841216

noncomputable def hp771010 := nat_lit 712150741465720539288863875119801923415562219885523307355568943143059456

noncomputable def hp771011 := BSN.cos_dyadic_bound_f 203079008 536870912 3 2 536870912 268435456 hp771008 hp708868 hp771009 hp771010 hp708870

noncomputable def hp771012 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 203079008) (BSN.cosEvenQ 536870912) 0 2 hp771008 hp708868 hp771009 rfl rfl rfl

noncomputable def hp771013 := hp771011 hp771009 498917953 rfl rfl rfl rfl rfl rfl rfl rfl (hp771012 rfl)

noncomputable def hp771014 := @BSN.binarySplit_of_base2 (BSN.cosOddP 203079008) (BSN.cosOddQ 536870912) 0 2 hp771010 hp708870 hp771009 rfl rfl rfl

noncomputable def hp771015 := hp771007 hp770932 hd5088 hd5090 hd4918 (hp771013 (hp771014 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp771016 := @hp770840 Bool.true 85376167 268435456 117961 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912007 1000)) (Enclosure.sfrac Bool.false 912007 1000) 12) (@hp770842 117961 134217728 (hp771015 rfl rfl rfl) (hp771015 rfl rfl rfl) rfl rfl)

noncomputable def hp771017 := @Enclosure.Real.IsNear.mulLit_ff hp770831 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1))) 1208385 4194304 1

noncomputable def hp771018 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp770830 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp771019 := @hp771018 1 1 0 1 1208385 4194304 1 33554432 1208385 4194304 1

noncomputable def hp771020 := @Enclosure.Real.IsNear.of_eq (hp770830 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp771021 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 912007 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771022 := @hp771020 (@Inv.inv Real Real.instInv (Real.sqrt hp770832)) Bool.false 1208385 4194304 1 33554432 (hp771021 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 912007 1000) 912007 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000))))

noncomputable def hp771023 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp770832)) Bool.false 19334160 67108864 2 67108864 1208385 4194304

noncomputable def hp771024 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp770832) Bool.false 232934844 67108864 6 67108864 58233711 16777216 3 33554432

noncomputable def hp771025 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 912007 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771026 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 912007 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771027 := @hp771026 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912007 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9740879548949

noncomputable def hp771028 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 912007 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 912007 1000 0

noncomputable def hp771029 := @hp771028 1 10680707 67108864 1 67108864 9740879548949 67108864000 912007 67108864000 (Enclosure.Real.IsNear.const Bool.false 912007 1000) hd4949

noncomputable def hp771030 := @hp771027 67108864000 912007 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 912007 1000) 912007 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000))) (hp771029 rfl)

noncomputable def hp771031 := @hp771025 9740879548949 67108864000 912007 67108864000 404258364 404258402 33554432 hp771030 rfl rfl rfl

noncomputable def hp771032 := @Enclosure.Real.IsNear.recentre' hp770832 Bool.false 808516766 67108864 38 67108864 404258383 33554432 19 33554432 (hp771031 rfl rfl rfl)

noncomputable def hp771033 := @Enclosure.Real.IsNear.sqrt_image hp770832 404258383 33554432 19 33554432 116467419 116467425 33554432 (hp771032 rfl) rfl rfl

noncomputable def hp771034 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp770832) 58233711 16777216 3 33554432 9667079 9667081 33554432 (hp771024 (hp771033 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp771035 := @hp771019 33554432 (@hp769737 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (hp771022 (@hp771023 1 33554432 (hp771034 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp771036 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp771037 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp771038 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1))) (hp771036 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771037 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp771039 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 912007 1000) 912007 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl

noncomputable def hp771040 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp771041 := @hp771040 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771037 (Enclosure.sfrac Bool.false 1 16)))) 70258909

noncomputable def hp771042 := @hp771041 67108864 271 67108864 13057113 16777216 91259027 22837985280000 917378514069717 1125899906842624 1122853706892661 153263124818952192000

noncomputable def hp771043 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp771044 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)))) 32050025

noncomputable def hp771045 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)))) Bool.false

noncomputable def hp771046 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 20171525) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp771047 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1))) Bool.false 1419444920664787482445

noncomputable def hp771048 := nat_lit 512735432785625418065354181

noncomputable def hp771049 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)) 884279719003555 140737488355328 1

noncomputable def hp771050 := @Enclosure.Real.IsNear.subLit_ff_p hp770832 (Enclosure.sfrac Bool.false 12 1) 404258383 33554432 19 33554432 12 1 0

noncomputable def hp771051 := @hp771049 500000000000000 1605199 33554432 19 33554432 1419444920664787482445 4722366482869645213696 hp771048 hp682805 hd4948 (@hp771050 1 1605199 1605199 33554432 19 33554432 (hp771032 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771052 := @hp771046 20171525 67108864 15 4194304 Bool.false 32050025 33554432 1 10890000 (@hp771047 4722366482869645213696 hp771048 hp682805 20171525 67108864 15 4194304 (hp771051 rfl) rfl) (Enclosure.sfrac_false_div 20171525 67108864)

noncomputable def hp771053 := nat_lit 165559814559654206706656640625

noncomputable def hp771054 := BSN.cos_dyadic_bound_f 20171525 67108864 2 1 33554432 10890000 hp771053 hp740060 hp771053 hp771053 hp740061

noncomputable def hp771055 := @BSN.binarySplit_of_base (BSN.cosEvenP 20171525) (BSN.cosEvenQ 67108864) 0 1 hp771053 hp740060 hp771053 rfl rfl rfl

noncomputable def hp771056 := hp771054 hp771053 32050025 rfl rfl rfl rfl rfl rfl rfl rfl (hp771055 rfl)

noncomputable def hp771057 := @BSN.binarySplit_of_base (BSN.cosOddP 20171525) (BSN.cosOddQ 67108864) 0 1 hp771053 hp740061 hp771053 rfl rfl rfl

noncomputable def hp771058 := hp771052 (hp771056 (hp771057 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp771059 := @hp771044 33554432 10471519 2854748160000 35129319 35129590 33554432 (@hp771045 32050025 33554432 167544304 45675970560000 32050025 33554432 10471519 2854748160000 hp771058 rfl)

noncomputable def hp771060 := @hp771043 Bool.false 70258909 67108864 271 67108864 70258909 67108864 271 67108864 (hp771059 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp771061 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771037 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp771062 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771037 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 5695017)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true

noncomputable def hp771063 := nat_lit 107575829829043579054086310205

noncomputable def hp771064 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771037 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp771063

noncomputable def hp771065 := nat_lit 18850640763851230392273864787231029

noncomputable def hp771066 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771037 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp771067 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp771068 := @hp771067 (Enclosure.sfrac Bool.false 1 16) 51284876862367 1125899906842624 698532131 1125899906842624 1 16 0

noncomputable def hp771069 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)) 2576663829601

noncomputable def hp771070 := @hp771069 1125899906842624 60997923 1125899906842624 1605199 33554432 19 33554432 1720834913306666860544 51284876862367 1125899906842624 698532131

noncomputable def hp771071 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)) 1605199 33554432 19

noncomputable def hp771072 := @hp771071 33554432 1605199 33554432 19 33554432 2576663829601 1125899906842624 60997923 1125899906842624 (@hp771050 1 1605199 1605199 33554432 19 33554432 (hp771032 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771073 := hp771072 (@hp771050 1 1605199 1605199 33554432 19 33554432 (hp771032 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771074 := @hp771070 1125899906842624 (hp771073 rfl) (@hp771050 1 1605199 1605199 33554432 19 33554432 (hp771032 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771075 := @hp771066 500000000000000 121653621040031 1125899906842624 698532131 1125899906842624 hp771063 hp682141 hp771065 hp682143 hd4948 (@hp771068 1 1946457936640496 121653621040031 1125899906842624 698532131 1125899906842624 (hp771074 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp771076 := @hp771062 5695017 8388608 131 33554432 Bool.false 26114226 33554432 1 10890000 (@hp771064 hp682141 hp771065 hp682143 5695017 8388608 131 33554432 (hp771075 rfl) rfl) (Enclosure.sfrac_true_div 5695017 8388608)

noncomputable def hp771077 := nat_lit 8751931184123644619008166576990355013027257660325178208321

noncomputable def hp771078 := nat_lit 1106522370647888567826017859721650851077432891217637441

noncomputable def hp771079 := nat_lit 26253580507629638079888847695251621737379618115193099350081

noncomputable def hp771080 := BSN.cos_dyadic_bound_f 5695017 8388608 3 2 33554432 10890000 hp771077 hp630724 hp771078 hp771079 hp630727

noncomputable def hp771081 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 5695017) (BSN.cosEvenQ 8388608) 0 2 hp771077 hp630724 hp771078 rfl rfl rfl

noncomputable def hp771082 := hp771080 hp771078 26114226 rfl rfl rfl rfl rfl rfl rfl rfl (hp771081 rfl)

noncomputable def hp771083 := @BSN.binarySplit_of_base2 (BSN.cosOddP 5695017) (BSN.cosOddQ 8388608) 0 2 hp771079 hp630727 hp771078 rfl rfl rfl

noncomputable def hp771084 := hp771076 (BSN.cos_neg_of_bound 5695017 8388608 Bool.false 26114226 33554432 1 10890000 (hp771082 (hp771083 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp771085 := hp771042 hp771060 (@hp771061 26114226 33554432 1460144432 365407764480000 13057113 16777216 91259027 22837985280000 (hp771084 rfl) rfl)

noncomputable def hp771086 := @hp771017 33554432 917378514069717 1125899906842624 1122853706892661 153263124818952192000 1108546435724134977045 4722366482869645213696 5489797942954676209583 hp754729 (hp771035 rfl) (@hp771038 Bool.false 917378514069717 1125899906842624 1122853706892661 153263124818952192000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp770832 (Enclosure.sfrac Bool.false 12 1)) (hp771039 rfl (hp770835 rfl rfl))) (hp771085 rfl))

noncomputable def hp771087 := @hp770829 hp770827 hp754729 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912007 1000))) (@hp770834 hp770827 hp754729 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 912007 1000) 12 (hp770835 rfl rfl)) (@hp770838 hp770827 hp754729 hp771016 (hp771086 rfl) rfl rfl))

theorem hd5096 : hp770828 hp754729 := hp771087

noncomputable def hp771088 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912638 1000)) Bool.false 2146514721796653684545 9444732965739290427392 1133571679730292553833161

noncomputable def hp771089 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912638 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912638 1000)) Bool.false 2146514721796653684545 9444732965739290427392

noncomputable def hp771090 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 912638 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771091 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp771090 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp771092 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 912638 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771093 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp771091 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp771094 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912638 1000)) hp771093 Bool.false 2146514721796653684545 9444732965739290427392

noncomputable def hp771095 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 912638 1000) 912638 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl

noncomputable def hp771096 := @Enclosure.Real.IsNear.subLit_ff_p (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp771091 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp771097 := nat_lit 72025082269524733885614653440

noncomputable def hp771098 := @hp771096 15415235 33554432 236087 268435456 2192488190817635559615 9444732965739290427392 2839450069918611561161 hp764965 hp771097 2146514721796653684545 9444732965739290427392

noncomputable def hp771099 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) 12)

noncomputable def hp771100 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) 12) hp771099

noncomputable def hp771101 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) 12)

noncomputable def hp771102 := @hp771101 123321880 536870912 236087 536870912 123321880 536870912 236087 536870912 132415860370309120 15415235 33554432

noncomputable def hp771103 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) Real.cos BSN.quadSignPos 11

noncomputable def hp771104 := hp771103 12 912638 1000 288 536870912 268435456 9007199254740992 Bool.false 974450359876 4157 1334074092

noncomputable def hp771105 := hp771104 51 154981288 8 Bool.true 20852773 221440 Bool.true 201672617 28296951008113761 1 Bool.false

noncomputable def hp771106 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp771107 := hp771106 BSN.quadSignNeg 9 10 11 912638 1000 182 237 536870912 268435456 9007199254740992

noncomputable def hp771108 := hp771107 Bool.false 974450359876 4157 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp771109 := hp771108 Bool.false 271711654 190100 Bool.true 261177936 Bool.true 577875586 28296951008113761 1 Bool.false 474584836

noncomputable def hp771110 := hp771109 Bool.true Bool.false 472577653 Bool.true Bool.true 20852773 221440 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 474584836 536870912) BSN.abs_quadSignNeg

noncomputable def hp771111 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp771112 := hp771111 BSN.quadSignNeg 7 8 9 912638 1000 52 121 536870912 268435456 9007199254740992

noncomputable def hp771113 := hp771112 Bool.false 974450359876 4157 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp771114 := hp771113 Bool.false 202313967 155254 Bool.true 558733985 Bool.true 80008414 28296951008113761 1 Bool.false 271440043

noncomputable def hp771115 := hp771114 Bool.false Bool.false 79712589 Bool.true Bool.false 271711654 190100 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 271440043 536870912) BSN.abs_quadSignNeg

noncomputable def hp771116 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp771117 := hp771116 BSN.quadSignPos 5 6 7 912638 1000 114 24 536870912 268435456 9007199254740992

noncomputable def hp771118 := hp771117 Bool.false 974450359876 4157 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp771119 := hp771118 Bool.false 336141337 115372 Bool.false 406244161 Bool.false 775565706 28296951008113761 1 Bool.false 390365952

noncomputable def hp771120 := hp771119 Bool.true Bool.false 67569480 Bool.false Bool.false 202313967 155254 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 390365952 536870912) BSN.abs_quadSignPos

noncomputable def hp771121 := hp771116 BSN.quadSignPos 3 4 5 912638 1000 350 220 536870912 268435456 9007199254740992

noncomputable def hp771122 := hp771121 Bool.false 974450359876 4157 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp771123 := hp771122 Bool.false 411716144 68191 Bool.false 49194657 Bool.false 346750705 28296951008113761 1 Bool.false 534618581

noncomputable def hp771124 := hp771123 Bool.true Bool.false 428731314 Bool.false Bool.false 336141337 115372 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 350 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 534618581 536870912) BSN.abs_quadSignPos

noncomputable def hp771125 := hp771111 BSN.quadSignNeg 1 2 3 912638 1000 752 517 536870912 268435456 9007199254740992

noncomputable def hp771126 := hp771125 Bool.false 974450359876 4157 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp771127 := hp771126 Bool.false 379655568 4218 Bool.false 657112348 Bool.false 170844257 28296951008113761 1 Bool.false 182491831

noncomputable def hp771128 := hp771127 Bool.false Bool.false 167975386 Bool.true Bool.false 411716144 68191 BSN.abs_quadSignPos (BSN.cos_quad_nat0 752 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 182491831 536870912) BSN.abs_quadSignNeg

noncomputable def hp771129 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) 1) Bool.false

noncomputable def hp771130 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)))

noncomputable def hp771131 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000))) Bool.false 47456946 67108864

noncomputable def hp771132 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 15225786873) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 15225786873 8388608

noncomputable def hp771133 := nat_lit 265683035806756134400470020211582343338114510376151455481

noncomputable def hp771134 := nat_lit 146377383199452605323159187091219390135561159809433600

noncomputable def hp771135 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) Bool.false hp771133 hp771134 69063795046264019737

noncomputable def hp771136 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912638 4000) (Real.log (Enclosure.sfrac Bool.false 3331633476176 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1825276))))))

noncomputable def hp771137 := nat_lit 303902523580960447777677249520640000

noncomputable def hp771138 := nat_lit 1664118180991097293862812729130603089920

noncomputable def hp771139 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp771136 (Enclosure.sfrac Bool.false 912638 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912638 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp771137 hp771138)) Bool.false

noncomputable def hp771140 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 912638 1000) 912638 1000 3331633476176 16000000 1825276

noncomputable def hp771141 := hp771140 4000 2000 hp771137 hp771138 (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl rfl rfl rfl

noncomputable def hp771142 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp771136 (Enclosure.sfrac Bool.false 912638 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912638 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp771137 hp771138) 3269713162765807021989 1801439850948198400

noncomputable def hp771143 := nat_lit 5441188573322365632521626013933206391564585172503581808250880

noncomputable def hp771144 := @hp771142 69063795046264019737 hp739631 hp771137 hp771138 0 1 hp771143 hp771133 hp771134 69063795046264019737 hp739631

noncomputable def hp771145 := @Enclosure.Real.IsNear.subLit_ff_p (hp771136 (Enclosure.sfrac Bool.false 912638 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912638 2000) (Real.log Real.pi)) 21053584388085039509049 9007199254740992000 5753995948105897 2178000000000000000000

noncomputable def hp771146 := nat_lit 548566839897651018222262026240000

noncomputable def hp771147 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912638 4000) (Real.log (Enclosure.sfrac Bool.false 3331633476176 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1825276))))))

noncomputable def hp771148 := @hp771147 (Enclosure.sfrac Bool.false 912638 2000) 25163740544809194237497 9007199254740992000 5753995948105897 2178000000000000000000 912638 2000 0

noncomputable def hp771149 := nat_lit 42107168776170079018098000

noncomputable def hp771150 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912638 4000) (Real.log (Enclosure.sfrac Bool.false 3331633476176 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1825276))))) 25167276430022961545497

noncomputable def hp771151 := nat_lit 56663706270425264585525832920917344256

noncomputable def hp771152 := @hp771150 9007199254740992000 5703995947833647 2178000000000000000000 883971303441827 2251799813685248 200000001089 8712000000000000000 hp771151 25163740544809194237497 9007199254740992000 5753995948105897

noncomputable def hp771153 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 912638 4000) (Real.log (Enclosure.sfrac Bool.false 3331633476176 16000000)) 912638 4000 0 1 55152812900674663 4503599627370496

noncomputable def hp771154 := nat_lit 118439763845402286960410624

noncomputable def hp771155 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3331633476176) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp771154 hp617687

noncomputable def hp771156 := BSN.log_rat_reduce_isNear 3331633476176 16000000 17 6663266952352 4194304000000 124254070 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp771157 := nat_lit 88552333693730704312615660912412684626404530568084829718017273652667306592716861728868532349501075887601190709929404367151804716505102717830777918770129141760

noncomputable def hp771158 := nat_lit 1575485863572616621324757133088724320620327652228440469467762500742159033971539199379482533179327635503763657525135714324405527401900746390837172100789174272

noncomputable def hp771159 := nat_lit 130208526601834702095863819284344258631895542319265400239278069335047691858609486894419369905343503885348063026185670807515614265194897786862588395520

noncomputable def hp771160 := BSN.log_dyadic_bound 1234481476176 5428785476176 7 6 hp771157 268435456 87120000 hp771158 hp771159 124254070 6663266952352

noncomputable def hp771161 := hp771160 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp771162 := @BSN.binarySplit_of_base6 (BSN.artanhP 1234481476176) (BSN.artanhQ 5428785476176) 0 6 hp771158 hp771157 hp771159 rfl rfl rfl

noncomputable def hp771163 := hp771156 rfl rfl rfl rfl (hp771161 (hp771162 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp771164 := @hp771153 12500018513 1089000000000000000 25167276430022961545497 9007199254740992000 5703995947833647 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 912638 4000) (BSN.isNear_log_sfrac 3331633476176 16000000 55152812900674663 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp771155 1000001481040000 87120000000000000000000 55152812900674663 4503599627370496 12500018513 1089000000000000000 (hp771163 rfl rfl rfl) rfl)) rfl

noncomputable def hp771165 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1825276)))) 1 4

noncomputable def hp771166 := @hp771165 0 1 883971303441827 562949953421312 200000001089 2178000000000000000 883971303441827 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp771167 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1825276))) 884279719003555 562949953421312 1

noncomputable def hp771168 := @hp771167 2000000000000000 18383 33554432 1 10890000 29661154991290150027264 883971303441827 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp771169 := BSN.arctan_dyadic_bound_f 1000 1825276 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp771170 := hp771169 1 18383 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1825276) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1825276) 0 0 rfl)

noncomputable def hp771171 := hp771166 (hp771168 (hp771170 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp771172 := @hp771145 17527560048759 33554432000 1368957 268435456000 hp771146 3269713162765807021989 1801439850948198400 69063795046264019737 hp739631 (@hp771148 1 hp771149 21053584388085039509049 9007199254740992000 5753995948105897 2178000000000000000000 (@hp771152 2178000000000000000000 hp771164 hp771171 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 912638 2000) rfl rfl)

noncomputable def hp771173 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 912638 2000) (Real.log Real.pi) 912638 2000 0 1 38410761 33554432

noncomputable def hp771174 := hp771172 (@hp771173 3 268435456 17527560048759 33554432000 1368957 268435456000 (Enclosure.Real.IsNear.const Bool.false 912638 2000) hd4909 rfl) rfl

noncomputable def hp771175 := @hp771135 hp739631 15225786873 8388608 521 67108864 (@hp771139 hp771133 hp771134 69063795046264019737 hp739631 (hp771141 rfl rfl rfl rfl rfl) (hp771144 (hp771174 rfl) (Enclosure.Real.IsNear.const Bool.true hp771137 hp771138) rfl rfl)) rfl

noncomputable def hp771176 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 15225786873) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 949585280307019231789056) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp771177 := BSN.sin_reduce_arg_pos_rat_q3 15225786873 8388608 226375608064910080 72057594037927936 288 949585280307019231789056 hp630689 rfl rfl rfl rfl

noncomputable def hp771178 := nat_lit 146572485337089107731203650026986156050617431527775647586273995951151856643296650245935530625

noncomputable def hp771179 := nat_lit 18448169616155817683597496004369015594070356788160552613960291332793725823165168062890625

noncomputable def hp771180 := nat_lit 383850450274902458448331354124766192202560016280803007545533101305144625176348959419634090625

noncomputable def hp771181 := BSN.sin_dyadic_bound_f 107955347665 137438953472 3 2 67108864 21801270 hp771178 hp738039 hp771179 hp771180 hp738042

noncomputable def hp771182 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 107955347665) (BSN.sinEvenQ 137438953472) 0 2 hp771178 hp738039 hp771179 rfl rfl rfl

noncomputable def hp771183 := hp771181 hp771179 47456946 rfl rfl rfl rfl rfl rfl rfl rfl (hp771182 rfl)

noncomputable def hp771184 := @BSN.binarySplit_of_base2 (BSN.sinOddP 107955347665) (BSN.sinOddQ 137438953472) 0 2 hp771180 hp738042 hp771179 rfl rfl rfl

noncomputable def hp771185 := @BSN.sin_arg_round Bool.false 47456946 67108864 949585280307019231789056 hp630689 107955347665 137438953472 21801270 21780000 (hp771183 (hp771184 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771186 := hp771176 47456946 67108864 288 1000000000000000 21780000 10890000 hp771177 BSN.pi_near_15 hp771185 rfl rfl

noncomputable def hp771187 := @hp771132 521 67108864 Bool.false 47456946 67108864 1 10890000 hp771175 (Enclosure.sfrac_false_div 15225786873 8388608) (hp771186 rfl rfl) rfl

noncomputable def hp771188 := @hp771129 23728473 33554432 358799929 45675970560000 379655568 536870912 4218 536870912 (@hp771130 Bool.false 23728473 33554432 358799929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000)) (@hp771131 5740798864 730815528960000 23728473 33554432 358799929 45675970560000 (hp771187 rfl) rfl))

noncomputable def hp771189 := @hp771135 hp739631 974450359876 536870912 4157 536870912 (@hp771139 hp771133 hp771134 69063795046264019737 hp739631 (hp771141 rfl rfl rfl rfl rfl) (hp771144 (hp771174 rfl) (Enclosure.Real.IsNear.const Bool.true hp771137 hp771138) rfl rfl)) rfl

noncomputable def hp771190 := hp771128 (BSN.cos_quad_nat1 517 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 167975386 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl rfl (hp771188 rfl) hp771189

noncomputable def hp771191 := nat_lit 25717166698885565962866222427653994505651700556200078159048749905800479548903052306274059343862709985862249086976

noncomputable def hp771192 := nat_lit 6481500199562625437933417537188337244710758749568692005783731748892707826379999731586730096411937127530496

noncomputable def hp771193 := nat_lit 155878682722449397126349570010068109083211865680032078875402050305534466969698751239675546817624594588283583856640

noncomputable def hp771194 := BSN.cos_dyadic_bound_f 657112348 536870912 4 3 536870912 268435456 hp771191 hp716712 hp771192 hp771193 hp716714

noncomputable def hp771195 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 657112348) (BSN.cosEvenQ 536870912) 0 3 hp771191 hp716712 hp771192 rfl rfl rfl

noncomputable def hp771196 := hp771194 hp771192 182491831 rfl rfl rfl rfl rfl rfl rfl rfl (hp771195 rfl)

noncomputable def hp771197 := @BSN.binarySplit_of_base3 (BSN.cosOddP 657112348) (BSN.cosOddQ 536870912) 0 3 hp771193 hp716714 hp771192 rfl rfl rfl

noncomputable def hp771198 := nat_lit 851925342567042571505108612438401

noncomputable def hp771199 := BSN.sin_dyadic_bound_f 170844257 536870912 2 1 536870912 268435456 hp771198 hp708890 hp771198 hp771198 hp708891

noncomputable def hp771200 := @BSN.binarySplit_of_base (BSN.sinEvenP 170844257) (BSN.sinEvenQ 536870912) 0 1 hp771198 hp708890 hp771198 rfl rfl rfl

noncomputable def hp771201 := hp771199 hp771198 167975386 rfl rfl rfl rfl rfl rfl rfl rfl (hp771200 rfl)

noncomputable def hp771202 := @BSN.binarySplit_of_base (BSN.sinOddP 170844257) (BSN.sinOddQ 536870912) 0 1 hp771198 hp708891 hp771198 rfl rfl rfl

noncomputable def hp771203 := hp771190 hd4911 hd4913 hd4915 hd4917 hd4918 (hp771196 (hp771197 rfl) rfl rfl rfl rfl) (hp771201 (hp771202 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771204 := hp771124 (BSN.cos_quad_nat0 220 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 428731314 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl rfl (hp771203 rfl rfl rfl rfl rfl) hp771189

noncomputable def hp771205 := nat_lit 5856953115421933345690405827201

noncomputable def hp771206 := BSN.cos_dyadic_bound_f 49194657 536870912 2 1 536870912 268435456 hp771205 hp708767 hp771205 hp771205 hp708768

noncomputable def hp771207 := @BSN.binarySplit_of_base (BSN.cosEvenP 49194657) (BSN.cosEvenQ 536870912) 0 1 hp771205 hp708767 hp771205 rfl rfl rfl

noncomputable def hp771208 := hp771206 hp771205 534618581 rfl rfl rfl rfl rfl rfl rfl rfl (hp771207 rfl)

noncomputable def hp771209 := @BSN.binarySplit_of_base (BSN.cosOddP 49194657) (BSN.cosOddQ 536870912) 0 1 hp771205 hp708768 hp771205 rfl rfl rfl

noncomputable def hp771210 := nat_lit 2017916409915816855951388046254244927288498055960014450760220245423690625

noncomputable def hp771211 := nat_lit 208996407949163280877632314642443652610634237248923895986958562890625

noncomputable def hp771212 := nat_lit 6053331236931552241292408874133449894560272899405545504488686819145290625

noncomputable def hp771213 := BSN.cos_dyadic_bound_f 346750705 536870912 3 2 536870912 268435456 hp771210 hp708868 hp771211 hp771212 hp708870

noncomputable def hp771214 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 346750705) (BSN.cosEvenQ 536870912) 0 2 hp771210 hp708868 hp771211 rfl rfl rfl

noncomputable def hp771215 := hp771213 hp771211 428731314 rfl rfl rfl rfl rfl rfl rfl rfl (hp771214 rfl)

noncomputable def hp771216 := @BSN.binarySplit_of_base2 (BSN.cosOddP 346750705) (BSN.cosOddQ 536870912) 0 2 hp771212 hp708870 hp771211 rfl rfl rfl

noncomputable def hp771217 := hp771204 hd4920 hd4922 hd4924 hd4926 hd4918 (hp771208 (hp771209 rfl) rfl rfl rfl rfl) (hp771215 (hp771216 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771218 := hp771120 (BSN.cos_quad_nat0 24 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 67569480 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl rfl (hp771217 rfl rfl rfl rfl rfl) hp771189

noncomputable def hp771219 := nat_lit 3802086987124132264787699546906950355936939721508941055046461896891701761

noncomputable def hp771220 := nat_lit 741817466622735326370534316711120908043325273120013320662015458286081

noncomputable def hp771221 := nat_lit 11404777326439151323710357572087428825994732513980583138498061659758533121

noncomputable def hp771222 := BSN.cos_dyadic_bound_f 406244161 536870912 3 2 536870912 268435456 hp771219 hp708868 hp771220 hp771221 hp708870

noncomputable def hp771223 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 406244161) (BSN.cosEvenQ 536870912) 0 2 hp771219 hp708868 hp771220 rfl rfl rfl

noncomputable def hp771224 := hp771222 hp771220 390365952 rfl rfl rfl rfl rfl rfl rfl rfl (hp771223 rfl)

noncomputable def hp771225 := @BSN.binarySplit_of_base2 (BSN.cosOddP 406244161) (BSN.cosOddQ 536870912) 0 2 hp771221 hp708870 hp771220 rfl rfl rfl

noncomputable def hp771226 := nat_lit 49967069860293773879418071442132713833655167675451525959507062143043879490174087481034981601281101311472425046016

noncomputable def hp771227 := nat_lit 47361251088834357972615316869498797937714804755287322470123912770159350908658570276884316403827860659572736

noncomputable def hp771228 := nat_lit 302610796381317044007406962098374578086842196447289070709765887215570049057593784197794434813542995239565283102720

noncomputable def hp771229 := BSN.cos_dyadic_bound_f 775565706 536870912 4 3 536870912 268435456 hp771226 hp716712 hp771227 hp771228 hp716714

noncomputable def hp771230 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 775565706) (BSN.cosEvenQ 536870912) 0 3 hp771226 hp716712 hp771227 rfl rfl rfl

noncomputable def hp771231 := hp771229 hp771227 67569480 rfl rfl rfl rfl rfl rfl rfl rfl (hp771230 rfl)

noncomputable def hp771232 := @BSN.binarySplit_of_base3 (BSN.cosOddP 775565706) (BSN.cosOddQ 536870912) 0 3 hp771228 hp716714 hp771227 rfl rfl rfl

noncomputable def hp771233 := hp771218 hd4928 hd4930 hd4932 hd4934 hd4918 (hp771224 (hp771225 rfl) rfl rfl rfl rfl) (hp771231 (hp771232 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771234 := hp771115 (BSN.cos_quad_nat1 121 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 79712589 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl rfl (hp771233 rfl rfl rfl rfl rfl) hp771189

noncomputable def hp771235 := nat_lit 13434090002465463803636353806923445926353981804924508366818427760426468722925791673410842245243308651879986890625

noncomputable def hp771236 := nat_lit 925680377220178949709363144299778746979961644483485178820553090042729275885140990925439509798886962890625

noncomputable def hp771237 := nat_lit 81462227681797634881715848796784167371852871962794737201879770778947848525657702366317702608219089766594508490625

noncomputable def hp771238 := BSN.cos_dyadic_bound_f 558733985 536870912 4 3 536870912 268435456 hp771235 hp716712 hp771236 hp771237 hp716714

noncomputable def hp771239 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 558733985) (BSN.cosEvenQ 536870912) 0 3 hp771235 hp716712 hp771236 rfl rfl rfl

noncomputable def hp771240 := hp771238 hp771236 271440043 rfl rfl rfl rfl rfl rfl rfl rfl (hp771239 rfl)

noncomputable def hp771241 := @BSN.binarySplit_of_base3 (BSN.cosOddP 558733985) (BSN.cosOddQ 536870912) 0 3 hp771237 hp716714 hp771236 rfl rfl rfl

noncomputable def hp771242 := nat_lit 40977234590733826599810174796816

noncomputable def hp771243 := BSN.sin_dyadic_bound_f 80008414 536870912 2 1 536870912 268435456 hp771242 hp708890 hp771242 hp771242 hp708891

noncomputable def hp771244 := @BSN.binarySplit_of_base (BSN.sinEvenP 80008414) (BSN.sinEvenQ 536870912) 0 1 hp771242 hp708890 hp771242 rfl rfl rfl

noncomputable def hp771245 := hp771243 hp771242 79712589 rfl rfl rfl rfl rfl rfl rfl rfl (hp771244 rfl)

noncomputable def hp771246 := @BSN.binarySplit_of_base (BSN.sinOddP 80008414) (BSN.sinOddQ 536870912) 0 1 hp771242 hp708891 hp771242 rfl rfl rfl

noncomputable def hp771247 := hp771234 hd4936 hd4938 hd4940 hd4942 hd4918 (hp771240 (hp771241 rfl) rfl rfl rfl rfl) (hp771245 (hp771246 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771248 := hp771110 (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 472577653 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl rfl (hp771247 rfl rfl rfl rfl rfl) hp771189

noncomputable def hp771249 := nat_lit 649455201610731677355684691334559333299965393102043327441868409679118336

noncomputable def hp771250 := nat_lit 21651694156692134376391402545823250352155569436582325045993884614656

noncomputable def hp771251 := nat_lit 1948322301443881647798301291198586353399191868167256817675513241268125696

noncomputable def hp771252 := BSN.cos_dyadic_bound_f 261177936 536870912 3 2 536870912 268435456 hp771249 hp708868 hp771250 hp771251 hp708870

noncomputable def hp771253 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 261177936) (BSN.cosEvenQ 536870912) 0 2 hp771249 hp708868 hp771250 rfl rfl rfl

noncomputable def hp771254 := hp771252 hp771250 474584836 rfl rfl rfl rfl rfl rfl rfl rfl (hp771253 rfl)

noncomputable def hp771255 := @BSN.binarySplit_of_base2 (BSN.cosOddP 261177936) (BSN.cosOddQ 536870912) 0 2 hp771251 hp708870 hp771250 rfl rfl rfl

noncomputable def hp771256 := nat_lit 28027954756423588175746196307531280013804666192285708621640120870465306880

noncomputable def hp771257 := nat_lit 12435829949714412729724248876829626579667022276448529123564134717849856

noncomputable def hp771258 := nat_lit 73386413970714621887296674878686104450264188658014986866666927014056427776

noncomputable def hp771259 := BSN.sin_dyadic_bound_f 577875586 536870912 3 2 536870912 268435456 hp771256 hp708845 hp771257 hp771258 hp708848

noncomputable def hp771260 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 577875586) (BSN.sinEvenQ 536870912) 0 2 hp771256 hp708845 hp771257 rfl rfl rfl

noncomputable def hp771261 := hp771259 hp771257 472577653 rfl rfl rfl rfl rfl rfl rfl rfl (hp771260 rfl)

noncomputable def hp771262 := @BSN.binarySplit_of_base2 (BSN.sinOddP 577875586) (BSN.sinOddQ 536870912) 0 2 hp771258 hp708848 hp771257 rfl rfl rfl

noncomputable def hp771263 := hp771248 hd4944 hd4946 hd4961 hd4963 hd4918 (hp771254 (hp771255 rfl) rfl rfl rfl rfl) (hp771261 (hp771262 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771264 := hp771105 499435632 Bool.false Bool.false 123321880 236087 BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 499435632 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl (hp771263 rfl rfl rfl rfl rfl)

noncomputable def hp771265 := nat_lit 230877526958976886814052590712668174184398442976441486606633506969721921

noncomputable def hp771266 := nat_lit 2736374102567574167265817119592123755207111167062584691937431755841

noncomputable def hp771267 := nat_lit 692627108128725525293823240503765338305684914706990334650516646045654081

noncomputable def hp771268 := BSN.cos_dyadic_bound_f 201672617 536870912 3 2 536870912 268435456 hp771265 hp708868 hp771266 hp771267 hp708870

noncomputable def hp771269 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 201672617) (BSN.cosEvenQ 536870912) 0 2 hp771265 hp708868 hp771266 rfl rfl rfl

noncomputable def hp771270 := hp771268 hp771266 499435632 rfl rfl rfl rfl rfl rfl rfl rfl (hp771269 rfl)

noncomputable def hp771271 := @BSN.binarySplit_of_base2 (BSN.cosOddP 201672617) (BSN.cosOddQ 536870912) 0 2 hp771267 hp708870 hp771266 rfl rfl rfl

noncomputable def hp771272 := hp771264 hp771189 hd5088 hd5090 hd4918 (hp771270 (hp771271 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp771273 := @hp771100 Bool.false 15415235 33554432 236087 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 912638 1000)) (Enclosure.sfrac Bool.false 912638 1000) 12) (@hp771102 236087 268435456 (hp771272 rfl rfl rfl) (hp771272 rfl rfl rfl) rfl rfl)

noncomputable def hp771274 := @Enclosure.Real.IsNear.mulLit_ff hp771091 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1))) 9665409 33554432 1

noncomputable def hp771275 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp771090 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp771276 := @hp771275 1 1 0 1 9665409 33554432 1 33554432 9665409 33554432 1

noncomputable def hp771277 := @Enclosure.Real.IsNear.of_eq (hp771090 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp771278 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 912638 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771279 := @hp771277 (@Inv.inv Real Real.instInv (Real.sqrt hp771092)) Bool.false 9665409 33554432 1 33554432 (hp771278 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 912638 1000) 912638 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000))))

noncomputable def hp771280 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp771092)) Bool.false 19330818 67108864 2 67108864 9665409 33554432

noncomputable def hp771281 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp771092) Bool.false 232975125 67108864 7 67108864 232975125 67108864 7 67108864

noncomputable def hp771282 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 912638 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771283 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 912638 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771284 := @hp771283 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 912638 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4873809537533

noncomputable def hp771285 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 912638 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 912638 1000 0

noncomputable def hp771286 := @hp771285 1 10680707 67108864 1 67108864 4873809537533 33554432000 456319 33554432000 (Enclosure.Real.IsNear.const Bool.false 912638 1000) hd4949

noncomputable def hp771287 := @hp771284 33554432000 456319 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 912638 1000) 912638 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000))) (hp771286 rfl)

noncomputable def hp771288 := @hp771282 4873809537533 33554432000 456319 33554432000 404398189 404398228 33554432 hp771287 rfl rfl rfl

noncomputable def hp771289 := @Enclosure.Real.IsNear.recentre' hp771092 Bool.false 808796417 67108864 39 67108864 808796417 67108864 39 67108864 (hp771288 rfl rfl rfl)

noncomputable def hp771290 := @Enclosure.Real.IsNear.sqrt_image hp771092 808796417 67108864 39 67108864 116487559 116487566 33554432 (hp771289 rfl) rfl rfl

noncomputable def hp771291 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp771092) 232975125 67108864 7 67108864 9665408 9665410 33554432 (hp771281 (hp771290 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp771292 := @hp771276 33554432 (@hp769737 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (hp771279 (@hp771280 1 33554432 (hp771291 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp771293 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp771294 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp771295 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1))) (hp771293 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771294 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp771296 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 912638 1000) 912638 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl

noncomputable def hp771297 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp771298 := @hp771297 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771294 (Enclosure.sfrac Bool.false 1 16)))) 35429105

noncomputable def hp771299 := @hp771298 33554432 141 33554432 6402607 8388608 11832769 2854748160000 226838635676735 281474976710656 1452898356426223 191578906023690240000

noncomputable def hp771300 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp771301 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)))) 15889477

noncomputable def hp771302 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)))) Bool.false

noncomputable def hp771303 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1370539) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false

noncomputable def hp771304 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1))) Bool.false 3086179549028638124195

noncomputable def hp771305 := nat_lit 1052456940982697065384464721

noncomputable def hp771306 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)) 884279719003555 140737488355328 1

noncomputable def hp771307 := @Enclosure.Real.IsNear.subLit_ff_p hp771092 (Enclosure.sfrac Bool.false 12 1) 808796417 67108864 39 67108864 12 1 0

noncomputable def hp771308 := @hp771306 500000000000000 3490049 67108864 39 67108864 3086179549028638124195 9444732965739290427392 hp771305 hp738031 hd4948 (@hp771307 1 3490049 3490049 67108864 39 67108864 (hp771289 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771309 := @hp771303 1370539 4194304 123 33554432 Bool.false 31778954 33554432 1 10890000 (@hp771304 9444732965739290427392 hp771305 hp738031 1370539 4194304 123 33554432 (hp771308 rfl) rfl) (Enclosure.sfrac_false_div 1370539 4194304)

noncomputable def hp771310 := nat_lit 3528300719599391490571441

noncomputable def hp771311 := BSN.cos_dyadic_bound_f 1370539 4194304 2 1 33554432 10890000 hp771310 hp664746 hp771310 hp771310 hp664747

noncomputable def hp771312 := @BSN.binarySplit_of_base (BSN.cosEvenP 1370539) (BSN.cosEvenQ 4194304) 0 1 hp771310 hp664746 hp771310 rfl rfl rfl

noncomputable def hp771313 := hp771311 hp771310 31778954 rfl rfl rfl rfl rfl rfl rfl rfl (hp771312 rfl)

noncomputable def hp771314 := @BSN.binarySplit_of_base (BSN.cosOddP 1370539) (BSN.cosOddQ 4194304) 0 1 hp771310 hp664747 hp771310 rfl rfl rfl

noncomputable def hp771315 := hp771309 (hp771313 (hp771314 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp771316 := @hp771301 16777216 85814027 22837985280000 35428964 35429246 33554432 (@hp771302 31778954 33554432 1373024432 365407764480000 15889477 16777216 85814027 22837985280000 hp771315 rfl)

noncomputable def hp771317 := @hp771300 Bool.false 70858210 67108864 282 67108864 35429105 33554432 141 33554432 (hp771316 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp771318 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771294 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp771319 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771294 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 23570899)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp771320 := nat_lit 445241699098667434052979111005

noncomputable def hp771321 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771294 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp771320

noncomputable def hp771322 := nat_lit 15595096671005589345836259879906917

noncomputable def hp771323 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771294 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp771324 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp771325 := @hp771324 (Enclosure.sfrac Bool.false 1 16) 222032781671935 4503599627370496 2889471039 4503599627370496 1 16 0

noncomputable def hp771326 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)) 12180442022401

noncomputable def hp771327 := @hp771326 4503599627370496 272225343 4503599627370496 3490049 67108864 39 67108864 14900367748763578531840 222032781671935 4503599627370496 2889471039

noncomputable def hp771328 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)) 3490049 67108864 39

noncomputable def hp771329 := @hp771328 67108864 3490049 67108864 39 67108864 12180442022401 4503599627370496 272225343 4503599627370496 (@hp771307 1 3490049 3490049 67108864 39 67108864 (hp771289 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771330 := hp771329 (@hp771307 1 3490049 3490049 67108864 39 67108864 (hp771289 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771331 := @hp771327 4503599627370496 (hp771330 rfl) (@hp771307 1 3490049 3490049 67108864 39 67108864 (hp771289 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771332 := @hp771323 500000000000000 503507758382591 4503599627370496 2889471039 4503599627370496 hp771320 hp627574 hp771322 hp742826 hd4948 (@hp771325 1 8056124134121456 503507758382591 4503599627370496 2889471039 4503599627370496 (hp771331 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp771333 := @hp771319 23570899 33554432 17 4194304 Bool.false 25610428 33554432 1 10890000 (@hp771321 hp627574 hp771322 hp742826 23570899 33554432 17 4194304 (hp771332 rfl) rfl) (Enclosure.sfrac_true_div 23570899 33554432)

noncomputable def hp771334 := nat_lit 657470663171028284544301830127846967970225614852238071183496481

noncomputable def hp771335 := nat_lit 95281629436879254617780436251771532440867582607005538112801

noncomputable def hp771336 := nat_lit 1972221426254211095123669929511037360845795109391500202474263841

noncomputable def hp771337 := BSN.cos_dyadic_bound_f 23570899 33554432 3 2 33554432 10890000 hp771334 hp684401 hp771335 hp771336 hp684404

noncomputable def hp771338 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 23570899) (BSN.cosEvenQ 33554432) 0 2 hp771334 hp684401 hp771335 rfl rfl rfl

noncomputable def hp771339 := hp771337 hp771335 25610428 rfl rfl rfl rfl rfl rfl rfl rfl (hp771338 rfl)

noncomputable def hp771340 := @BSN.binarySplit_of_base2 (BSN.cosOddP 23570899) (BSN.cosOddQ 33554432) 0 2 hp771336 hp684404 hp771335 rfl rfl rfl

noncomputable def hp771341 := hp771333 (BSN.cos_neg_of_bound 23570899 33554432 Bool.false 25610428 33554432 1 10890000 (hp771339 (hp771340 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp771342 := hp771299 hp771317 (@hp771318 25610428 33554432 189324304 45675970560000 6402607 8388608 11832769 2854748160000 (hp771341 rfl) rfl)

noncomputable def hp771343 := @hp771274 33554432 226838635676735 281474976710656 1452898356426223 191578906023690240000 2192488190817635559615 9444732965739290427392 2839450069918611561161 hp764965 (hp771292 rfl) (@hp771295 Bool.false 226838635676735 281474976710656 1452898356426223 191578906023690240000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771092 (Enclosure.sfrac Bool.false 12 1)) (hp771296 rfl (hp771095 rfl rfl))) (hp771342 rfl))

noncomputable def hp771344 := @hp771089 1133571679730292553833161 hp764965 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912638 1000))) (@hp771094 1133571679730292553833161 hp764965 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 912638 1000) 12 (hp771095 rfl rfl)) (@hp771098 1133571679730292553833161 hp764965 hp771273 (hp771343 rfl) rfl rfl))

theorem hd5097 : hp771088 hp764965 := hp771344

noncomputable def hp771345 := nat_lit 4126366894891559248462627

noncomputable def hp771346 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 913584 1000)) Bool.true 259305943499235714045743 75557863725914323419136 hp771345

noncomputable def hp771347 := nat_lit 4675142818040948761559040000

noncomputable def hp771348 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 913584 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 913584 1000)) Bool.true 259305943499235714045743 75557863725914323419136

noncomputable def hp771349 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 913584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771350 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp771349 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp771351 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 913584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771352 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp771350 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp771353 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 913584 1000)) hp771352 Bool.true 259305943499235714045743 75557863725914323419136

noncomputable def hp771354 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 913584 1000) 913584 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl

noncomputable def hp771355 := @Enclosure.Real.IsNear.subLit_tf (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) 12) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp771350 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1))))

noncomputable def hp771356 := nat_lit 69606909186727574551354627063808

noncomputable def hp771357 := @hp771355 859958423 268435456 118165 134217728 17249166413178252990255 75557863725914323419136 10381180293494301262627 hp771347 hp771356 259305943499235714045743 75557863725914323419136

noncomputable def hp771358 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) 12)

noncomputable def hp771359 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) 12) hp771358

noncomputable def hp771360 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) 12) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) 12)

noncomputable def hp771361 := @hp771360 859958423 536870912 236330 536870912 859958423 536870912 236330 536870912 923373325676183552 859958423 268435456

noncomputable def hp771362 := BSN.mainSumRS_step (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) Real.cos BSN.quadSignPos 11

noncomputable def hp771363 := hp771362 12 913584 1000 288 536870912 268435456 9007199254740992 Bool.false 975714721773 4162 1334074092

noncomputable def hp771364 := hp771363 51 154981288 8 Bool.true 1004378250 221668 Bool.true 199344811 28296951008113761 1 Bool.false

noncomputable def hp771365 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp771366 := hp771365 BSN.quadSignNeg 9 10 11 913584 1000 182 237 536870912 268435456 9007199254740992

noncomputable def hp771367 := hp771366 Bool.false 975714721773 4162 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp771368 := hp771367 Bool.true 707374520 190295 Bool.true 166252684 Bool.true 531356457 28296951008113761 1 Bool.false 511334250

noncomputable def hp771369 := hp771368 Bool.true Bool.false 448758043 Bool.true Bool.true 1004378250 221668 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 511334250 536870912) BSN.abs_quadSignNeg

noncomputable def hp771370 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp771371 := hp771370 BSN.quadSignPos 7 8 9 913584 1000 52 120 536870912 268435456 9007199254740992

noncomputable def hp771372 := hp771371 Bool.false 975714721773 4162 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp771373 := hp771372 Bool.true 880904383 155413 Bool.true 350478614 Bool.true 774887520 28296951008113761 1 Bool.false 426477182

noncomputable def hp771374 := hp771373 Bool.false Bool.false 68242220 Bool.false Bool.true 707374520 190295 BSN.abs_quadSignPos (BSN.cos_quad_nat0 52 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 426477182 536870912) BSN.abs_quadSignPos

noncomputable def hp771375 := hp771365 BSN.quadSignNeg 5 6 7 913584 1000 114 25 536870912 268435456 9007199254740992

noncomputable def hp771376 := hp771375 Bool.false 975714721773 4162 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp771377 := hp771376 Bool.true 770494649 115489 Bool.false 760607476 Bool.false 208324142 28296951008113761 1 Bool.false 82380622

noncomputable def hp771378 := hp771377 Bool.true Bool.false 203135452 Bool.true Bool.true 880904383 155413 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 114 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 82380622 536870912) BSN.abs_quadSignNeg

noncomputable def hp771379 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp771380 := hp771379 BSN.quadSignPos 3 4 5 913584 1000 350 220 536870912 268435456 9007199254740992

noncomputable def hp771381 := hp771380 Bool.false 975714721773 4162 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp771382 := hp771381 Bool.true 679393227 68258 Bool.false 609485549 Bool.false 793711479 28296951008113761 1 Bool.false 226506363

noncomputable def hp771383 := hp771382 Bool.true Bool.false 49532833 Bool.false Bool.true 770494649 115489 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 350 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 226506363 536870912) BSN.abs_quadSignPos

noncomputable def hp771384 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp771385 := hp771384 BSN.quadSignNeg 1 2 3 913584 1000 753 518 536870912 268435456 9007199254740992

noncomputable def hp771386 := hp771385 Bool.false 975714721773 4162 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp771387 := hp771386 Bool.false 567240 4218 Bool.false 726123894 Bool.false 33928223 28296951008113761 1 Bool.false 524131093

noncomputable def hp771388 := hp771387 Bool.true Bool.false 535799200 Bool.true Bool.true 679393227 68258 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 753 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 524131093 536870912) BSN.abs_quadSignNeg

noncomputable def hp771389 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) 1) Bool.false

noncomputable def hp771390 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)))

noncomputable def hp771391 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000))) Bool.false 70905 67108864

noncomputable def hp771392 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 121964340221) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 121964340221 67108864

noncomputable def hp771393 := nat_lit 290458519146923852983474170521573031728470324596511257

noncomputable def hp771394 := nat_lit 159820003319313787008537704899601802073949077504000

noncomputable def hp771395 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) Bool.false hp771393 hp771394 8641896402618701677

noncomputable def hp771396 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 913584 4000) (Real.log (Enclosure.sfrac Bool.false 3338543900224 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1827168))))))

noncomputable def hp771397 := nat_lit 305480851023403423422597599723520000

noncomputable def hp771398 := nat_lit 1674494740871973432457120325528569774080

noncomputable def hp771399 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp771396 (Enclosure.sfrac Bool.false 913584 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 913584 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp771397 hp771398)) Bool.false

noncomputable def hp771400 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 913584 1000) 913584 1000 3338543900224 16000000 1827168

noncomputable def hp771401 := hp771400 4000 2000 hp771397 hp771398 (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl rfl rfl rfl

noncomputable def hp771402 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp771396 (Enclosure.sfrac Bool.false 913584 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 913584 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp771397 hp771398) 2046222285596976275217 1125899906842624000

noncomputable def hp771403 := nat_lit 3426388111946304293242493383074325837324265614696253112975360

noncomputable def hp771404 := @hp771402 8641896402618701677 1115136000000000000000000 hp771397 hp771398 0 1 hp771403 hp771393 hp771394 8641896402618701677 1115136000000000000000000

noncomputable def hp771405 := @Enclosure.Real.IsNear.subLit_ff_p (hp771396 (Enclosure.sfrac Bool.false 913584 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 913584 2000) (Real.log Real.pi)) 2634959234028761046801 1125899906842624000 2879954228431273 1089000000000000000000

noncomputable def hp771406 := nat_lit 8582478317368539979047763968000

noncomputable def hp771407 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 913584 4000) (Real.log (Enclosure.sfrac Bool.false 3338543900224 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1827168))))))

noncomputable def hp771408 := @hp771407 (Enclosure.sfrac Bool.false 913584 2000) 3149261304275216949009 1125899906842624000 2879954228431273 1089000000000000000000 913584 2000 0

noncomputable def hp771409 := nat_lit 5269918468057522093602000

noncomputable def hp771410 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 913584 4000) (Real.log (Enclosure.sfrac Bool.false 3338543900224 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1827168))))) 3149703290086321414509

noncomputable def hp771411 := nat_lit 7091506018213094636544880599191519232

noncomputable def hp771412 := @hp771410 1125899906842624000 237912852357929 90750000000000000000 883971622208931 2251799813685248 200000001089 8712000000000000000 hp771411 3149261304275216949009 1125899906842624000 2879954228431273

noncomputable def hp771413 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 913584 4000) (Real.log (Enclosure.sfrac Bool.false 3338543900224 16000000)) 913584 4000 0 1 55162144522431591 4503599627370496

noncomputable def hp771414 := nat_lit 118459803350534610871123968

noncomputable def hp771415 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3338543900224) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp771414 hp617687

noncomputable def hp771416 := BSN.log_rat_reduce_isNear 3338543900224 16000000 17 6677087800448 4194304000000 124810278 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp771417 := nat_lit 89914487212917812509736270325469901706433542938399872395337269655866556214064625636865920721637135145735496894246482061271022720152376146465492277219043573760

noncomputable def hp771418 := nat_lit 1614023314204966481883472158493708770303649859355968110239521528594170445910860228622919686412805282447038324094872869825011057459025820055093084151896604672

noncomputable def hp771419 := nat_lit 139229538115350476424089358743957627142126869525138690640197767202878680524919733581214285494944944019112008329271034620944568090947771671275655659520

noncomputable def hp771420 := BSN.log_dyadic_bound 1241391900224 5435695900224 7 6 hp771417 268435456 87120000 hp771418 hp771419 124810278 6677087800448

noncomputable def hp771421 := hp771420 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp771422 := @BSN.binarySplit_of_base6 (BSN.artanhP 1241391900224) (BSN.artanhQ 5435695900224) 0 6 hp771418 hp771417 hp771419 rfl rfl rfl

noncomputable def hp771423 := hp771416 rfl rfl rfl rfl (hp771421 (hp771422 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp771424 := @hp771413 12500018513 1089000000000000000 3149703290086321414509 1125899906842624000 237912852357929 90750000000000000000 (Enclosure.Real.IsNear.const Bool.false 913584 4000) (BSN.isNear_log_sfrac 3338543900224 16000000 55162144522431591 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp771415 1000001481040000 87120000000000000000000 55162144522431591 4503599627370496 12500018513 1089000000000000000 (hp771423 rfl rfl rfl) rfl)) rfl

noncomputable def hp771425 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1827168)))) 1 4

noncomputable def hp771426 := @hp771425 0 1 883971622208931 562949953421312 200000001089 2178000000000000000 883971622208931 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp771427 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1827168))) 884279719003555 562949953421312 1

noncomputable def hp771428 := @hp771427 2000000000000000 18364 33554432 1 10890000 29661165687339265032192 883971622208931 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp771429 := BSN.arctan_dyadic_bound_f 1000 1827168 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp771430 := hp771429 1 18364 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1827168) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1827168) 0 0 rfl)

noncomputable def hp771431 := hp771426 (hp771428 (hp771430 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp771432 := @hp771405 2193216042339 4194304000 171297 33554432000 hp771406 2046222285596976275217 1125899906842624000 8641896402618701677 1115136000000000000000000 (@hp771408 1 hp771409 2634959234028761046801 1125899906842624000 2879954228431273 1089000000000000000000 (@hp771412 1089000000000000000000 hp771424 hp771431 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 913584 2000) rfl rfl)

noncomputable def hp771433 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 913584 2000) (Real.log Real.pi) 913584 2000 0 1 38410761 33554432

noncomputable def hp771434 := hp771432 (@hp771433 3 268435456 2193216042339 4194304000 171297 33554432000 (Enclosure.Real.IsNear.const Bool.false 913584 2000) hd4909 rfl) rfl

noncomputable def hp771435 := @hp771395 1115136000000000000000000 121964340221 67108864 521 67108864 (@hp771399 hp771393 hp771394 8641896402618701677 1115136000000000000000000 (hp771401 rfl rfl rfl rfl rfl) (hp771404 (hp771434 rfl) (Enclosure.Real.IsNear.const Bool.true hp771397 hp771398) rfl rfl)) rfl

noncomputable def hp771436 := nat_lit 15181591402659015391444992

noncomputable def hp771437 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 121964340221) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp771436) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp771438 := BSN.sin_reduce_arg_pos_rat_q0 121964340221 67108864 226375608064910080 72057594037927936 289 hp771436 hp617687 rfl rfl rfl rfl

noncomputable def hp771439 := nat_lit 5524869052725798132221380393475860431791602912195008617019459987476698728122360902412430421403801030980831386732319152464499718782007803641856

noncomputable def hp771440 := nat_lit 10168338076972414478622406858218520506353281037340186933308553802120772435989999084446186731784608675687226500221792780758459173805490176

noncomputable def hp771441 := nat_lit 33437020984329174162525422566776522940367930584247316698119961391745756451409121546290976953773229977696238219777938245824574014150004734689280

noncomputable def hp771442 := BSN.cos_dyadic_bound_f 215743389768 137438953472 4 3 67108864 21801270 hp771439 hp740177 hp771440 hp771441 hp740180

noncomputable def hp771443 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 215743389768) (BSN.cosEvenQ 137438953472) 0 3 hp771439 hp740177 hp771440 rfl rfl rfl

noncomputable def hp771444 := hp771442 hp771440 70905 rfl rfl rfl rfl rfl rfl rfl rfl (hp771443 rfl)

noncomputable def hp771445 := @BSN.binarySplit_of_base3 (BSN.cosOddP 215743389768) (BSN.cosOddQ 137438953472) 0 3 hp771441 hp740180 hp771440 rfl rfl rfl

noncomputable def hp771446 := @BSN.cos_arg_round Bool.false 70905 67108864 hp771436 hp617687 215743389768 137438953472 21801270 21780000 (hp771444 (hp771445 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771447 := hp771437 70905 67108864 289 1000000000000000 21780000 10890000 hp771438 BSN.pi_near_15 hp771446 rfl rfl

noncomputable def hp771448 := @hp771392 521 67108864 Bool.false 70905 67108864 1 10890000 hp771435 (Enclosure.sfrac_false_div 121964340221 67108864) (hp771447 rfl rfl) rfl

noncomputable def hp771449 := @hp771389 70905 67108864 358799929 45675970560000 567240 536870912 4218 536870912 (@hp771390 Bool.false 70905 67108864 358799929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000)) (@hp771391 5740798864 730815528960000 70905 67108864 358799929 45675970560000 (hp771448 rfl) rfl))

noncomputable def hp771450 := @hp771395 1115136000000000000000000 975714721773 536870912 4162 536870912 (@hp771399 hp771393 hp771394 8641896402618701677 1115136000000000000000000 (hp771401 rfl rfl rfl rfl rfl) (hp771404 (hp771434 rfl) (Enclosure.Real.IsNear.const Bool.true hp771397 hp771398) rfl rfl)) rfl

noncomputable def hp771451 := hp771388 (BSN.cos_quad_nat2 518 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535799200 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl rfl (hp771449 rfl) hp771450

noncomputable def hp771452 := nat_lit 99673884627722735495269072772458576249434427209176034904121949345193350471588702008424021850164802118865109979136

noncomputable def hp771453 := nat_lit 21484672396279588074264031400859262825438332101212963210032945257595079634513453778898504420807237577281536

noncomputable def hp771454 := nat_lit 498028796647417709322179246566201980309105892867887009082389177911330830516002102122850013569134546078416078442496

noncomputable def hp771455 := BSN.sin_dyadic_bound_f 726123894 536870912 4 3 536870912 268435456 hp771452 hp642702 hp771453 hp771454 hp642705

noncomputable def hp771456 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 726123894) (BSN.sinEvenQ 536870912) 0 3 hp771452 hp642702 hp771453 rfl rfl rfl

noncomputable def hp771457 := hp771455 hp771453 524131093 rfl rfl rfl rfl rfl rfl rfl rfl (hp771456 rfl)

noncomputable def hp771458 := @BSN.binarySplit_of_base3 (BSN.sinOddP 726123894) (BSN.sinOddQ 536870912) 0 3 hp771454 hp642705 hp771453 rfl rfl rfl

noncomputable def hp771459 := nat_lit 1325087190743104531440605677441

noncomputable def hp771460 := BSN.cos_dyadic_bound_f 33928223 536870912 2 1 536870912 268435456 hp771459 hp708767 hp771459 hp771459 hp708768

noncomputable def hp771461 := @BSN.binarySplit_of_base (BSN.cosEvenP 33928223) (BSN.cosEvenQ 536870912) 0 1 hp771459 hp708767 hp771459 rfl rfl rfl

noncomputable def hp771462 := hp771460 hp771459 535799200 rfl rfl rfl rfl rfl rfl rfl rfl (hp771461 rfl)

noncomputable def hp771463 := @BSN.binarySplit_of_base (BSN.cosOddP 33928223) (BSN.cosOddQ 536870912) 0 1 hp771459 hp708768 hp771459 rfl rfl rfl

noncomputable def hp771464 := hp771451 hd4911 hd4913 hd4915 hd4917 hd4918 (hp771457 (hp771458 rfl) rfl rfl rfl rfl) (hp771462 (hp771463 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771465 := hp771383 (BSN.cos_quad_nat0 220 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 49532833 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl rfl (hp771464 rfl rfl rfl rfl rfl) hp771450

noncomputable def hp771466 := nat_lit 19026881048857956433111048122259582739822733355597190731773654403961543943915802764034186608903314490588944850481

noncomputable def hp771467 := nat_lit 2627610294081785872131936452476801772172147790940631050660938572666618736701156516033157886204639908388401

noncomputable def hp771468 := nat_lit 115353723224741911884647879814384541350990983024251133136815841533279254586572408914712004999354721660375469579825

noncomputable def hp771469 := BSN.cos_dyadic_bound_f 609485549 536870912 4 3 536870912 268435456 hp771466 hp716712 hp771467 hp771468 hp716714

noncomputable def hp771470 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 609485549) (BSN.cosEvenQ 536870912) 0 3 hp771466 hp716712 hp771467 rfl rfl rfl

noncomputable def hp771471 := hp771469 hp771467 226506363 rfl rfl rfl rfl rfl rfl rfl rfl (hp771470 rfl)

noncomputable def hp771472 := @BSN.binarySplit_of_base3 (BSN.cosOddP 609485549) (BSN.cosOddQ 536870912) 0 3 hp771468 hp716714 hp771467 rfl rfl rfl

noncomputable def hp771473 := nat_lit 54823788734730526897748703090229310062468133410802309763745163307547657422105100096359544316673749073325232119521

noncomputable def hp771474 := nat_lit 62510350737063200274140472029587246122826564969167246054068969575452193709630494688726646143812342020988641

noncomputable def hp771475 := nat_lit 331968616637015833353678571361672792422022431012728985982198235202066820547522398187876024027291472285196583329505

noncomputable def hp771476 := BSN.cos_dyadic_bound_f 793711479 536870912 4 3 536870912 268435456 hp771473 hp716712 hp771474 hp771475 hp716714

noncomputable def hp771477 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 793711479) (BSN.cosEvenQ 536870912) 0 3 hp771473 hp716712 hp771474 rfl rfl rfl

noncomputable def hp771478 := hp771476 hp771474 49532833 rfl rfl rfl rfl rfl rfl rfl rfl (hp771477 rfl)

noncomputable def hp771479 := @BSN.binarySplit_of_base3 (BSN.cosOddP 793711479) (BSN.cosOddQ 536870912) 0 3 hp771475 hp716714 hp771474 rfl rfl rfl

noncomputable def hp771480 := hp771465 hd4920 hd4922 hd4924 hd4926 hd4918 (hp771471 (hp771472 rfl) rfl rfl rfl rfl) (hp771478 (hp771479 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771481 := hp771378 (BSN.cos_quad_nat1 25 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 203135452 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl rfl (hp771480 rfl rfl rfl rfl rfl) hp771450

noncomputable def hp771482 := nat_lit 46213368964002026903027133883613493475459710254172790665033854106011973856624909100471841439529560762146573254656

noncomputable def hp771483 := nat_lit 37491004550006543555413375914198483669440358071615270016379959409162282629405342409993364995940608771096576

noncomputable def hp771484 := nat_lit 279913779204360528360157806244970451801779308038513005755668544393840435491260651252213001924633695373694389452800

noncomputable def hp771485 := BSN.cos_dyadic_bound_f 760607476 536870912 4 3 536870912 268435456 hp771482 hp716712 hp771483 hp771484 hp716714

noncomputable def hp771486 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 760607476) (BSN.cosEvenQ 536870912) 0 3 hp771482 hp716712 hp771483 rfl rfl rfl

noncomputable def hp771487 := hp771485 hp771483 82380622 rfl rfl rfl rfl rfl rfl rfl rfl (hp771486 rfl)

noncomputable def hp771488 := @BSN.binarySplit_of_base3 (BSN.cosOddP 760607476) (BSN.cosOddQ 536870912) 0 3 hp771484 hp716714 hp771483 rfl rfl rfl

noncomputable def hp771489 := nat_lit 1883468699661548418721071227834896

noncomputable def hp771490 := BSN.sin_dyadic_bound_f 208324142 536870912 2 1 536870912 268435456 hp771489 hp708890 hp771489 hp771489 hp708891

noncomputable def hp771491 := @BSN.binarySplit_of_base (BSN.sinEvenP 208324142) (BSN.sinEvenQ 536870912) 0 1 hp771489 hp708890 hp771489 rfl rfl rfl

noncomputable def hp771492 := hp771490 hp771489 203135452 rfl rfl rfl rfl rfl rfl rfl rfl (hp771491 rfl)

noncomputable def hp771493 := @BSN.binarySplit_of_base (BSN.sinOddP 208324142) (BSN.sinOddQ 536870912) 0 1 hp771489 hp708891 hp771489 rfl rfl rfl

noncomputable def hp771494 := hp771481 hd4928 hd4930 hd4932 hd4934 hd4918 (hp771487 (hp771488 rfl) rfl rfl rfl rfl) (hp771492 (hp771493 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771495 := hp771374 (BSN.cos_quad_nat0 120 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 68242220 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl rfl (hp771494 rfl rfl rfl rfl rfl) hp771450

noncomputable def hp771496 := nat_lit 2106113722093997776039510217734955037404288149726794377788411266940231936

noncomputable def hp771497 := nat_lit 227662857055321769578086909424435898165290224055859944527895747584256

noncomputable def hp771498 := nat_lit 6317885840567882684579374479386016240416533868732271413476178009325527296

noncomputable def hp771499 := BSN.cos_dyadic_bound_f 350478614 536870912 3 2 536870912 268435456 hp771496 hp708868 hp771497 hp771498 hp708870

noncomputable def hp771500 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 350478614) (BSN.cosEvenQ 536870912) 0 2 hp771496 hp708868 hp771497 rfl rfl rfl

noncomputable def hp771501 := hp771499 hp771497 426477182 rfl rfl rfl rfl rfl rfl rfl rfl (hp771500 rfl)

noncomputable def hp771502 := @BSN.binarySplit_of_base2 (BSN.cosOddP 350478614) (BSN.cosOddQ 536870912) 0 2 hp771498 hp708870 hp771497 rfl rfl rfl

noncomputable def hp771503 := nat_lit 49792076015049951986235827843506160657934044906253079589657898071351957115840628770819577118793938264653824000000

noncomputable def hp771504 := nat_lit 46866659192543160252581530127560933197838392184166894567957225249624208825623571305857963524096000000000000

noncomputable def hp771505 := nat_lit 301552813698268969407132110598130000507931552392389457099941203624247596447677459876901210294542438808263065600000

noncomputable def hp771506 := BSN.cos_dyadic_bound_f 774887520 536870912 4 3 536870912 268435456 hp771503 hp716712 hp771504 hp771505 hp716714

noncomputable def hp771507 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 774887520) (BSN.cosEvenQ 536870912) 0 3 hp771503 hp716712 hp771504 rfl rfl rfl

noncomputable def hp771508 := hp771506 hp771504 68242220 rfl rfl rfl rfl rfl rfl rfl rfl (hp771507 rfl)

noncomputable def hp771509 := @BSN.binarySplit_of_base3 (BSN.cosOddP 774887520) (BSN.cosOddQ 536870912) 0 3 hp771505 hp716714 hp771504 rfl rfl rfl

noncomputable def hp771510 := hp771495 hd4936 hd4938 hd4940 hd4942 hd4918 (hp771501 (hp771502 rfl) rfl rfl rfl rfl) (hp771508 (hp771509 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771511 := hp771369 (BSN.cos_quad_nat1 237 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 448758043 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl rfl (hp771510 rfl rfl rfl rfl rfl) hp771450

noncomputable def hp771512 := nat_lit 106626662895940760169246073409543029242365215732745233543354597968510976

noncomputable def hp771513 := nat_lit 583645743527870640083049946156682409396040588855313353520091037696

noncomputable def hp771514 := nat_lit 319878821396335224766458054128736774362276855117057990003356753723457536

noncomputable def hp771515 := BSN.cos_dyadic_bound_f 166252684 536870912 3 2 536870912 268435456 hp771512 hp708868 hp771513 hp771514 hp708870

noncomputable def hp771516 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 166252684) (BSN.cosEvenQ 536870912) 0 2 hp771512 hp708868 hp771513 rfl rfl rfl

noncomputable def hp771517 := hp771515 hp771513 511334250 rfl rfl rfl rfl rfl rfl rfl rfl (hp771516 rfl)

noncomputable def hp771518 := @BSN.binarySplit_of_base2 (BSN.cosOddP 166252684) (BSN.cosOddQ 536870912) 0 2 hp771514 hp708870 hp771513 rfl rfl rfl

noncomputable def hp771519 := nat_lit 20032858222497588985528490271190197554658135164828249963631369904967833665

noncomputable def hp771520 := nat_lit 6354592409513597766503829314514039112208258899134883674505920354113601

noncomputable def hp771521 := nat_lit 52456721242640187232381230224703208960780112060142055331180578261009094721

noncomputable def hp771522 := BSN.sin_dyadic_bound_f 531356457 536870912 3 2 536870912 268435456 hp771519 hp708845 hp771520 hp771521 hp708848

noncomputable def hp771523 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 531356457) (BSN.sinEvenQ 536870912) 0 2 hp771519 hp708845 hp771520 rfl rfl rfl

noncomputable def hp771524 := hp771522 hp771520 448758043 rfl rfl rfl rfl rfl rfl rfl rfl (hp771523 rfl)

noncomputable def hp771525 := @BSN.binarySplit_of_base2 (BSN.sinOddP 531356457) (BSN.sinOddQ 536870912) 0 2 hp771521 hp708848 hp771520 rfl rfl rfl

noncomputable def hp771526 := hp771511 hd4944 hd4946 hd4961 hd4963 hd4918 (hp771517 (hp771518 rfl) rfl rfl rfl rfl) (hp771524 (hp771525 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp771527 := hp771364 500284942 Bool.false Bool.true 859958423 236330 BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 500284942 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl (hp771526 rfl rfl rfl rfl rfl)

noncomputable def hp771528 := nat_lit 220400935650898744087506639475363372406647530171578633215583692372068961

noncomputable def hp771529 := nat_lit 2493672883445823322897054823970565596403377166937872824669755165281

noncomputable def hp771530 := nat_lit 661197819606929340615874124316442176088749783760402023901101737605876321

noncomputable def hp771531 := BSN.cos_dyadic_bound_f 199344811 536870912 3 2 536870912 268435456 hp771528 hp708868 hp771529 hp771530 hp708870

noncomputable def hp771532 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 199344811) (BSN.cosEvenQ 536870912) 0 2 hp771528 hp708868 hp771529 rfl rfl rfl

noncomputable def hp771533 := hp771531 hp771529 500284942 rfl rfl rfl rfl rfl rfl rfl rfl (hp771532 rfl)

noncomputable def hp771534 := @BSN.binarySplit_of_base2 (BSN.cosOddP 199344811) (BSN.cosOddQ 536870912) 0 2 hp771530 hp708870 hp771529 rfl rfl rfl

noncomputable def hp771535 := hp771527 hp771450 hd5088 hd5090 hd4918 (hp771533 (hp771534 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp771536 := @hp771359 Bool.true 859958423 268435456 118165 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 913584 1000)) (Enclosure.sfrac Bool.false 913584 1000) 12) (@hp771361 118165 134217728 (hp771535 rfl rfl rfl) (hp771535 rfl rfl rfl) rfl rfl)

noncomputable def hp771537 := @Enclosure.Real.IsNear.mulLit_ff hp771350 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1))) 19325811 67108864 1

noncomputable def hp771538 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 12) (hp771349 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp771539 := @hp771538 1 1 0 1 19325811 67108864 1 67108864 19325811 67108864 1

noncomputable def hp771540 := @Enclosure.Real.IsNear.of_eq (hp771349 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp771541 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 913584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771542 := @hp771540 (@Inv.inv Real Real.instInv (Real.sqrt hp771351)) Bool.false 19325811 67108864 1 67108864 (hp771541 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 913584 1000) 913584 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000))))

noncomputable def hp771543 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp771351)) Bool.false 19325811 67108864 1 67108864 19325811 67108864

noncomputable def hp771544 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp771351) Bool.false 233035474 67108864 6 67108864 116517737 33554432 3 33554432

noncomputable def hp771545 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 913584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771546 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 913584 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp771547 := @hp771546 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 913584 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 609857688993

noncomputable def hp771548 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 913584 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 913584 1000 0

noncomputable def hp771549 := @hp771548 1 10680707 67108864 1 67108864 609857688993 4194304000 57099 4194304000 (Enclosure.Real.IsNear.const Bool.false 913584 1000) hd4949

noncomputable def hp771550 := @hp771547 4194304000 57099 4194304000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 913584 1000) 913584 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000))) (hp771549 rfl)

noncomputable def hp771551 := @hp771545 609857688993 4194304000 57099 4194304000 404607725 404607764 33554432 hp771550 rfl rfl rfl

noncomputable def hp771552 := @Enclosure.Real.IsNear.recentre' hp771351 Bool.false 809215489 67108864 39 67108864 809215489 67108864 39 67108864 (hp771551 rfl rfl rfl)

noncomputable def hp771553 := @Enclosure.Real.IsNear.sqrt_image hp771351 809215489 67108864 39 67108864 116517734 116517740 33554432 (hp771552 rfl) rfl rfl

noncomputable def hp771554 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp771351) 116517737 33554432 3 33554432 9662905 9662906 33554432 (hp771544 (hp771553 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp771555 := @hp771539 67108864 (@hp769737 1 0 1 (BSN.neg_one_pow_even_mk 12 rfl) (Enclosure.Real.IsNear.const Bool.false 1 1)) (hp771542 (@hp771543 1 67108864 (hp771554 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp771556 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp771557 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp771558 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1))) (hp771556 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771557 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp771559 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 913584 1000) 913584 1000 12 (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl

noncomputable def hp771560 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp771561 := @hp771560 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771557 (Enclosure.sfrac Bool.false 1 16)))) 35934483

noncomputable def hp771562 := @hp771561 33554432 145 33554432 24838135 33554432 95342777 22837985280000 892545539909205 1125899906842624 5877398290966331 766315624094760960000

noncomputable def hp771563 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)))))

noncomputable def hp771564 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)))) 31332019

noncomputable def hp771565 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)))) Bool.false

noncomputable def hp771566 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 24561731) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp771567 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1))) Bool.false 3456756419430895925155

noncomputable def hp771568 := nat_lit 210491388197259373290760669

noncomputable def hp771569 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)) 884279719003555 140737488355328 1

noncomputable def hp771570 := @Enclosure.Real.IsNear.subLit_ff_p hp771351 (Enclosure.sfrac Bool.false 12 1) 809215489 67108864 39 67108864 12 1 0

noncomputable def hp771571 := @hp771569 500000000000000 3909121 67108864 39 67108864 3456756419430895925155 9444732965739290427392 hp771568 hp645312 hd4948 (@hp771570 1 3909121 3909121 67108864 39 67108864 (hp771552 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771572 := @hp771566 24561731 67108864 123 33554432 Bool.false 31332019 33554432 1 10890000 (@hp771567 9444732965739290427392 hp771568 hp645312 24561731 67108864 123 33554432 (hp771571 rfl) rfl) (Enclosure.sfrac_false_div 24561731 67108864)

noncomputable def hp771573 := nat_lit 363945105072450205411311082321

noncomputable def hp771574 := BSN.cos_dyadic_bound_f 24561731 67108864 2 1 33554432 10890000 hp771573 hp740060 hp771573 hp771573 hp740061

noncomputable def hp771575 := @BSN.binarySplit_of_base (BSN.cosEvenP 24561731) (BSN.cosEvenQ 67108864) 0 1 hp771573 hp740060 hp771573 rfl rfl rfl

noncomputable def hp771576 := hp771574 hp771573 31332019 rfl rfl rfl rfl rfl rfl rfl rfl (hp771575 rfl)

noncomputable def hp771577 := @BSN.binarySplit_of_base (BSN.cosOddP 24561731) (BSN.cosOddQ 67108864) 0 1 hp771573 hp740061 hp771573 rfl rfl rfl

noncomputable def hp771578 := hp771572 (hp771576 (hp771577 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp771579 := @hp771564 33554432 85814027 22837985280000 35934338 35934628 33554432 (@hp771565 31332019 33554432 1373024432 365407764480000 31332019 33554432 85814027 22837985280000 hp771578 rfl)

noncomputable def hp771580 := @hp771563 Bool.false 71868966 67108864 290 67108864 35934483 33554432 145 33554432 (hp771579 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp771581 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771557 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp771582 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771557 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 49484589)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp771583 := nat_lit 467368730633863904257413617245

noncomputable def hp771584 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771557 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp771583

noncomputable def hp771585 := nat_lit 78857593825560764434417489829368313

noncomputable def hp771586 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp771557 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp771587 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)))

noncomputable def hp771588 := @hp771587 (Enclosure.sfrac Bool.false 1 16) 247055442555903 4503599627370496 2922158655 4503599627370496 1 16 0

noncomputable def hp771589 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)) 15281226992641

noncomputable def hp771590 := @hp771589 4503599627370496 304912959 4503599627370496 3909121 67108864 39 67108864 16579610094943906824192 247055442555903 4503599627370496 2922158655

noncomputable def hp771591 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)) 3909121 67108864 39

noncomputable def hp771592 := @hp771591 67108864 3909121 67108864 39 67108864 15281226992641 4503599627370496 304912959 4503599627370496 (@hp771570 1 3909121 3909121 67108864 39 67108864 (hp771552 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771593 := hp771592 (@hp771570 1 3909121 3909121 67108864 39 67108864 (hp771552 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771594 := @hp771590 4503599627370496 (hp771593 rfl) (@hp771570 1 3909121 3909121 67108864 39 67108864 (hp771552 rfl) (Enclosure.Real.IsNear.const Bool.false 12 1) rfl rfl)

noncomputable def hp771595 := @hp771586 500000000000000 528530419266559 4503599627370496 2922158655 4503599627370496 hp771583 hp627574 hp771585 hp738055 hd4948 (@hp771588 1 8456486708264944 528530419266559 4503599627370496 2922158655 4503599627370496 (hp771594 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp771596 := @hp771582 49484589 67108864 137 33554432 Bool.false 24838135 33554432 1 10890000 (@hp771584 hp627574 hp771585 hp738055 49484589 67108864 137 33554432 (hp771595 rfl) rfl) (Enclosure.sfrac_true_div 49484589 67108864)

noncomputable def hp771597 := nat_lit 204354929894174435549782758058495190152739749037856525791141584161

noncomputable def hp771598 := nat_lit 35955037021200439731008411260745013722050673122679921891106081

noncomputable def hp771599 := nat_lit 612992879608480905769886257352964080430775145767324217529642540321

noncomputable def hp771600 := BSN.cos_dyadic_bound_f 49484589 67108864 3 2 33554432 10890000 hp771597 hp738066 hp771598 hp771599 hp738069

noncomputable def hp771601 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 49484589) (BSN.cosEvenQ 67108864) 0 2 hp771597 hp738066 hp771598 rfl rfl rfl

noncomputable def hp771602 := hp771600 hp771598 24838135 rfl rfl rfl rfl rfl rfl rfl rfl (hp771601 rfl)

noncomputable def hp771603 := @BSN.binarySplit_of_base2 (BSN.cosOddP 49484589) (BSN.cosOddQ 67108864) 0 2 hp771599 hp738069 hp771598 rfl rfl rfl

noncomputable def hp771604 := hp771596 (BSN.cos_neg_of_bound 49484589 67108864 Bool.false 24838135 33554432 1 10890000 (hp771602 (hp771603 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp771605 := hp771562 hp771580 (@hp771581 24838135 33554432 1525484432 365407764480000 24838135 33554432 95342777 22837985280000 (hp771604 rfl) rfl)

noncomputable def hp771606 := @hp771537 67108864 892545539909205 1125899906842624 5877398290966331 766315624094760960000 17249166413178252990255 75557863725914323419136 10381180293494301262627 hp771347 (hp771555 rfl) (@hp771558 Bool.false 892545539909205 1125899906842624 5877398290966331 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp771351 (Enclosure.sfrac Bool.false 12 1)) (hp771559 rfl (hp771354 rfl rfl))) (hp771605 rfl))

noncomputable def hp771607 := @hp771348 hp771345 hp771347 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 913584 1000))) (@hp771353 hp771345 hp771347 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 913584 1000) 12 (hp771354 rfl rfl)) (@hp771357 hp771345 hp771347 hp771536 (hp771606 rfl) rfl rfl))

theorem hd5098 : hp771346 hp771347 := hp771607

noncomputable def hp790762 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) Bool.false 556919581 10737418240 1213 10737418240

noncomputable def hp793797 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) 906639 1000 907903 1000

noncomputable def hp793798 := hp793797 (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl rfl rfl

noncomputable def hp793799 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798))

noncomputable def hp793800 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 906639 1000) 906639 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl rfl

noncomputable def hp793801 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798))

noncomputable def hp793802 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798)) 652345635981816454823077

noncomputable def hp793803 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 906639 1000))

noncomputable def hp793804 := @hp793802 151115727451828646838272 hp769801 hp755229 (@hp793803 Bool.true 652345635981816454823077 151115727451828646838272 hp769801 hp755229 (hd4340 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798) hd5092)

noncomputable def hp793805 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798)) 26527206859214920030045

noncomputable def hp793806 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 907903 1000))

noncomputable def hp793807 := @hp793805 37778931862957161709568 227783628409128725737721 hp756508 (@hp793806 Bool.false 26527206859214920030045 37778931862957161709568 227783628409128725737721 hp756508 (hd4359 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798) hd5093)

noncomputable def hp793808 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798) hp793800 (hp793801 (hp793804 rfl rfl rfl) (hp793807 rfl rfl rfl))

noncomputable def hp793809 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793810 := hp793809 (Enclosure.sfrac Bool.false 906639 1000) 749551 1000 906639 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793811 := hp793810 (@Eq.refl Real (Enclosure.sfrac Bool.false 906639 1000)) rfl rfl rfl rfl

noncomputable def hp793812 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793813 := @hp793812 Bool.true Bool.false 652345635981816454823077 151115727451828646838272 hp769801 hp755229 556919581 10737418240 1213 10737418240 (@hp793803 Bool.true 652345635981816454823077 151115727451828646838272 hp769801 hp755229 (hd4340 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798) hd5092)

noncomputable def hp793814 := hp793813 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793815 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793816 := hp793815 (Enclosure.sfrac Bool.false 907903 1000) 749551 1000 907903 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793817 := hp793816 (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl rfl rfl rfl

noncomputable def hp793818 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793819 := @hp793818 Bool.false Bool.false 26527206859214920030045 37778931862957161709568 227783628409128725737721 hp756508 556919581 10737418240 1213 10737418240 (@hp793806 Bool.false 26527206859214920030045 37778931862957161709568 227783628409128725737721 hp756508 (hd4359 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798) hd5093)

noncomputable def hp793820 := hp793819 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793822 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) 907903 1000 909166 1000

noncomputable def hp793823 := hp793822 (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl rfl rfl

noncomputable def hp793824 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823))

noncomputable def hp793825 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 907903 1000) 907903 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl rfl

noncomputable def hp793826 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823))

noncomputable def hp793827 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823)) 26527206859214920030045

noncomputable def hp793828 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 907903 1000))

noncomputable def hp793829 := @hp793827 37778931862957161709568 227783628409128725737721 hp756508 (@hp793828 Bool.false 26527206859214920030045 37778931862957161709568 227783628409128725737721 hp756508 (hd4340 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823) hd5093)

noncomputable def hp793830 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823)) 133258922115036277105549

noncomputable def hp793831 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 909166 1000))

noncomputable def hp793832 := @hp793830 37778931862957161709568 hp770314 hp740088 (@hp793831 Bool.true 133258922115036277105549 37778931862957161709568 hp770314 hp740088 (hd4359 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823) hd5094)

noncomputable def hp793833 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823) hp793825 (hp793826 (hp793829 rfl rfl rfl) (hp793832 rfl rfl rfl))

noncomputable def hp793834 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793835 := hp793834 (Enclosure.sfrac Bool.false 907903 1000) 749551 1000 907903 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793836 := hp793835 (@Eq.refl Real (Enclosure.sfrac Bool.false 907903 1000)) rfl rfl rfl rfl

noncomputable def hp793837 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793838 := @hp793837 Bool.false Bool.false 26527206859214920030045 37778931862957161709568 227783628409128725737721 hp756508 556919581 10737418240 1213 10737418240 (@hp793828 Bool.false 26527206859214920030045 37778931862957161709568 227783628409128725737721 hp756508 (hd4340 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823) hd5093)

noncomputable def hp793839 := hp793838 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793840 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793841 := hp793840 (Enclosure.sfrac Bool.false 909166 1000) 749551 1000 909166 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793842 := hp793841 (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl rfl rfl rfl

noncomputable def hp793843 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793844 := @hp793843 Bool.true Bool.false 133258922115036277105549 37778931862957161709568 hp770314 hp740088 556919581 10737418240 1213 10737418240 (@hp793831 Bool.true 133258922115036277105549 37778931862957161709568 hp770314 hp740088 (hd4359 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823) hd5094)

noncomputable def hp793845 := hp793844 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793847 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) 909166 1000 910429 1000

noncomputable def hp793848 := hp793847 (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl rfl rfl

noncomputable def hp793849 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848))

noncomputable def hp793850 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 909166 1000) 909166 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl rfl

noncomputable def hp793851 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848))

noncomputable def hp793852 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848)) 133258922115036277105549

noncomputable def hp793853 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 909166 1000))

noncomputable def hp793854 := @hp793852 37778931862957161709568 hp770314 hp740088 (@hp793853 Bool.true 133258922115036277105549 37778931862957161709568 hp770314 hp740088 (hd4340 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848) hd5094)

noncomputable def hp793855 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848)) 15478527489335219082355

noncomputable def hp793856 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 910429 1000))

noncomputable def hp793857 := @hp793855 18889465931478580854784 hp770574 hp758057 (@hp793856 Bool.false 15478527489335219082355 18889465931478580854784 hp770574 hp758057 (hd4359 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848) hd5095)

noncomputable def hp793858 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848) hp793850 (hp793851 (hp793854 rfl rfl rfl) (hp793857 rfl rfl rfl))

noncomputable def hp793859 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793860 := hp793859 (Enclosure.sfrac Bool.false 909166 1000) 749551 1000 909166 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793861 := hp793860 (@Eq.refl Real (Enclosure.sfrac Bool.false 909166 1000)) rfl rfl rfl rfl

noncomputable def hp793862 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793863 := @hp793862 Bool.true Bool.false 133258922115036277105549 37778931862957161709568 hp770314 hp740088 556919581 10737418240 1213 10737418240 (@hp793853 Bool.true 133258922115036277105549 37778931862957161709568 hp770314 hp740088 (hd4340 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848) hd5094)

noncomputable def hp793864 := hp793863 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793865 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793866 := hp793865 (Enclosure.sfrac Bool.false 910429 1000) 749551 1000 910429 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793867 := hp793866 (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl rfl rfl rfl

noncomputable def hp793868 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793869 := @hp793868 Bool.false Bool.false 15478527489335219082355 18889465931478580854784 hp770574 hp758057 556919581 10737418240 1213 10737418240 (@hp793856 Bool.false 15478527489335219082355 18889465931478580854784 hp770574 hp758057 (hd4359 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848) hd5095)

noncomputable def hp793870 := hp793869 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793872 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) 910429 1000 912007 1000

noncomputable def hp793873 := hp793872 (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl rfl rfl

noncomputable def hp793874 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873))

noncomputable def hp793875 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 910429 1000) 910429 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl rfl

noncomputable def hp793876 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873))

noncomputable def hp793877 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873)) 15478527489335219082355

noncomputable def hp793878 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 910429 1000))

noncomputable def hp793879 := @hp793877 18889465931478580854784 hp770574 hp758057 (@hp793878 Bool.false 15478527489335219082355 18889465931478580854784 hp770574 hp758057 (hd4340 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873) hd5095)

noncomputable def hp793880 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873)) 2610499849347264810517

noncomputable def hp793881 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912007 1000))

noncomputable def hp793882 := @hp793880 4722366482869645213696 hp770827 hp754729 (@hp793881 Bool.true 2610499849347264810517 4722366482869645213696 hp770827 hp754729 (hd4359 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873) hd5096)

noncomputable def hp793883 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873) hp793875 (hp793876 (hp793879 rfl rfl rfl) (hp793882 rfl rfl rfl))

noncomputable def hp793884 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793885 := hp793884 (Enclosure.sfrac Bool.false 910429 1000) 749551 1000 910429 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793886 := hp793885 (@Eq.refl Real (Enclosure.sfrac Bool.false 910429 1000)) rfl rfl rfl rfl

noncomputable def hp793887 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793888 := @hp793887 Bool.false Bool.false 15478527489335219082355 18889465931478580854784 hp770574 hp758057 556919581 10737418240 1213 10737418240 (@hp793878 Bool.false 15478527489335219082355 18889465931478580854784 hp770574 hp758057 (hd4340 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873) hd5095)

noncomputable def hp793889 := hp793888 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793890 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793891 := hp793890 (Enclosure.sfrac Bool.false 912007 1000) 749551 1000 912007 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793892 := hp793891 (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl rfl rfl rfl

noncomputable def hp793893 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793894 := @hp793893 Bool.true Bool.false 2610499849347264810517 4722366482869645213696 hp770827 hp754729 556919581 10737418240 1213 10737418240 (@hp793881 Bool.true 2610499849347264810517 4722366482869645213696 hp770827 hp754729 (hd4359 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873) hd5096)

noncomputable def hp793895 := hp793894 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793897 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) 912007 1000 912638 1000

noncomputable def hp793898 := hp793897 (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl rfl rfl

noncomputable def hp793899 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898))

noncomputable def hp793900 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 912007 1000) 912007 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl rfl

noncomputable def hp793901 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898))

noncomputable def hp793902 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898)) 2610499849347264810517

noncomputable def hp793903 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912007 1000))

noncomputable def hp793904 := @hp793902 4722366482869645213696 hp770827 hp754729 (@hp793903 Bool.true 2610499849347264810517 4722366482869645213696 hp770827 hp754729 (hd4340 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898) hd5096)

noncomputable def hp793905 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898)) 2146514721796653684545

noncomputable def hp793906 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912638 1000))

noncomputable def hp793907 := @hp793905 9444732965739290427392 1133571679730292553833161 hp764965 (@hp793906 Bool.false 2146514721796653684545 9444732965739290427392 1133571679730292553833161 hp764965 (hd4359 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898) hd5097)

noncomputable def hp793908 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898) hp793900 (hp793901 (hp793904 rfl rfl rfl) (hp793907 rfl rfl rfl))

noncomputable def hp793909 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793910 := hp793909 (Enclosure.sfrac Bool.false 912007 1000) 749551 1000 912007 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793911 := hp793910 (@Eq.refl Real (Enclosure.sfrac Bool.false 912007 1000)) rfl rfl rfl rfl

noncomputable def hp793912 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793913 := @hp793912 Bool.true Bool.false 2610499849347264810517 4722366482869645213696 hp770827 hp754729 556919581 10737418240 1213 10737418240 (@hp793903 Bool.true 2610499849347264810517 4722366482869645213696 hp770827 hp754729 (hd4340 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898) hd5096)

noncomputable def hp793914 := hp793913 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793915 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793916 := hp793915 (Enclosure.sfrac Bool.false 912638 1000) 749551 1000 912638 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793917 := hp793916 (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl rfl rfl rfl

noncomputable def hp793918 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793919 := @hp793918 Bool.false Bool.false 2146514721796653684545 9444732965739290427392 1133571679730292553833161 hp764965 556919581 10737418240 1213 10737418240 (@hp793906 Bool.false 2146514721796653684545 9444732965739290427392 1133571679730292553833161 hp764965 (hd4359 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898) hd5097)

noncomputable def hp793920 := hp793919 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793922 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) 912638 1000 913584 1000

noncomputable def hp793923 := hp793922 (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl rfl rfl

noncomputable def hp793924 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923))

noncomputable def hp793925 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 912638 1000) 912638 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl rfl

noncomputable def hp793926 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923))

noncomputable def hp793927 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923)) 2146514721796653684545

noncomputable def hp793928 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 912638 1000))

noncomputable def hp793929 := @hp793927 9444732965739290427392 1133571679730292553833161 hp764965 (@hp793928 Bool.false 2146514721796653684545 9444732965739290427392 1133571679730292553833161 hp764965 (hd4340 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923) hd5097)

noncomputable def hp793930 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923)) 259305943499235714045743

noncomputable def hp793931 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 913584 1000))

noncomputable def hp793932 := @hp793930 75557863725914323419136 hp771345 hp771347 (@hp793931 Bool.true 259305943499235714045743 75557863725914323419136 hp771345 hp771347 (hd4359 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923) hd5098)

noncomputable def hp793933 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923) hp793925 (hp793926 (hp793929 rfl rfl rfl) (hp793932 rfl rfl rfl))

noncomputable def hp793934 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793935 := hp793934 (Enclosure.sfrac Bool.false 912638 1000) 749551 1000 912638 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793936 := hp793935 (@Eq.refl Real (Enclosure.sfrac Bool.false 912638 1000)) rfl rfl rfl rfl

noncomputable def hp793937 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793938 := @hp793937 Bool.false Bool.false 2146514721796653684545 9444732965739290427392 1133571679730292553833161 hp764965 556919581 10737418240 1213 10737418240 (@hp793928 Bool.false 2146514721796653684545 9444732965739290427392 1133571679730292553833161 hp764965 (hd4340 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923) hd5097)

noncomputable def hp793939 := hp793938 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793940 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793941 := hp793940 (Enclosure.sfrac Bool.false 913584 1000) 749551 1000 913584 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793942 := hp793941 (@Eq.refl Real (Enclosure.sfrac Bool.false 913584 1000)) rfl rfl rfl rfl

noncomputable def hp793943 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793944 := @hp793943 Bool.true Bool.false 259305943499235714045743 75557863725914323419136 hp771345 hp771347 556919581 10737418240 1213 10737418240 (@hp793931 Bool.true 259305943499235714045743 75557863725914323419136 hp771345 hp771347 (hd4359 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923) hd5098)

noncomputable def hp793945 := hp793944 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl
open Zeta.Certificates
noncomputable def certificatePairs : List (Σ' I : ZIntervalRS, I.Certified) := [(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 906639 1000) (Enclosure.sfrac Bool.false 907903 1000) hp793798) (hp793799 (hp793808 (hp793811 (hp793814 rfl rfl)) (hp793817 (hp793820 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 907903 1000) (Enclosure.sfrac Bool.false 909166 1000) hp793823) (hp793824 (hp793833 (hp793836 (hp793839 rfl rfl)) (hp793842 (hp793845 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 909166 1000) (Enclosure.sfrac Bool.false 910429 1000) hp793848) (hp793849 (hp793858 (hp793861 (hp793864 rfl rfl)) (hp793867 (hp793870 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 910429 1000) (Enclosure.sfrac Bool.false 912007 1000) hp793873) (hp793874 (hp793883 (hp793886 (hp793889 rfl rfl)) (hp793892 (hp793895 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 912007 1000) (Enclosure.sfrac Bool.false 912638 1000) hp793898) (hp793899 (hp793908 (hp793911 (hp793914 rfl rfl)) (hp793917 (hp793920 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 912638 1000) (Enclosure.sfrac Bool.false 913584 1000) hp793923) (hp793924 (hp793933 (hp793936 (hp793939 rfl rfl)) (hp793942 (hp793945 rfl rfl)))))]

theorem solution : Zeta.Certificates.BatchSpec 6 906639 1000 913584 1000 :=
  ⟨CertifiedZeroIntervals.ofCertifiedRS certificatePairs (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.singleton _)))))), rfl, rfl, rfl⟩
#print axioms solution
