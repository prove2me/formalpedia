-- Prove2me | solution 1 for RHHeight1000.rs_main_0475_0486
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:38:05.928873+00:00
-- url     : https://prove2.me/submissions/d1764a17-ebb9-45a5-a7ad-9f8fe104b4d4

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

noncomputable def hp631146 := nat_lit 39614081257132168796771975168

noncomputable def hp633059 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600

noncomputable def hp633062 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600

noncomputable def hp633286 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600

noncomputable def hp633289 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600

noncomputable def hp642702 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800

noncomputable def hp642705 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000

noncomputable def hp645312 := nat_lit 57646075230342348800000000000000

noncomputable def hp681368 := @BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl

noncomputable def hp681432 := @BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl

noncomputable def hp681868 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600

noncomputable def hp681871 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600

noncomputable def hp682141 := nat_lit 158456325028528675187087900672

noncomputable def hp682143 := nat_lit 4835703278458516698824704000000000000000

noncomputable def hp682805 := nat_lit 144115188075855872000000000000000

noncomputable def hp684593 := nat_lit 5764607523034234880000000000000

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

noncomputable def hp738860 := nat_lit 51426570998450436377149440000

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

noncomputable def hp740177 := nat_lit 21759806992472160846509436431027924547665573599712653161483140986990306751823661669370177199848368120331884066839754328502985489716814125465600

noncomputable def hp740180 := nat_lit 1980142436314966637032358715223541133837567197573851437694965829816117914415953211912686125186201498950201450082417643893771679564230085417369600

noncomputable def hp740271 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (Enclosure.sfrac Bool.true 1 1) Bool.true 1

noncomputable def hp740893 := nat_lit 2973696000000000000000000

noncomputable def hp741590 := nat_lit 17142190332816812125716480000

noncomputable def hp742826 := nat_lit 3868562622766813359059763200000000000000

noncomputable def hp743344 := nat_lit 5142657099845043637714944000

noncomputable def hp743892 := nat_lit 1622016000000000000000000

noncomputable def hp745658 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600

noncomputable def hp745661 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600

noncomputable def hp746621 := nat_lit 5133330660362904937396483134791632965849700352038159351603073932373040875403608499582161387520

noncomputable def hp746624 := nat_lit 230999879716330722182841741065623483463236515841717170822138326956786839393162382481197262438400

noncomputable def hp746784 := nat_lit 77919046967349146025984000

noncomputable def hp747268 := nat_lit 773712524553362671811952640000000000000

noncomputable def hp749778 := nat_lit 42817430781178796431748579083484854091482398720

noncomputable def hp749779 := nat_lit 299722015468251575022240053584393978640376791040

noncomputable def hp750331 := nat_lit 1071386895801050757857280000

noncomputable def hp751106 := nat_lit 571406344427227070857216000

noncomputable def hp752921 := nat_lit 114281268885445414171443200

noncomputable def hp753999 := nat_lit 1486848000000000000000000

noncomputable def hp755229 := nat_lit 102853141996900872754298880000

noncomputable def hp757535 := nat_lit 13159671718668153693571157

noncomputable def hp757536 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 845556 1000)) Bool.true 76793180622600504301829 37778931862957161709568 hp757535

noncomputable def hp757537 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 845556 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 845556 1000)) Bool.true 76793180622600504301829 37778931862957161709568

noncomputable def hp757538 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 845556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757539 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp757538 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757540 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 845556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757541 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp757539 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp757542 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 845556 1000)) hp757541 Bool.true 76793180622600504301829 37778931862957161709568

noncomputable def hp757543 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 845556 1000) 845556 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl

noncomputable def hp757544 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp757539 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp757545 := nat_lit 20614012458118130278091429249024

noncomputable def hp757546 := @hp757544 577221523 268435456 102587 134217728 4443526749056689022715 37778931862957161709568 57334897166613259651157 hp741590 hp757545 76793180622600504301829 37778931862957161709568

noncomputable def hp757547 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) 11)

noncomputable def hp757548 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) 11) hp757547

noncomputable def hp757549 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) 11)

noncomputable def hp757550 := @hp757549 577221523 536870912 205174 536870912 577221523 536870912 205174 536870912 619786890958077952 577221523 268435456

noncomputable def hp757551 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp757552 := hp757551 BSN.quadSignPos 9 10 11 845556 1000 189 240 536870912 268435456 9007199254740992

noncomputable def hp757553 := hp757552 Bool.false 885480892024 3853 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp757554 := hp757553 Bool.true 516388171 176136 Bool.true 401280082 Bool.true 658700590 28296951008113761 1 Bool.false 364946143

noncomputable def hp757555 := hp757554 Bool.true Bool.false 180997364 Bool.false Bool.true 577221523 205174 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 364946143 536870912) BSN.abs_quadSignPos

noncomputable def hp757556 := hp757551 BSN.quadSignPos 7 8 9 845556 1000 69 132 536870912 268435456 9007199254740992

noncomputable def hp757557 := hp757556 Bool.false 885480892024 3853 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp757558 := hp757557 Bool.true 480885307 143849 Bool.true 302062867 Bool.true 641345000 28296951008113761 1 Bool.false 286376424

noncomputable def hp757559 := hp757558 Bool.true Bool.false 197239487 Bool.false Bool.true 516388171 176136 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 286376424 536870912) BSN.abs_quadSignPos

noncomputable def hp757560 := hp757551 BSN.quadSignNeg 5 6 7 845556 1000 85 2 536870912 268435456 9007199254740992

noncomputable def hp757561 := hp757560 Bool.false 885480892024 3853 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp757562 := hp757561 Bool.true 187238354 106896 Bool.false 422003229 Bool.false 439760553 28296951008113761 1 Bool.false 379869501

noncomputable def hp757563 := hp757562 Bool.true Bool.false 366610845 Bool.true Bool.true 480885307 143849 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 85 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 379869501 536870912) BSN.abs_quadSignNeg

noncomputable def hp757564 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp757565 := hp757564 BSN.quadSignPos 3 4 5 845556 1000 303 183 536870912 268435456 9007199254740992

noncomputable def hp757566 := hp757565 Bool.false 885480892024 3853 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp757567 := hp757566 Bool.true 640492113 63180 Bool.false 642048440 Bool.false 542831225 28296951008113761 1 Bool.false 499584513

noncomputable def hp757568 := hp757567 Bool.false Bool.false 454953759 Bool.false Bool.true 187238354 106896 BSN.abs_quadSignPos (BSN.cos_quad_nat3 303 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 499584513 536870912) BSN.abs_quadSignPos

noncomputable def hp757569 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp757570 := hp757569 BSN.quadSignNeg 1 2 3 845556 1000 676 458 536870912 268435456 9007199254740992

noncomputable def hp757571 := hp757570 Bool.false 885480892024 3853 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp757572 := hp757571 Bool.true 536870832 3906 Bool.false 742834745 Bool.false 522786997 28296951008113761 1 Bool.false 99894528

noncomputable def hp757573 := hp757572 Bool.false Bool.false 301822631 Bool.true Bool.true 640492113 63180 BSN.abs_quadSignPos (BSN.cos_quad_nat0 676 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 99894528 536870912) BSN.abs_quadSignNeg

noncomputable def hp757574 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) 1) Bool.true

noncomputable def hp757575 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)))

noncomputable def hp757576 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000))) Bool.true 67108854 67108864

noncomputable def hp757577 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 110685111503) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 110685111503 67108864

noncomputable def hp757578 := nat_lit 82846443312942949833910488637136292796008777930821539

noncomputable def hp757579 := nat_lit 50230158525145433915764838057468625853173727232000

noncomputable def hp757580 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) Bool.false hp757578 hp757579 2909201112988024577

noncomputable def hp757581 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 845556 4000) (Real.log (Enclosure.sfrac Bool.false 2859860796544 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1691112))))))

noncomputable def hp757582 := nat_lit 207469136849377640978822098452480000

noncomputable def hp757583 := nat_lit 1052560812622096634567444078897167073280

noncomputable def hp757584 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp757581 (Enclosure.sfrac Bool.false 845556 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 845556 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp757582 hp757583)) Bool.false

noncomputable def hp757585 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 845556 1000) 845556 1000 2859860796544 16000000 1691112

noncomputable def hp757586 := hp757585 4000 2000 hp757582 hp757583 (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl rfl rfl rfl

noncomputable def hp757587 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp757581 (Enclosure.sfrac Bool.false 845556 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 845556 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp757582 hp757583) 7427952982383259053467 4503599627370496000

noncomputable def hp757588 := nat_lit 7818371292898121990853827207985644281938093029483021347061760

noncomputable def hp757589 := @hp757587 2909201112988024577 405504000000000000000000 hp757582 hp757583 0 1 hp757588 hp757578 hp757579 2909201112988024577 405504000000000000000000

noncomputable def hp757590 := @Enclosure.Real.IsNear.subLit_ff_p (hp757581 (Enclosure.sfrac Bool.false 845556 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 845556 2000) (Real.log Real.pi)) 9607544827985573473691 4503599627370496000 121243927890031 49500000000000000000

noncomputable def hp757591 := nat_lit 124620371623288131923971407872000

noncomputable def hp757592 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 845556 4000) (Real.log (Enclosure.sfrac Bool.false 2859860796544 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1691112))))))

noncomputable def hp757593 := @hp757592 (Enclosure.sfrac Bool.false 845556 2000) 11511567671246017031579 4503599627370496000 121243927890031 49500000000000000000 845556 2000 0

noncomputable def hp757594 := nat_lit 19215089655971146947382000

noncomputable def hp757595 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 845556 4000) (Real.log (Enclosure.sfrac Bool.false 2859860796544 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1691112))))) 11513335564930538829579

noncomputable def hp757596 := nat_lit 25921745937336905352290397973582446592

noncomputable def hp757597 := @hp757595 4503599627370496000 880788804481519 363000000000000000000 883946842260899 2251799813685248 200000001089 8712000000000000000 hp757596 11511567671246017031579 4503599627370496000 121243927890031

noncomputable def hp757598 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 845556 4000) (Real.log (Enclosure.sfrac Bool.false 2859860796544 16000000)) 845556 4000 0 1 54465159326788711 4503599627370496

noncomputable def hp757599 := nat_lit 116963039039993445223497728

noncomputable def hp757600 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2859860796544) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp757599 hp617687

noncomputable def hp757601 := BSN.log_rat_reduce_isNear 2859860796544 16000000 17 5719721593088 4194304000000 83266723 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp757602 := nat_lit 344502302451005649648584067657845486999100323556774737210520401911631084283556290195786522169112128389120

noncomputable def hp757603 := nat_lit 2757900635929837763986119386396091695145677115402908905797145342517783085057793775407322460403431112704

noncomputable def hp757604 := nat_lit 12024287209741605761872865496356438242486788322440157335640847763334979677477731361811471196487680

noncomputable def hp757605 := BSN.log_dyadic_bound 762708796544 4957012796544 5 4 hp757602 268435456 87120000 hp757603 hp757604 83266723 5719721593088

noncomputable def hp757606 := hp757605 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp757607 := @BSN.binarySplit_of_base4 (BSN.artanhP 762708796544) (BSN.artanhQ 4957012796544) 0 4 hp757603 hp757602 hp757604 rfl rfl rfl

noncomputable def hp757608 := hp757601 rfl rfl rfl rfl (hp757606 (hp757607 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp757609 := @hp757598 12500018513 1089000000000000000 11513335564930538829579 4503599627370496000 880788804481519 363000000000000000000 (Enclosure.Real.IsNear.const Bool.false 845556 4000) (BSN.isNear_log_sfrac 2859860796544 16000000 54465159326788711 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp757600 1000001481040000 87120000000000000000000 54465159326788711 4503599627370496 12500018513 1089000000000000000 (hp757608 rfl rfl rfl) rfl)) rfl

noncomputable def hp757610 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1691112)))) 1 4

noncomputable def hp757611 := @hp757610 0 1 883946842260899 562949953421312 200000001089 2178000000000000000 883946842260899 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp757612 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1691112))) 884279719003555 562949953421312 1

noncomputable def hp757613 := @hp757612 2000000000000000 19841 33554432 1 10890000 29660334210258061754368 883946842260899 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp757614 := BSN.arctan_dyadic_bound_f 1000 1691112 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp757615 := hp757614 1 19841 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1691112) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1691112) 0 0 rfl)

noncomputable def hp757616 := hp757611 (hp757613 (hp757615 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp757617 := @hp757590 8119612357029 16777216000 634167 134217728000 hp757591 7427952982383259053467 4503599627370496000 2909201112988024577 405504000000000000000000 (@hp757593 1 hp757594 9607544827985573473691 4503599627370496000 121243927890031 49500000000000000000 (@hp757597 49500000000000000000 hp757609 hp757616 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 845556 2000) rfl rfl)

noncomputable def hp757618 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 845556 2000) (Real.log Real.pi) 845556 2000 0 1 38410761 33554432

noncomputable def hp757619 := hp757617 (@hp757618 3 268435456 8119612357029 16777216000 634167 134217728000 (Enclosure.Real.IsNear.const Bool.false 845556 2000) hd4909 rfl) rfl

noncomputable def hp757620 := @hp757580 405504000000000000000000 110685111503 67108864 241 33554432 (@hp757584 hp757578 hp757579 2909201112988024577 405504000000000000000000 (hp757586 rfl rfl rfl rfl rfl) (hp757589 (hp757619 rfl) (Enclosure.Real.IsNear.const Bool.true hp757582 hp757583) rfl rfl)) rfl

noncomputable def hp757621 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 110685111503) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 5272179301796980719616) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp757622 := BSN.sin_reduce_arg_pos_rat_q2 110685111503 67108864 226375608064910080 72057594037927936 262 5272179301796980719616 hp617687 rfl rfl rfl rfl

noncomputable def hp757623 := BSN.cos_dyadic_bound_f 74922174 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp757624 := hp757623 1 67108854 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 74922174) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp757625 := hp757624 (@BSN.binarySplit_of_le (BSN.cosOddP 74922174) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp757626 := @BSN.cos_arg_round Bool.false 67108854 67108864 5272179301796980719616 hp617687 74922174 137438953472 21801270 21780000 hp757625 rfl

noncomputable def hp757627 := hp757621 67108854 67108864 262 1000000000000000 21780000 10890000 hp757622 BSN.pi_near_15 hp757626 rfl rfl

noncomputable def hp757628 := @hp757577 241 33554432 Bool.true 67108854 67108864 1 10890000 hp757620 (Enclosure.sfrac_false_div 110685111503 67108864) (hp757627 rfl rfl) rfl

noncomputable def hp757629 := @hp757574 33554427 33554432 166127777 22837985280000 536870832 536870912 3906 536870912 (@hp757575 Bool.true 33554427 33554432 166127777 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000)) (@hp757576 2658044432 365407764480000 33554427 33554432 166127777 22837985280000 (hp757628 rfl) rfl))

noncomputable def hp757630 := @hp757580 405504000000000000000000 885480892024 536870912 3853 536870912 (@hp757584 hp757578 hp757579 2909201112988024577 405504000000000000000000 (hp757586 rfl rfl rfl rfl rfl) (hp757589 (hp757619 rfl) (Enclosure.Real.IsNear.const Bool.true hp757582 hp757583) rfl rfl)) rfl

noncomputable def hp757631 := hp757573 (BSN.cos_quad_nat2 458 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 301822631 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl rfl (hp757629 rfl) hp757630

noncomputable def hp757632 := nat_lit 42033957403157033749361127138862073056903757499807622173976037312113835441539954577618977878340684109683629390625

noncomputable def hp757633 := nat_lit 28229715954232129063281437445992559006125265196675357093136177147594262449081440327199806523537988525390625

noncomputable def hp757634 := nat_lit 254635787883586436844153177328455906978222833331318998102172038335765369902583968960629554697270863247390022990625

noncomputable def hp757635 := BSN.cos_dyadic_bound_f 742834745 536870912 4 3 536870912 268435456 hp757632 hp716712 hp757633 hp757634 hp716714

noncomputable def hp757636 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 742834745) (BSN.cosEvenQ 536870912) 0 3 hp757632 hp716712 hp757633 rfl rfl rfl

noncomputable def hp757637 := hp757635 hp757633 99894528 rfl rfl rfl rfl rfl rfl rfl rfl (hp757636 rfl)

noncomputable def hp757638 := @BSN.binarySplit_of_base3 (BSN.cosOddP 742834745) (BSN.cosOddQ 536870912) 0 3 hp757634 hp716714 hp757633 rfl rfl rfl

noncomputable def hp757639 := nat_lit 10294759643886485225091698396672504662533556342553407766645381210412342512989133608393299372148917239821213330321

noncomputable def hp757640 := nat_lit 416770839567085559715662905350652521539171474137376065877477804617901822469134602345937027127775562263441

noncomputable def hp757641 := nat_lit 62432601378687214482414188807532525280538838847304275479675946603191855791146066817674627685556709334262045961105

noncomputable def hp757642 := BSN.cos_dyadic_bound_f 522786997 536870912 4 3 536870912 268435456 hp757639 hp716712 hp757640 hp757641 hp716714

noncomputable def hp757643 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 522786997) (BSN.cosEvenQ 536870912) 0 3 hp757639 hp716712 hp757640 rfl rfl rfl

noncomputable def hp757644 := hp757642 hp757640 301822631 rfl rfl rfl rfl rfl rfl rfl rfl (hp757643 rfl)

noncomputable def hp757645 := @BSN.binarySplit_of_base3 (BSN.cosOddP 522786997) (BSN.cosOddQ 536870912) 0 3 hp757641 hp716714 hp757640 rfl rfl rfl

noncomputable def hp757646 := hp757631 hd4911 hd4913 hd4915 hd4917 hd4918 (hp757637 (hp757638 rfl) rfl rfl rfl rfl) (hp757644 (hp757645 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757647 := hp757568 (BSN.cos_quad_nat3 183 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 454953759 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl rfl (hp757646 rfl rfl rfl rfl rfl) hp757630

noncomputable def hp757648 := nat_lit 60900792131361933211040697219876814869052707509444149701486489251818053884596652532639673780104687249679974400000

noncomputable def hp757649 := nat_lit 4906971562903312494833602701218189054829612613356069796949447110205410242459382804687813083136000000000000

noncomputable def hp757650 := nat_lit 304376700527120200288624585480541610664970326804639202604527017550349745002801143390460805015588247670095872000000

noncomputable def hp757651 := BSN.sin_dyadic_bound_f 642048440 536870912 4 3 536870912 268435456 hp757648 hp642702 hp757649 hp757650 hp642705

noncomputable def hp757652 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 642048440) (BSN.sinEvenQ 536870912) 0 3 hp757648 hp642702 hp757649 rfl rfl rfl

noncomputable def hp757653 := hp757651 hp757649 499584513 rfl rfl rfl rfl rfl rfl rfl rfl (hp757652 rfl)

noncomputable def hp757654 := @BSN.binarySplit_of_base3 (BSN.sinOddP 642048440) (BSN.sinOddQ 536870912) 0 3 hp757650 hp642705 hp757649 rfl rfl rfl

noncomputable def hp757655 := nat_lit 21820798760313641624426880007261584442357847547857614341150581454487890625

noncomputable def hp757656 := nat_lit 7539083809133986516763512953429420728129228996096756674804840087890625

noncomputable def hp757657 := nat_lit 57137504903225701609614687664712883048805962921252452335063743592087890625

noncomputable def hp757658 := BSN.sin_dyadic_bound_f 542831225 536870912 3 2 536870912 268435456 hp757655 hp708845 hp757656 hp757657 hp708848

noncomputable def hp757659 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 542831225) (BSN.sinEvenQ 536870912) 0 2 hp757655 hp708845 hp757656 rfl rfl rfl

noncomputable def hp757660 := hp757658 hp757656 454953759 rfl rfl rfl rfl rfl rfl rfl rfl (hp757659 rfl)

noncomputable def hp757661 := @BSN.binarySplit_of_base2 (BSN.sinOddP 542831225) (BSN.sinOddQ 536870912) 0 2 hp757657 hp708848 hp757656 rfl rfl rfl

noncomputable def hp757662 := hp757647 hd4920 hd4922 hd4924 hd4926 hd4918 (hp757653 (hp757654 rfl) rfl rfl rfl rfl) (hp757660 (hp757661 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757663 := hp757563 (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 366610845 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl rfl (hp757662 rfl rfl rfl rfl rfl) hp757630

noncomputable def hp757664 := nat_lit 7968548172266178033294000447274797643956656289484697043249693081914166945

noncomputable def hp757665 := nat_lit 1005833722719300413164955287444330810399571423287385339269585453043361

noncomputable def hp757666 := nat_lit 20868378625146063600815353148587655389050595737774598394152283504755986081

noncomputable def hp757667 := BSN.sin_dyadic_bound_f 422003229 536870912 3 2 536870912 268435456 hp757664 hp708845 hp757665 hp757666 hp708848

noncomputable def hp757668 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 422003229) (BSN.sinEvenQ 536870912) 0 2 hp757664 hp708845 hp757665 rfl rfl rfl

noncomputable def hp757669 := hp757667 hp757665 379869501 rfl rfl rfl rfl rfl rfl rfl rfl (hp757668 rfl)

noncomputable def hp757670 := @BSN.binarySplit_of_base2 (BSN.sinOddP 422003229) (BSN.sinOddQ 536870912) 0 2 hp757666 hp708848 hp757665 rfl rfl rfl

noncomputable def hp757671 := nat_lit 5221198670360771262229114839323590721329384623907604300996436810816050241

noncomputable def hp757672 := nat_lit 1398717989870002787543524637865756837647814214001514504738000225719361

noncomputable def hp757673 := nat_lit 15660798575102573781112257468695040650312858243294809873979834431996712001

noncomputable def hp757674 := BSN.cos_dyadic_bound_f 439760553 536870912 3 2 536870912 268435456 hp757671 hp708868 hp757672 hp757673 hp708870

noncomputable def hp757675 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 439760553) (BSN.cosEvenQ 536870912) 0 2 hp757671 hp708868 hp757672 rfl rfl rfl

noncomputable def hp757676 := hp757674 hp757672 366610845 rfl rfl rfl rfl rfl rfl rfl rfl (hp757675 rfl)

noncomputable def hp757677 := @BSN.binarySplit_of_base2 (BSN.cosOddP 439760553) (BSN.cosOddQ 536870912) 0 2 hp757673 hp708870 hp757672 rfl rfl rfl

noncomputable def hp757678 := hp757663 hd4928 hd4930 hd4932 hd4934 hd4918 (hp757669 (hp757670 rfl) rfl rfl rfl rfl) (hp757676 (hp757677 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757679 := hp757559 (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 197239487 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl rfl (hp757678 rfl rfl rfl rfl rfl) hp757630

noncomputable def hp757680 := nat_lit 2091534515400339179256886501554325438747220864491905822753983865330602785

noncomputable def hp757681 := nat_lit 69307258625842827101607326106788871105242357817953549973290634711841

noncomputable def hp757682 := nat_lit 5477716280963113152524157282685727062356169966994714753846191462457283361

noncomputable def hp757683 := BSN.sin_dyadic_bound_f 302062867 536870912 3 2 536870912 268435456 hp757680 hp708845 hp757681 hp757682 hp708848

noncomputable def hp757684 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 302062867) (BSN.sinEvenQ 536870912) 0 2 hp757680 hp708845 hp757681 rfl rfl rfl

noncomputable def hp757685 := hp757683 hp757681 286376424 rfl rfl rfl rfl rfl rfl rfl rfl (hp757684 rfl)

noncomputable def hp757686 := @BSN.binarySplit_of_base2 (BSN.sinOddP 302062867) (BSN.sinOddQ 536870912) 0 2 hp757682 hp708848 hp757681 rfl rfl rfl

noncomputable def hp757687 := nat_lit 23333387700223893525872780390258159971835235460324663970868350753894240021986107654193482563584000000000000000000

noncomputable def hp757688 := nat_lit 4842844889420740409614951366199240587608524007190495625361855712890625000000000000000000000000000000000000

noncomputable def hp757689 := nat_lit 141441602344327803382685006736759183679562815878498734657309719452434800797783472302107127552409600000000000000000

noncomputable def hp757690 := BSN.cos_dyadic_bound_f 641345000 536870912 4 3 536870912 268435456 hp757687 hp716712 hp757688 hp757689 hp716714

noncomputable def hp757691 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 641345000) (BSN.cosEvenQ 536870912) 0 3 hp757687 hp716712 hp757688 rfl rfl rfl

noncomputable def hp757692 := hp757690 hp757688 197239487 rfl rfl rfl rfl rfl rfl rfl rfl (hp757691 rfl)

noncomputable def hp757693 := @BSN.binarySplit_of_base3 (BSN.cosOddP 641345000) (BSN.cosOddQ 536870912) 0 3 hp757689 hp716714 hp757688 rfl rfl rfl

noncomputable def hp757694 := hp757679 hd4936 hd4938 hd4940 hd4942 hd4918 (hp757685 (hp757686 rfl) rfl rfl rfl rfl) (hp757692 (hp757693 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757695 := hp757555 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 180997364 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl rfl (hp757694 rfl rfl rfl rfl rfl) hp757630

noncomputable def hp757696 := nat_lit 6514731481897529614838645992502714285923130253687010667372019184330359040

noncomputable def hp757697 := nat_lit 672327427331591086033421921214720034774486887559924699969944562974976

noncomputable def hp757698 := nat_lit 17061303446277850224723828249634665964028087209457549965031527477287076096

noncomputable def hp757699 := BSN.sin_dyadic_bound_f 401280082 536870912 3 2 536870912 268435456 hp757696 hp708845 hp757697 hp757698 hp708848

noncomputable def hp757700 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 401280082) (BSN.sinEvenQ 536870912) 0 2 hp757696 hp708845 hp757697 rfl rfl rfl

noncomputable def hp757701 := hp757699 hp757697 364946143 rfl rfl rfl rfl rfl rfl rfl rfl (hp757700 rfl)

noncomputable def hp757702 := @BSN.binarySplit_of_base2 (BSN.sinOddP 401280082) (BSN.sinOddQ 536870912) 0 2 hp757698 hp708848 hp757697 rfl rfl rfl

noncomputable def hp757703 := nat_lit 25967039636165046437921636423500292292968557605925454444098134094412427679485956172084460053414323051619904000000

noncomputable def hp757704 := nat_lit 6672009089531364450710613708349400628933911966796729482251255763425241796088317936706312676881000000000000

noncomputable def hp757705 := nat_lit 157391871656395365257782682863022159853686574566742820965997596559000688335359101621382261006349704354758617600000

noncomputable def hp757706 := BSN.cos_dyadic_bound_f 658700590 536870912 4 3 536870912 268435456 hp757703 hp716712 hp757704 hp757705 hp716714

noncomputable def hp757707 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 658700590) (BSN.cosEvenQ 536870912) 0 3 hp757703 hp716712 hp757704 rfl rfl rfl

noncomputable def hp757708 := hp757706 hp757704 180997364 rfl rfl rfl rfl rfl rfl rfl rfl (hp757707 rfl)

noncomputable def hp757709 := @BSN.binarySplit_of_base3 (BSN.cosOddP 658700590) (BSN.cosOddQ 536870912) 0 3 hp757705 hp716714 hp757704 rfl rfl rfl

noncomputable def hp757710 := hp757695 hd4944 hd4946 hd4961 hd4963 hd4918 (hp757701 (hp757702 rfl) rfl rfl rfl rfl) (hp757708 (hp757709 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757711 := @hp757550 102587 134217728 (hp757710 rfl rfl rfl rfl rfl) (hp757710 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp757712 := @hp757548 Bool.true 577221523 268435456 102587 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 845556 1000)) (Enclosure.sfrac Bool.false 845556 1000) 11) hp757711

noncomputable def hp757713 := @Enclosure.Real.IsNear.mulLit_tf hp757539 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1))) 19703313 67108864 1

noncomputable def hp757714 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp757538 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757715 := @hp757714 1 1 0 1 19703313 67108864 1 67108864 19703313 67108864 1

noncomputable def hp757716 := @Enclosure.Real.IsNear.of_eq (hp757538 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757717 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 845556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757718 := @hp757716 (@Inv.inv Real Real.instInv (Real.sqrt hp757540)) Bool.false 19703313 67108864 1 67108864 (hp757717 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 845556 1000) 845556 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000))))

noncomputable def hp757719 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp757540)) Bool.false 19703313 67108864 1 67108864 19703313 67108864

noncomputable def hp757720 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp757540) Bool.false 228570674 67108864 6 67108864 114285337 33554432 3 33554432

noncomputable def hp757721 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 845556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757722 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 845556 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757723 := @hp757722 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 845556 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2257783972023

noncomputable def hp757724 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 845556 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 845556 1000 0

noncomputable def hp757725 := @hp757724 1 10680707 67108864 1 67108864 2257783972023 16777216000 211389 16777216000 (Enclosure.Real.IsNear.const Bool.false 845556 1000) hd4949

noncomputable def hp757726 := @hp757723 16777216000 211389 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 845556 1000) 845556 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000))) (hp757725 rfl)

noncomputable def hp757727 := @hp757721 2257783972023 16777216000 211389 16777216000 389252236 389252273 33554432 hp757726 rfl rfl rfl

noncomputable def hp757728 := @Enclosure.Real.IsNear.recentre' hp757540 Bool.false 778504509 67108864 37 67108864 778504509 67108864 37 67108864 (hp757727 rfl rfl rfl)

noncomputable def hp757729 := @Enclosure.Real.IsNear.sqrt_image hp757540 778504509 67108864 37 67108864 114285334 114285340 33554432 (hp757728 rfl) rfl rfl

noncomputable def hp757730 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp757540) 114285337 33554432 3 33554432 9851656 9851657 33554432 (hp757720 (hp757729 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp757731 := @hp757715 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp757718 (@hp757719 1 67108864 (hp757730 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp757732 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757733 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp757734 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1))) (hp757732 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757733 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp757735 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 845556 1000) 845556 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl

noncomputable def hp757736 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757737 := @hp757736 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757733 (Enclosure.sfrac Bool.false 1 16)))) 20796911

noncomputable def hp757738 := @hp757737 16777216 185 33554432 10844005 33554432 353354929 45675970560000 225521806868555 562949953421312 5809435574822251 510877082729840640000

noncomputable def hp757739 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757740 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757741 := @hp757739 (@Neg.neg Real Real.instNeg hp757740) Bool.true 20796911 16777216 185 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757742 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757743 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp757744 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp757745 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 253256381) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp757746 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1))) Bool.false 35642667055274886402775

noncomputable def hp757747 := nat_lit 998484790480864218390668739

noncomputable def hp757748 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp757749 := @Enclosure.Real.IsNear.subLit_ff_p hp757540 (Enclosure.sfrac Bool.false 11 1) 778504509 67108864 37 67108864 11 1 0

noncomputable def hp757750 := @hp757748 500000000000000 40307005 67108864 37 67108864 35642667055274886402775 9444732965739290427392 hp757747 hp738031 hd4948 (@hp757749 1 40307005 40307005 67108864 37 67108864 (hp757728 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757751 := @hp757745 253256381 67108864 117 33554432 Bool.true 54137843 67108864 1 10890000 (@hp757746 9444732965739290427392 hp757747 hp738031 253256381 67108864 117 33554432 (hp757750 rfl) rfl) (Enclosure.sfrac_false_div 253256381 67108864)

noncomputable def hp757752 := nat_lit 6114471190134904158420992

noncomputable def hp757753 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 253256381) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp757752) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp757754 := BSN.sin_reduce_arg_pos_rat_q2 253256381 67108864 226375608064910080 72057594037927936 0 hp757752 hp617687 rfl rfl rfl rfl

noncomputable def hp757755 := nat_lit 34174828848516539524163123071221898900722807888309281224643283398164274681483026371643466881

noncomputable def hp757756 := nat_lit 3249621803926268947911905333657753491685980319331570500524866220274309279751048380572801

noncomputable def hp757757 := nat_lit 102517987301941766034593545402998381195185051704289180532928800462052275425889577018169255041

noncomputable def hp757758 := BSN.cos_dyadic_bound_f 86891861743 137438953472 3 2 67108864 21801270 hp757755 hp746621 hp757756 hp757757 hp746624

noncomputable def hp757759 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 86891861743) (BSN.cosEvenQ 137438953472) 0 2 hp757755 hp746621 hp757756 rfl rfl rfl

noncomputable def hp757760 := hp757758 hp757756 54137843 rfl rfl rfl rfl rfl rfl rfl rfl (hp757759 rfl)

noncomputable def hp757761 := @BSN.binarySplit_of_base2 (BSN.cosOddP 86891861743) (BSN.cosOddQ 137438953472) 0 2 hp757757 hp746624 hp757756 rfl rfl rfl

noncomputable def hp757762 := @BSN.cos_arg_round Bool.false 54137843 67108864 hp757752 hp617687 86891861743 137438953472 21801270 21780000 (hp757760 (hp757761 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757763 := hp757753 54137843 67108864 0 1000000000000000 21780000 10890000 hp757754 BSN.pi_near_15 hp757762 rfl rfl

noncomputable def hp757764 := @hp757743 54137843 67108864 81730277 22837985280000 (@hp757744 54137843 67108864 1307684432 365407764480000 54137843 67108864 81730277 22837985280000 (hp757751 (hp757763 rfl rfl) rfl rfl) rfl)

noncomputable def hp757765 := @hp757742 54137843 67108864 81730277 22837985280000 41593637 41594007 33554432 hp757764 rfl rfl rfl

noncomputable def hp757766 := @Enclosure.Real.IsNear.recentre' hp757740 Bool.false 83187644 67108864 370 67108864 20796911 16777216 185 33554432 (hp757765 rfl rfl rfl)

noncomputable def hp757767 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757733 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp757768 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757733 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 15937353)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true

noncomputable def hp757769 := nat_lit 1204192350111653787136063140805

noncomputable def hp757770 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757733 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp757769

noncomputable def hp757771 := nat_lit 147499079799609159377350630921349661

noncomputable def hp757772 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757733 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp757773 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp757774 := @hp757773 (Enclosure.sfrac Bool.false 1 16) 1080302664722295 4503599627370496 5465747707 4503599627370496 1 16 0

noncomputable def hp757775 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)) 1624654652070025

noncomputable def hp757776 := @hp757775 4503599627370496 2982719739 4503599627370496 40307005 67108864 37 67108864 72497884605686092922880 1080302664722295 4503599627370496 5465747707

noncomputable def hp757777 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)) 40307005 67108864 37

noncomputable def hp757778 := @hp757777 67108864 40307005 67108864 37 67108864 1624654652070025 4503599627370496 2982719739 4503599627370496 (@hp757749 1 40307005 40307005 67108864 37 67108864 (hp757728 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757779 := hp757778 (@hp757749 1 40307005 40307005 67108864 37 67108864 (hp757728 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757780 := @hp757776 4503599627370496 (hp757779 rfl) (@hp757749 1 40307005 40307005 67108864 37 67108864 (hp757728 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757781 := @hp757772 500000000000000 1361777641432951 4503599627370496 5465747707 4503599627370496 hp757769 hp627574 hp757771 hp738055 hd4948 (@hp757774 1 21788442262927216 1361777641432951 4503599627370496 5465747707 4503599627370496 (hp757780 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp757782 := @hp757768 15937353 8388608 513 67108864 Bool.true 10844005 33554432 1 10890000 (@hp757770 hp627574 hp757771 hp738055 15937353 8388608 513 67108864 (hp757781 rfl) rfl) (Enclosure.sfrac_true_div 15937353 8388608)

noncomputable def hp757783 := nat_lit 31817674011959325660154971036122983162296484980904080056357046692575086228707891873227159521

noncomputable def hp757784 := nat_lit 268530922853493924765314120108168414446021714158862243292157201212890629292692324431841

noncomputable def hp757785 := nat_lit 192035567088342795054060285926689253895343345034967296278980439198766214878368493885182130145

noncomputable def hp757786 := BSN.cos_dyadic_bound_t 15937353 8388608 4 3 33554432 10890000 hp757783 hp633059 hp757784 hp757785 hp633062

noncomputable def hp757787 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 15937353) (BSN.cosEvenQ 8388608) 0 3 hp757783 hp633059 hp757784 rfl rfl rfl

noncomputable def hp757788 := hp757786 hp757784 10844005 rfl rfl rfl rfl rfl rfl rfl rfl (hp757787 rfl)

noncomputable def hp757789 := @BSN.binarySplit_of_base3 (BSN.cosOddP 15937353) (BSN.cosOddQ 8388608) 0 3 hp757785 hp633062 hp757784 rfl rfl rfl

noncomputable def hp757790 := hp757782 (BSN.cos_neg_of_bound 15937353 8388608 Bool.true 10844005 33554432 1 10890000 (hp757788 (hp757789 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp757791 := hp757738 (hp757741 (@Enclosure.Real.IsNear.neg hp757740 Bool.false 20796911 16777216 185 33554432 (hp757766 rfl))) (@hp757767 10844005 33554432 5653678864 730815528960000 10844005 33554432 353354929 45675970560000 (hp757790 rfl) rfl)

noncomputable def hp757792 := @hp757713 67108864 225521806868555 562949953421312 5809435574822251 510877082729840640000 4443526749056689022715 37778931862957161709568 57334897166613259651157 hp741590 (hp757731 rfl) (@hp757734 Bool.false 225521806868555 562949953421312 5809435574822251 510877082729840640000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757540 (Enclosure.sfrac Bool.false 11 1)) (hp757735 rfl (hp757543 rfl rfl))) (hp757791 rfl))

noncomputable def hp757793 := @hp757537 hp757535 hp741590 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 845556 1000))) (@hp757542 hp757535 hp741590 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 845556 1000) 11 (hp757543 rfl rfl)) (@hp757546 hp757535 hp741590 hp757712 (hp757792 rfl) rfl rfl))

theorem hd5040 : hp757536 hp741590 := hp757793

noncomputable def hp757794 := nat_lit 7909482486575171666324447

noncomputable def hp757795 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 846837 1000)) Bool.false 198734100447729969238121 75557863725914323419136 hp757794

noncomputable def hp757796 := nat_lit 10285314199690087275429888000

noncomputable def hp757797 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 846837 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 846837 1000)) Bool.false 198734100447729969238121 75557863725914323419136

noncomputable def hp757798 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 846837 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757799 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp757798 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757800 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 846837 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757801 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp757799 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp757802 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 846837 1000)) hp757801 Bool.false 198734100447729969238121 75557863725914323419136

noncomputable def hp757803 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 846837 1000) 846837 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl

noncomputable def hp757804 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp757799 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp757805 := nat_lit 53347278876436198457300983218176

noncomputable def hp757806 := @hp757804 674223191 268435456 51371 67108864 8957143463220797214825 75557863725914323419136 36202501500778611092447 hp757796 hp757805 198734100447729969238121 75557863725914323419136

noncomputable def hp757807 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) 11)

noncomputable def hp757808 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) 11) hp757807

noncomputable def hp757809 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) 11)

noncomputable def hp757810 := @hp757809 674223191 536870912 205484 536870912 674223191 536870912 205484 536870912 723941638887440384 674223191 268435456

noncomputable def hp757811 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp757812 := hp757811 BSN.quadSignPos 9 10 11 846837 1000 189 240 536870912 268435456 9007199254740992

noncomputable def hp757813 := hp757812 Bool.false 887166823086 3858 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp757814 := hp757813 Bool.false 699049666 176402 Bool.true 298909635 Bool.true 621877970 28296951008113761 1 Bool.false 283704333

noncomputable def hp757815 := hp757814 Bool.true Bool.false 215211533 Bool.false Bool.false 674223191 205484 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 283704333 536870912) BSN.abs_quadSignPos

noncomputable def hp757816 := hp757811 BSN.quadSignPos 7 8 9 846837 1000 69 132 536870912 268435456 9007199254740992

noncomputable def hp757817 := hp757816 Bool.false 887166823086 3858 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp757818 := hp757817 Bool.false 599834529 144067 Bool.true 46229542 Bool.true 466514778 28296951008113761 1 Bool.false 46172432

noncomputable def hp757819 := hp757818 Bool.true Bool.false 346618678 Bool.false Bool.false 699049666 176402 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 46172432 536870912) BSN.abs_quadSignPos

noncomputable def hp757820 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp757821 := hp757820 BSN.quadSignNeg 5 6 7 846837 1000 86 2 536870912 268435456 9007199254740992

noncomputable def hp757822 := hp757821 Bool.false 887166823086 3858 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp757823 := hp757822 Bool.false 839698142 107058 Bool.false 32369769 Bool.false 787427660 28296951008113761 1 Bool.false 535895365

noncomputable def hp757824 := hp757823 Bool.true Bool.false 55786315 Bool.true Bool.false 599834529 144067 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535895365 536870912) BSN.abs_quadSignNeg

noncomputable def hp757825 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp757826 := hp757825 BSN.quadSignPos 3 4 5 846837 1000 304 184 536870912 268435456 9007199254740992

noncomputable def hp757827 := hp757826 Bool.false 887166823086 3858 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp757828 := hp757827 Bool.false 483821523 63277 Bool.false 531266172 Bool.false 278586078 28296951008113761 1 Bool.false 294772925

noncomputable def hp757829 := hp757828 Bool.false Bool.false 466198163 Bool.false Bool.false 839698142 107058 BSN.abs_quadSignPos (BSN.cos_quad_nat0 304 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 294772925 536870912) BSN.abs_quadSignPos

noncomputable def hp757830 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp757831 := hp757830 BSN.quadSignPos 1 2 3 846837 1000 678 459 536870912 268435456 9007199254740992

noncomputable def hp757832 := hp757831 Bool.false 887166823086 3858 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp757833 := hp757832 Bool.false 536870752 3914 Bool.false 265436867 Bool.false 609852780 28296951008113761 1 Bool.false 472578794

noncomputable def hp757834 := hp757833 Bool.true Bool.false 486904493 Bool.false Bool.false 483821523 63277 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 678 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 472578794 536870912) BSN.abs_quadSignPos

noncomputable def hp757835 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) 1) Bool.false

noncomputable def hp757836 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)))

noncomputable def hp757837 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000))) Bool.false 67108844 67108864

noncomputable def hp757838 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 110895852885) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 110895852885 67108864

noncomputable def hp757839 := nat_lit 10978792776316452066293768789050518629433444970073610274523

noncomputable def hp757840 := nat_lit 6643840072801197564265290270681789863624589344505856000

noncomputable def hp757841 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) Bool.false hp757839 hp757840 128198153157038082451

noncomputable def hp757842 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 846837 4000) (Real.log (Enclosure.sfrac Bool.false 2868532618276 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1693674))))))

noncomputable def hp757843 := nat_lit 209045462702140755331555736619360000

noncomputable def hp757844 := nat_lit 1062164767788167873135087625444869785920

noncomputable def hp757845 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp757842 (Enclosure.sfrac Bool.false 846837 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 846837 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp757843 hp757844)) Bool.false

noncomputable def hp757846 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 846837 1000) 846837 1000 2868532618276 16000000 1693674

noncomputable def hp757847 := hp757846 4000 2000 hp757843 hp757844 (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl rfl rfl rfl

noncomputable def hp757848 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp757842 (Enclosure.sfrac Bool.false 846837 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 846837 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp757843 hp757844) 29768382383330524308947 18014398509481984000

noncomputable def hp757849 := nat_lit 31618923195791381950926054112465493652768321513811997590626240

noncomputable def hp757850 := @hp757848 128198153157038082451 hp738659 hp757843 hp757844 0 1 hp757849 hp757839 hp757840 128198153157038082451 hp738659

noncomputable def hp757851 := @Enclosure.Real.IsNear.subLit_ff_p (hp757842 (Enclosure.sfrac Bool.false 846837 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 846837 2000) (Real.log Real.pi)) 38499957913534684112339 18014398509481984000 10685478178037881 4356000000000000000000

noncomputable def hp757852 := nat_lit 1997722324862924022897818206208000

noncomputable def hp757853 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 846837 4000) (Real.log (Enclosure.sfrac Bool.false 2868532618276 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1693674))))))

noncomputable def hp757854 := @hp757853 (Enclosure.sfrac Bool.false 846837 2000) 46127587508821781554643 18014398509481984000 10685478178037881 4356000000000000000000 846837 2000 0

noncomputable def hp757855 := nat_lit 76999915827069368224678000

noncomputable def hp757856 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 846837 4000) (Real.log (Enclosure.sfrac Bool.false 2868532618276 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1693674))))) 46134659087586400586643

noncomputable def hp757857 := nat_lit 103870092958114860640317064848515006464

noncomputable def hp757858 := @hp757856 18014398509481984000 1176164241943709 484000000000000000000 883947345577379 2251799813685248 200000001089 8712000000000000000 hp757857 46127587508821781554643 18014398509481984000 10685478178037881

noncomputable def hp757859 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 846837 4000) (Real.log (Enclosure.sfrac Bool.false 2868532618276 16000000)) 846837 4000 0 1 54478794723880039 4503599627370496

noncomputable def hp757860 := nat_lit 116992320832281058866102272

noncomputable def hp757861 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2868532618276) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp757860 hp617687

noncomputable def hp757862 := BSN.log_rat_reduce_isNear 2868532618276 16000000 17 5737065236552 4194304000000 84079456 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp757863 := nat_lit 349353318659257241663784707265106853111217442752645535152906597766084960216064225243948455394924674744320

noncomputable def hp757864 := nat_lit 2851507850554711641640917345512700571985379610382807646805424517097691386009329338282733617144457068544

noncomputable def hp757865 := nat_lit 13162521078540649665688277350194262642362927519660367960736993075752787785960738863110581603860480

noncomputable def hp757866 := BSN.log_dyadic_bound 771380618276 4965684618276 5 4 hp757863 268435456 87120000 hp757864 hp757865 84079456 5737065236552

noncomputable def hp757867 := hp757866 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp757868 := @BSN.binarySplit_of_base4 (BSN.artanhP 771380618276) (BSN.artanhQ 4965684618276) 0 4 hp757864 hp757863 hp757865 rfl rfl rfl

noncomputable def hp757869 := hp757862 rfl rfl rfl rfl (hp757867 (hp757868 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp757870 := @hp757859 12500018513 1089000000000000000 46134659087586400586643 18014398509481984000 1176164241943709 484000000000000000000 (Enclosure.Real.IsNear.const Bool.false 846837 4000) (BSN.isNear_log_sfrac 2868532618276 16000000 54478794723880039 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp757861 1000001481040000 87120000000000000000000 54478794723880039 4503599627370496 12500018513 1089000000000000000 (hp757869 rfl rfl rfl) rfl)) rfl

noncomputable def hp757871 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1693674)))) 1 4

noncomputable def hp757872 := @hp757871 0 1 883947345577379 562949953421312 200000001089 2178000000000000000 883947345577379 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp757873 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1693674))) 884279719003555 562949953421312 1

noncomputable def hp757874 := @hp757873 2000000000000000 19811 33554432 1 10890000 29660351098756664393728 883947345577379 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp757875 := BSN.arctan_dyadic_bound_f 1000 1693674 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp757876 := hp757875 1 19811 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1693674) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1693674) 0 0 rfl)

noncomputable def hp757877 := hp757872 (hp757874 (hp757876 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp757878 := @hp757851 32527653612957 67108864000 2540511 536870912000 hp757852 29768382383330524308947 18014398509481984000 128198153157038082451 hp738659 (@hp757854 1 hp757855 38499957913534684112339 18014398509481984000 10685478178037881 4356000000000000000000 (@hp757858 4356000000000000000000 hp757870 hp757877 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 846837 2000) rfl rfl)

noncomputable def hp757879 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 846837 2000) (Real.log Real.pi) 846837 2000 0 1 38410761 33554432

noncomputable def hp757880 := hp757878 (@hp757879 3 268435456 32527653612957 67108864000 2540511 536870912000 (Enclosure.Real.IsNear.const Bool.false 846837 2000) hd4909 rfl) rfl

noncomputable def hp757881 := @hp757841 hp738659 110895852885 67108864 483 67108864 (@hp757845 hp757839 hp757840 128198153157038082451 hp738659 (hp757847 rfl rfl rfl rfl rfl) (hp757850 (hp757880 rfl) (Enclosure.Real.IsNear.const Bool.true hp757843 hp757844) rfl rfl)) rfl

noncomputable def hp757882 := nat_lit 15184496187052230547865600

noncomputable def hp757883 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 110895852885) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp757882) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp757884 := BSN.sin_reduce_arg_pos_rat_q3 110895852885 67108864 226375608064910080 72057594037927936 262 hp757882 hp617687 rfl rfl rfl rfl

noncomputable def hp757885 := nat_lit 14352654342808877732001327664814730762034897513844076853707518236551963444866034771374214620014760604804908273175351020688997215196524028411281

noncomputable def hp757886 := nat_lit 10191709486588437602087366225225752009841920085803117435344078248241493671037212221032753867535184786279780488674818618050692675458350481

noncomputable def hp757887 := nat_lit 71674268327317619090287758226998596341478435820636426026038409879550618899316059627797481360156516014682226511951513833406816063134115180887441

noncomputable def hp757888 := BSN.sin_dyadic_bound_f 215784669237 137438953472 4 3 67108864 21801270 hp757885 hp737934 hp757886 hp757887 hp737937

noncomputable def hp757889 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215784669237) (BSN.sinEvenQ 137438953472) 0 3 hp757885 hp737934 hp757886 rfl rfl rfl

noncomputable def hp757890 := hp757888 hp757886 67108844 rfl rfl rfl rfl rfl rfl rfl rfl (hp757889 rfl)

noncomputable def hp757891 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215784669237) (BSN.sinOddQ 137438953472) 0 3 hp757887 hp737937 hp757886 rfl rfl rfl

noncomputable def hp757892 := @BSN.sin_arg_round Bool.false 67108844 67108864 hp757882 hp617687 215784669237 137438953472 21801270 21780000 (hp757890 (hp757891 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757893 := hp757883 67108844 67108864 262 1000000000000000 21780000 10890000 hp757884 BSN.pi_near_15 hp757892 rfl rfl

noncomputable def hp757894 := @hp757838 483 67108864 Bool.false 67108844 67108864 1 10890000 hp757881 (Enclosure.sfrac_false_div 110895852885 67108864) (hp757893 rfl rfl) rfl

noncomputable def hp757895 := @hp757835 16777211 16777216 332936179 45675970560000 536870752 536870912 3914 536870912 (@hp757836 Bool.false 16777211 16777216 332936179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000)) (@hp757837 5326978864 730815528960000 16777211 16777216 332936179 45675970560000 (hp757894 rfl) rfl))

noncomputable def hp757896 := @hp757841 hp738659 887166823086 536870912 3858 536870912 (@hp757845 hp757839 hp757840 128198153157038082451 hp738659 (hp757847 rfl rfl rfl rfl rfl) (hp757850 (hp757880 rfl) (Enclosure.Real.IsNear.const Bool.true hp757843 hp757844) rfl rfl)) rfl

noncomputable def hp757897 := hp757834 (BSN.cos_quad_nat3 459 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 486904493 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl rfl (hp757895 rfl) hp757896

noncomputable def hp757898 := nat_lit 692865913207573244892607333660425525459849966684408021839958553135573921

noncomputable def hp757899 := nat_lit 24642793695439801709224356441839818895148013539455275372415205927841

noncomputable def hp757900 := nat_lit 2078548454035328855074403552268392896741759604026145154969130828994866081

noncomputable def hp757901 := BSN.cos_dyadic_bound_f 265436867 536870912 3 2 536870912 268435456 hp757898 hp708868 hp757899 hp757900 hp708870

noncomputable def hp757902 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 265436867) (BSN.cosEvenQ 536870912) 0 2 hp757898 hp708868 hp757899 rfl rfl rfl

noncomputable def hp757903 := hp757901 hp757899 472578794 rfl rfl rfl rfl rfl rfl rfl rfl (hp757902 rfl)

noncomputable def hp757904 := @BSN.binarySplit_of_base2 (BSN.cosOddP 265436867) (BSN.cosOddQ 536870912) 0 2 hp757900 hp708870 hp757899 rfl rfl rfl

noncomputable def hp757905 := nat_lit 34769654364315261278778009353732237645940639597245466111787114026147840000

noncomputable def hp757906 := nat_lit 19133748582496276234422822181817112367919209910634201598558233600000000

noncomputable def hp757907 := nat_lit 91032402027882595092420006595290061366963139271978051109235251975987200000

noncomputable def hp757908 := BSN.sin_dyadic_bound_f 609852780 536870912 3 2 536870912 268435456 hp757905 hp708845 hp757906 hp757907 hp708848

noncomputable def hp757909 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 609852780) (BSN.sinEvenQ 536870912) 0 2 hp757905 hp708845 hp757906 rfl rfl rfl

noncomputable def hp757910 := hp757908 hp757906 486904493 rfl rfl rfl rfl rfl rfl rfl rfl (hp757909 rfl)

noncomputable def hp757911 := @BSN.binarySplit_of_base2 (BSN.sinOddP 609852780) (BSN.sinOddQ 536870912) 0 2 hp757907 hp708848 hp757906 rfl rfl rfl

noncomputable def hp757912 := hp757897 hd4911 hd4913 hd4915 hd4917 hd4918 (hp757903 (hp757904 rfl) rfl rfl rfl rfl) (hp757910 (hp757911 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757913 := hp757829 (BSN.cos_quad_nat0 184 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 466198163 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl rfl (hp757912 rfl rfl rfl rfl rfl) hp757896

noncomputable def hp757914 := nat_lit 10979465561095160333093710232735625953785615256133611345528372992989906788524906943450762052207043636851162218496

noncomputable def hp757915 := nat_lit 505528867888469227129081390188661578769880191962546143417661198661856457389807111824897233224150198255616

noncomputable def hp757916 := nat_lit 66583424188555971585589279231138374947698795736908478321021674125933655279454679379895420384049376105722890158080

noncomputable def hp757917 := BSN.cos_dyadic_bound_f 531266172 536870912 4 3 536870912 268435456 hp757914 hp716712 hp757915 hp757916 hp716714

noncomputable def hp757918 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 531266172) (BSN.cosEvenQ 536870912) 0 3 hp757914 hp716712 hp757915 rfl rfl rfl

noncomputable def hp757919 := hp757917 hp757915 294772925 rfl rfl rfl rfl rfl rfl rfl rfl (hp757918 rfl)

noncomputable def hp757920 := @BSN.binarySplit_of_base3 (BSN.cosOddP 531266172) (BSN.cosOddQ 536870912) 0 3 hp757916 hp716714 hp757915 rfl rfl rfl

noncomputable def hp757921 := nat_lit 840707957731778762231021225881649816265100115132872424171250672957686016

noncomputable def hp757922 := nat_lit 36280667970183348727867693805803553567257254402713263607092438139136

noncomputable def hp757923 := nat_lit 2522051311859395919995607942257337841688165830889811845986537833996779776

noncomputable def hp757924 := BSN.cos_dyadic_bound_f 278586078 536870912 3 2 536870912 268435456 hp757921 hp708868 hp757922 hp757923 hp708870

noncomputable def hp757925 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 278586078) (BSN.cosEvenQ 536870912) 0 2 hp757921 hp708868 hp757922 rfl rfl rfl

noncomputable def hp757926 := hp757924 hp757922 466198163 rfl rfl rfl rfl rfl rfl rfl rfl (hp757925 rfl)

noncomputable def hp757927 := @BSN.binarySplit_of_base2 (BSN.cosOddP 278586078) (BSN.cosOddQ 536870912) 0 2 hp757923 hp708870 hp757922 rfl rfl rfl

noncomputable def hp757928 := hp757913 hd4920 hd4922 hd4924 hd4926 hd4918 (hp757919 (hp757920 rfl) rfl rfl rfl rfl) (hp757926 (hp757927 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757929 := hp757824 (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 55786315 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl rfl (hp757928 rfl rfl rfl rfl rfl) hp757896

noncomputable def hp757930 := nat_lit 1097888916183342777587140716321

noncomputable def hp757931 := BSN.cos_dyadic_bound_f 32369769 536870912 2 1 536870912 268435456 hp757930 hp708767 hp757930 hp757930 hp708768

noncomputable def hp757932 := @BSN.binarySplit_of_base (BSN.cosEvenP 32369769) (BSN.cosEvenQ 536870912) 0 1 hp757930 hp708767 hp757930 rfl rfl rfl

noncomputable def hp757933 := hp757931 hp757930 535895365 rfl rfl rfl rfl rfl rfl rfl rfl (hp757932 rfl)

noncomputable def hp757934 := @BSN.binarySplit_of_base (BSN.cosOddP 32369769) (BSN.cosOddQ 536870912) 0 1 hp757930 hp708768 hp757930 rfl rfl rfl

noncomputable def hp757935 := nat_lit 53103420535091674073127396246695513899353886557946091823239029576727218375877850037614946721653954141487104000000

noncomputable def hp757936 := nat_lit 56823501852082092111757056801102584361012869893803837096378807713571013595189650372530648518656000000000000

noncomputable def hp757937 := nat_lit 321570479466176578776794651227153586643415140218144642143320745688898852325816641160817826958709875837606297600000

noncomputable def hp757938 := BSN.cos_dyadic_bound_f 787427660 536870912 4 3 536870912 268435456 hp757935 hp716712 hp757936 hp757937 hp716714

noncomputable def hp757939 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 787427660) (BSN.cosEvenQ 536870912) 0 3 hp757935 hp716712 hp757936 rfl rfl rfl

noncomputable def hp757940 := hp757938 hp757936 55786315 rfl rfl rfl rfl rfl rfl rfl rfl (hp757939 rfl)

noncomputable def hp757941 := @BSN.binarySplit_of_base3 (BSN.cosOddP 787427660) (BSN.cosOddQ 536870912) 0 3 hp757937 hp716714 hp757936 rfl rfl rfl

noncomputable def hp757942 := hp757929 hd4928 hd4930 hd4932 hd4934 hd4918 (hp757933 (hp757934 rfl) rfl rfl rfl rfl) (hp757940 (hp757941 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757943 := hp757819 (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 346618678 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl rfl (hp757942 rfl rfl rfl rfl rfl) hp757896

noncomputable def hp757944 := nat_lit 4567497974874717850959633895696

noncomputable def hp757945 := BSN.sin_dyadic_bound_f 46229542 536870912 2 1 536870912 268435456 hp757944 hp708890 hp757944 hp757944 hp708891

noncomputable def hp757946 := @BSN.binarySplit_of_base (BSN.sinEvenP 46229542) (BSN.sinEvenQ 536870912) 0 1 hp757944 hp708890 hp757944 rfl rfl rfl

noncomputable def hp757947 := hp757945 hp757944 46172432 rfl rfl rfl rfl rfl rfl rfl rfl (hp757946 rfl)

noncomputable def hp757948 := @BSN.binarySplit_of_base (BSN.sinOddP 46229542) (BSN.sinOddQ 536870912) 0 1 hp757944 hp708891 hp757944 rfl rfl rfl

noncomputable def hp757949 := nat_lit 6612988426386689859741200781220318276823690568741502503242252706992169216

noncomputable def hp757950 := nat_lit 2243485387299856467075651483622772264402153968758742068692376042414336

noncomputable def hp757951 := nat_lit 19834478308385469866289451040693709285942267398286990025589373368891678976

noncomputable def hp757952 := BSN.cos_dyadic_bound_f 466514778 536870912 3 2 536870912 268435456 hp757949 hp708868 hp757950 hp757951 hp708870

noncomputable def hp757953 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 466514778) (BSN.cosEvenQ 536870912) 0 2 hp757949 hp708868 hp757950 rfl rfl rfl

noncomputable def hp757954 := hp757952 hp757950 346618678 rfl rfl rfl rfl rfl rfl rfl rfl (hp757953 rfl)

noncomputable def hp757955 := @BSN.binarySplit_of_base2 (BSN.cosOddP 466514778) (BSN.cosOddQ 536870912) 0 2 hp757951 hp708870 hp757950 rfl rfl rfl

noncomputable def hp757956 := hp757943 hd4936 hd4938 hd4940 hd4942 hd4918 (hp757947 (hp757948 rfl) rfl rfl rfl rfl) (hp757954 (hp757955 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757957 := hp757815 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 215211533 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl rfl (hp757956 rfl rfl rfl rfl rfl) hp757896

noncomputable def hp757958 := nat_lit 2005555758226939645556674017005321589364816081577190504425446816688030625

noncomputable def hp757959 := nat_lit 63726389532219545477973068131063228031212570964200891814477375390625

noncomputable def hp757960 := nat_lit 5252542857392265954336705707189344345967229679015842614908470604146590625

noncomputable def hp757961 := BSN.sin_dyadic_bound_f 298909635 536870912 3 2 536870912 268435456 hp757958 hp708845 hp757959 hp757960 hp708848

noncomputable def hp757962 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 298909635) (BSN.sinEvenQ 536870912) 0 2 hp757958 hp708845 hp757959 rfl rfl rfl

noncomputable def hp757963 := hp757961 hp757959 283704333 rfl rfl rfl rfl rfl rfl rfl rfl (hp757962 rfl)

noncomputable def hp757964 := @BSN.binarySplit_of_base2 (BSN.sinOddP 298909635) (BSN.sinOddQ 536870912) 0 2 hp757960 hp708848 hp757959 rfl rfl rfl

noncomputable def hp757965 := nat_lit 20623891521522216923221992329368874996295834322882289189714605208343878637581354508718056033911566813816384000000

noncomputable def hp757966 := nat_lit 3345507953353434808863950917530743926049817460905147182476019137430357173199446066523082612241000000000000

noncomputable def hp757967 := nat_lit 125028969643777056400517060050906264915131481448238878135360773615079810736405154131188541789822347981651929600000

noncomputable def hp757968 := BSN.cos_dyadic_bound_f 621877970 536870912 4 3 536870912 268435456 hp757965 hp716712 hp757966 hp757967 hp716714

noncomputable def hp757969 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 621877970) (BSN.cosEvenQ 536870912) 0 3 hp757965 hp716712 hp757966 rfl rfl rfl

noncomputable def hp757970 := hp757968 hp757966 215211533 rfl rfl rfl rfl rfl rfl rfl rfl (hp757969 rfl)

noncomputable def hp757971 := @BSN.binarySplit_of_base3 (BSN.cosOddP 621877970) (BSN.cosOddQ 536870912) 0 3 hp757967 hp716714 hp757966 rfl rfl rfl

noncomputable def hp757972 := hp757957 hd4944 hd4946 hd4961 hd4963 hd4918 (hp757963 (hp757964 rfl) rfl rfl rfl rfl) (hp757970 (hp757971 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757973 := @hp757810 51371 67108864 (hp757972 rfl rfl rfl rfl rfl) (hp757972 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp757974 := @hp757808 Bool.false 674223191 268435456 51371 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 846837 1000)) (Enclosure.sfrac Bool.false 846837 1000) 11) hp757973

noncomputable def hp757975 := @Enclosure.Real.IsNear.mulLit_tf hp757799 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1))) 9847929 33554432 1

noncomputable def hp757976 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp757798 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757977 := @hp757976 1 1 0 1 9847929 33554432 1 33554432 9847929 33554432 1

noncomputable def hp757978 := @Enclosure.Real.IsNear.of_eq (hp757798 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757979 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 846837 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757980 := @hp757978 (@Inv.inv Real Real.instInv (Real.sqrt hp757800)) Bool.false 9847929 33554432 1 33554432 (hp757979 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 846837 1000) 846837 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000))))

noncomputable def hp757981 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp757800)) Bool.false 19695858 67108864 2 67108864 9847929 33554432

noncomputable def hp757982 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp757800) Bool.false 228657195 67108864 7 67108864 228657195 67108864 7 67108864

noncomputable def hp757983 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 846837 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757984 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 846837 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757985 := @hp757984 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 846837 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9044817873759

noncomputable def hp757986 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 846837 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 846837 1000 0

noncomputable def hp757987 := @hp757986 1 10680707 67108864 1 67108864 9044817873759 67108864000 846837 67108864000 (Enclosure.Real.IsNear.const Bool.false 846837 1000) hd4949

noncomputable def hp757988 := @hp757985 67108864000 846837 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 846837 1000) 846837 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000))) (hp757987 rfl)

noncomputable def hp757989 := @hp757983 9044817873759 67108864000 846837 67108864000 389546979 389547016 33554432 hp757988 rfl rfl rfl

noncomputable def hp757990 := @Enclosure.Real.IsNear.recentre' hp757800 Bool.false 779093995 67108864 37 67108864 779093995 67108864 37 67108864 (hp757989 rfl rfl rfl)

noncomputable def hp757991 := @Enclosure.Real.IsNear.sqrt_image hp757800 779093995 67108864 37 67108864 114328594 114328601 33554432 (hp757990 rfl) rfl rfl

noncomputable def hp757992 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp757800) 228657195 67108864 7 67108864 9847928 9847930 33554432 (hp757982 (hp757991 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp757993 := @hp757977 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp757980 (@hp757981 1 33554432 (hp757992 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp757994 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757995 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp757996 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1))) (hp757994 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757995 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp757997 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 846837 1000) 846837 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl

noncomputable def hp757998 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757999 := @hp757998 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757995 (Enclosure.sfrac Bool.false 1 16)))) 86828475

noncomputable def hp758000 := @hp757999 67108864 401 67108864 10475203 33554432 356077429 45675970560000 909545901805425 2251799813685248 18317905166311777 1532631248189521920000

noncomputable def hp758001 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758002 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758003 := @hp758001 (@Neg.neg Real Real.instNeg hp758002) Bool.true 86828475 67108864 401 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758004 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758005 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp758006 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp758007 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 256960231) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp758008 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1))) Bool.false 36163937569711416025505

noncomputable def hp758009 := nat_lit 998484790485927864573568451

noncomputable def hp758010 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp758011 := @Enclosure.Real.IsNear.subLit_ff_p hp757800 (Enclosure.sfrac Bool.false 11 1) 779093995 67108864 37 67108864 11 1 0

noncomputable def hp758012 := @hp758010 500000000000000 40896491 67108864 37 67108864 36163937569711416025505 9444732965739290427392 hp758009 hp738031 hd4948 (@hp758011 1 40896491 40896491 67108864 37 67108864 (hp757990 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758013 := @hp758007 256960231 67108864 233 67108864 Bool.true 51867773 67108864 1 10890000 (@hp758008 9444732965739290427392 hp758009 hp738031 256960231 67108864 233 67108864 (hp758012 rfl) rfl) (Enclosure.sfrac_false_div 256960231 67108864)

noncomputable def hp758014 := nat_lit 6648252229489662929928192

noncomputable def hp758015 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 256960231) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp758014) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp758016 := BSN.sin_reduce_arg_pos_rat_q2 256960231 67108864 226375608064910080 72057594037927936 0 hp758014 hp617687 rfl rfl rfl rfl

noncomputable def hp758017 := nat_lit 47765805752778076871414289800949935580998774706436151954554798820356769046424519295976727681

noncomputable def hp758018 := nat_lit 6347774621761359303534632903939665783388044898235349062190786317312006642615084907881601

noncomputable def hp758019 := nat_lit 143284721709090707895635800137041927411429548029511985165540014888435683125988327718114419841

noncomputable def hp758020 := BSN.cos_dyadic_bound_f 94477346543 137438953472 3 2 67108864 21801270 hp758017 hp746621 hp758018 hp758019 hp746624

noncomputable def hp758021 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 94477346543) (BSN.cosEvenQ 137438953472) 0 2 hp758017 hp746621 hp758018 rfl rfl rfl

noncomputable def hp758022 := hp758020 hp758018 51867773 rfl rfl rfl rfl rfl rfl rfl rfl (hp758021 rfl)

noncomputable def hp758023 := @BSN.binarySplit_of_base2 (BSN.cosOddP 94477346543) (BSN.cosOddQ 137438953472) 0 2 hp758019 hp746624 hp758018 rfl rfl rfl

noncomputable def hp758024 := @BSN.cos_arg_round Bool.false 51867773 67108864 hp758014 hp617687 94477346543 137438953472 21801270 21780000 (hp758022 (hp758023 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758025 := hp758015 51867773 67108864 0 1000000000000000 21780000 10890000 hp758016 BSN.pi_near_15 hp758024 rfl rfl

noncomputable def hp758026 := @hp758005 51867773 67108864 162779929 45675970560000 (@hp758006 51867773 67108864 2604478864 730815528960000 51867773 67108864 162779929 45675970560000 (hp758013 (hp758025 rfl rfl) rfl rfl) rfl)

noncomputable def hp758027 := @hp758004 51867773 67108864 162779929 45675970560000 43414037 43414438 33554432 hp758026 rfl rfl rfl

noncomputable def hp758028 := @Enclosure.Real.IsNear.recentre' hp758002 Bool.false 86828475 67108864 401 67108864 86828475 67108864 401 67108864 (hp758027 rfl rfl rfl)

noncomputable def hp758029 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757995 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp758030 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757995 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 63360459)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp758031 := nat_lit 1196845234038220214746584955445

noncomputable def hp758032 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757995 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp758031

noncomputable def hp758033 := nat_lit 29735253081906478754616839816038973

noncomputable def hp758034 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757995 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp758035 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp758036 := @hp758035 (Enclosure.sfrac Bool.false 1 16) 1071994076483143 4503599627370496 5509369671 4503599627370496 1 16 0

noncomputable def hp758037 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)) 1672522976113081

noncomputable def hp758038 := @hp758037 4503599627370496 3026341703 4503599627370496 40896491 67108864 37 67108864 71940304687512841879552 1071994076483143 4503599627370496 5509369671

noncomputable def hp758039 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)) 40896491 67108864 37

noncomputable def hp758040 := @hp758039 67108864 40896491 67108864 37 67108864 1672522976113081 4503599627370496 3026341703 4503599627370496 (@hp758011 1 40896491 40896491 67108864 37 67108864 (hp757990 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758041 := hp758040 (@hp758011 1 40896491 40896491 67108864 37 67108864 (hp757990 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758042 := @hp758038 4503599627370496 (hp758041 rfl) (@hp758011 1 40896491 40896491 67108864 37 67108864 (hp757990 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758043 := @hp758034 500000000000000 1353469053193799 4503599627370496 5509369671 4503599627370496 hp758031 hp627574 hp758033 hp742826 hd4948 (@hp758036 1 21655504851100784 1353469053193799 4503599627370496 5509369671 4503599627370496 (hp758042 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp758044 := @hp758030 63360459 33554432 517 67108864 Bool.true 10475203 33554432 1 10890000 (@hp758032 hp627574 hp758033 hp742826 63360459 33554432 517 67108864 (hp758043 rfl) rfl) (Enclosure.sfrac_true_div 63360459 33554432)

noncomputable def hp758045 := nat_lit 520805839921882656488914662419319869863227140866534892310365596104625814206851094671999652249154961

noncomputable def hp758046 := nat_lit 4186198105792145766990861678238469456588203089321697879972806761454979138993177673472190920081

noncomputable def hp758047 := nat_lit 3143713675290720352716265369986935366348440555051110296501021389852009056088508522057330881939846545

noncomputable def hp758048 := BSN.cos_dyadic_bound_t 63360459 33554432 4 3 33554432 10890000 hp758045 hp681868 hp758046 hp758047 hp681871

noncomputable def hp758049 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 63360459) (BSN.cosEvenQ 33554432) 0 3 hp758045 hp681868 hp758046 rfl rfl rfl

noncomputable def hp758050 := hp758048 hp758046 10475203 rfl rfl rfl rfl rfl rfl rfl rfl (hp758049 rfl)

noncomputable def hp758051 := @BSN.binarySplit_of_base3 (BSN.cosOddP 63360459) (BSN.cosOddQ 33554432) 0 3 hp758047 hp681871 hp758046 rfl rfl rfl

noncomputable def hp758052 := hp758044 (BSN.cos_neg_of_bound 63360459 33554432 Bool.true 10475203 33554432 1 10890000 (hp758050 (hp758051 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp758053 := hp758000 (hp758003 (@Enclosure.Real.IsNear.neg hp758002 Bool.false 86828475 67108864 401 67108864 (hp758028 rfl))) (@hp758029 10475203 33554432 5697238864 730815528960000 10475203 33554432 356077429 45675970560000 (hp758052 rfl) rfl)

noncomputable def hp758054 := @hp757975 33554432 909545901805425 2251799813685248 18317905166311777 1532631248189521920000 8957143463220797214825 75557863725914323419136 36202501500778611092447 hp757796 (hp757993 rfl) (@hp757996 Bool.false 909545901805425 2251799813685248 18317905166311777 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757800 (Enclosure.sfrac Bool.false 11 1)) (hp757997 rfl (hp757803 rfl rfl))) (hp758053 rfl))

noncomputable def hp758055 := @hp757797 hp757794 hp757796 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 846837 1000))) (@hp757802 hp757794 hp757796 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 846837 1000) 11 (hp757803 rfl rfl)) (@hp757806 hp757794 hp757796 hp757974 (hp758054 rfl) rfl rfl))

theorem hd5041 : hp757795 hp757796 := hp758055

noncomputable def hp758056 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 848118 1000)) Bool.true 2012623543766027380309 9444732965739290427392 1100504667036348179557697

noncomputable def hp758057 := nat_lit 1428515861068067677143040000

noncomputable def hp758058 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 848118 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 848118 1000)) Bool.true 2012623543766027380309 9444732965739290427392

noncomputable def hp758059 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 848118 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758060 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp758059 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp758061 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 848118 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758062 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp758060 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp758063 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 848118 1000)) hp758062 Bool.true 2012623543766027380309 9444732965739290427392

noncomputable def hp758064 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 848118 1000) 848118 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl

noncomputable def hp758065 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp758060 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp758066 := nat_lit 270129759363584758570865917952

noncomputable def hp758067 := @hp758065 44648031 134217728 102901 134217728 1129202327709384399275 9444732965739290427392 5301277661695435877697 hp758057 hp758066 2012623543766027380309 9444732965739290427392

noncomputable def hp758068 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) 11)

noncomputable def hp758069 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) 11) hp758068

noncomputable def hp758070 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) 11)

noncomputable def hp758071 := @hp758070 89296062 536870912 205802 536870912 89296062 536870912 205802 536870912 95880916487897088 44648031 134217728

noncomputable def hp758072 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp758073 := hp758072 BSN.quadSignPos 9 10 11 848118 1000 189 240 536870912 268435456 9007199254740992

noncomputable def hp758074 := hp758073 Bool.false 888853274089 3865 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp758075 := hp758074 Bool.true 103715890 176675 Bool.true 196019247 Bool.true 584535409 28296951008113761 1 Bool.false 191693013

noncomputable def hp758076 := hp758075 Bool.true Bool.false 248874508 Bool.false Bool.true 89296062 205802 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 191693013 536870912) BSN.abs_quadSignPos

noncomputable def hp758077 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp758078 := hp758077 BSN.quadSignPos 7 8 9 848118 1000 68 132 536870912 268435456 9007199254740992

noncomputable def hp758079 := hp758078 Bool.false 888853274089 3865 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp758080 := hp758079 Bool.true 329401223 144290 Bool.true 633191132 Bool.true 291164614 28296951008113761 1 Bool.false 204800100

noncomputable def hp758081 := hp758080 Bool.false Bool.false 459832693 Bool.false Bool.true 103715890 176675 BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 204800100 536870912) BSN.abs_quadSignPos

noncomputable def hp758082 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp758083 := hp758082 BSN.quadSignPos 5 6 7 848118 1000 86 3 536870912 268435456 9007199254740992

noncomputable def hp758084 := hp758083 Bool.false 888853274089 3865 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp758085 := hp758084 Bool.true 299345911 107225 Bool.false 486571106 Bool.false 292299851 28296951008113761 1 Bool.false 331064333

noncomputable def hp758086 := hp758085 Bool.true Bool.false 278071462 Bool.false Bool.true 329401223 144290 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 86 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 331064333 536870912) BSN.abs_quadSignPos

noncomputable def hp758087 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp758088 := hp758087 BSN.quadSignNeg 3 4 5 848118 1000 305 185 536870912 268435456 9007199254740992

noncomputable def hp758089 := hp758088 Bool.false 888853274089 3865 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp758090 := hp758089 Bool.true 103119467 63376 Bool.false 421003844 Bool.false 14860873 28296951008113761 1 Bool.false 379162627

noncomputable def hp758091 := hp758090 Bool.true Bool.false 14858975 Bool.true Bool.true 299345911 107225 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 305 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 379162627 536870912) BSN.abs_quadSignNeg

noncomputable def hp758092 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp758093 := hp758092 BSN.quadSignPos 1 2 3 848118 1000 679 460 536870912 268435456 9007199254740992

noncomputable def hp758094 := hp758093 Bool.false 888853274089 3865 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp758095 := hp758094 Bool.true 536870592 3922 Bool.false 631873787 Bool.false 697438504 28296951008113761 1 Bool.false 495769386

noncomputable def hp758096 := hp758095 Bool.false Bool.false 144087970 Bool.false Bool.true 103119467 63376 BSN.abs_quadSignPos (BSN.cos_quad_nat3 679 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 495769386 536870912) BSN.abs_quadSignPos

noncomputable def hp758097 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) 1) Bool.true

noncomputable def hp758098 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)))

noncomputable def hp758099 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000))) Bool.true 67108824 67108864

noncomputable def hp758100 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 111106659261) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 111106659261 67108864

noncomputable def hp758101 := nat_lit 17343555329948530208403075784084702898879732886678135101

noncomputable def hp758102 := nat_lit 10475576384465662984433476272543761345745827292774400

noncomputable def hp758103 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) Bool.false hp758101 hp758102 64195728671301541757

noncomputable def hp758104 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 848118 4000) (Real.log (Enclosure.sfrac Bool.false 2877217567696 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1696236))))))

noncomputable def hp758105 := nat_lit 210631355418444537316311080432640000

noncomputable def hp758106 := nat_lit 1071841637215026899638147443202954629120

noncomputable def hp758107 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp758104 (Enclosure.sfrac Bool.false 848118 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 848118 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp758105 hp758106)) Bool.false

noncomputable def hp758108 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 848118 1000) 848118 1000 2877217567696 16000000 1696236

noncomputable def hp758109 := hp758108 4000 2000 hp758105 hp758106 (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl rfl rfl rfl

noncomputable def hp758110 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp758104 (Enclosure.sfrac Bool.false 848118 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 848118 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp758105 hp758106) 2982497028350199749561 1801439850948198400

noncomputable def hp758111 := nat_lit 3196764118416113088012854928522492438321512365672513861816320

noncomputable def hp758112 := @hp758110 64195728671301541757 hp739631 hp758105 hp758106 0 1 hp758111 hp758101 hp758102 64195728671301541757 hp739631

noncomputable def hp758113 := @Enclosure.Real.IsNear.subLit_ff_p (hp758104 (Enclosure.sfrac Bool.false 848118 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 848118 2000) (Real.log Real.pi)) 19284876980750529710749 9007199254740992000 5350745350876517 2178000000000000000000

noncomputable def hp758114 := nat_lit 500379968639894248415308021760000

noncomputable def hp758115 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 848118 4000) (Real.log (Enclosure.sfrac Bool.false 2877217567696 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1696236))))))

noncomputable def hp758116 := @hp758115 (Enclosure.sfrac Bool.false 848118 2000) 23104460889516740037277 9007199254740992000 5350745350876517 2178000000000000000000 848118 2000 0

noncomputable def hp758117 := nat_lit 38569753961501059421498000

noncomputable def hp758118 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 848118 4000) (Real.log (Enclosure.sfrac Bool.false 2877217567696 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1696236))))) 23107996680912315473277

noncomputable def hp758119 := nat_lit 52026620726311894491929528706264989696

noncomputable def hp758120 := @hp758118 9007199254740992000 1766915116868089 726000000000000000000 883947848893859 2251799813685248 200000001089 8712000000000000000 hp758119 23104460889516740037277 9007199254740992000 5350745350876517

noncomputable def hp758121 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 848118 4000) (Real.log (Enclosure.sfrac Bool.false 2877217567696 16000000)) 848118 4000 0 1 54492409501772903 4503599627370496

noncomputable def hp758122 := nat_lit 117021558345177136201990144

noncomputable def hp758123 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2877217567696) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp758122 hp617687

noncomputable def hp758124 := BSN.log_rat_reduce_isNear 2877217567696 16000000 17 5754435135392 4194304000000 84890960 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp758125 := nat_lit 354271479224331527141250455623970178859543698983670315192418174292757381155601196961328046961684140523520

noncomputable def hp758126 := nat_lit 2947645553178658509506637830418291465684635881901794186370999599198238323892140386116608934000600285184

noncomputable def hp758127 := nat_lit 14395878303625528444718579917247601380664579373206376088536871449047085218057036087492705811169280

noncomputable def hp758128 := BSN.log_dyadic_bound 780065567696 4974369567696 5 4 hp758125 268435456 87120000 hp758126 hp758127 84890960 5754435135392

noncomputable def hp758129 := hp758128 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp758130 := @BSN.binarySplit_of_base4 (BSN.artanhP 780065567696) (BSN.artanhQ 4974369567696) 0 4 hp758126 hp758125 hp758127 rfl rfl rfl

noncomputable def hp758131 := hp758124 rfl rfl rfl rfl (hp758129 (hp758130 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp758132 := @hp758121 12500018513 1089000000000000000 23107996680912315473277 9007199254740992000 1766915116868089 726000000000000000000 (Enclosure.Real.IsNear.const Bool.false 848118 4000) (BSN.isNear_log_sfrac 2877217567696 16000000 54492409501772903 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp758123 1000001481040000 87120000000000000000000 54492409501772903 4503599627370496 12500018513 1089000000000000000 (hp758131 rfl rfl rfl) rfl)) rfl

noncomputable def hp758133 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1696236)))) 1 4

noncomputable def hp758134 := @hp758133 0 1 883947848893859 562949953421312 200000001089 2178000000000000000 883947848893859 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp758135 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1696236))) 884279719003555 562949953421312 1

noncomputable def hp758136 := @hp758135 2000000000000000 19781 33554432 1 10890000 29660367987255267033088 883947848893859 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp758137 := BSN.arctan_dyadic_bound_f 1000 1696236 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp758138 := hp758137 1 19781 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1696236) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1696236) 0 0 rfl)

noncomputable def hp758139 := hp758134 (hp758136 (hp758138 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp758140 := @hp758113 16288428898899 33554432000 1272177 268435456000 hp758114 2982497028350199749561 1801439850948198400 64195728671301541757 hp739631 (@hp758116 1 hp758117 19284876980750529710749 9007199254740992000 5350745350876517 2178000000000000000000 (@hp758120 2178000000000000000000 hp758132 hp758139 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 848118 2000) rfl rfl)

noncomputable def hp758141 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 848118 2000) (Real.log Real.pi) 848118 2000 0 1 38410761 33554432

noncomputable def hp758142 := hp758140 (@hp758141 3 268435456 16288428898899 33554432000 1272177 268435456000 (Enclosure.Real.IsNear.const Bool.false 848118 2000) hd4909 rfl) rfl

noncomputable def hp758143 := @hp758103 hp739631 111106659261 67108864 121 16777216 (@hp758107 hp758101 hp758102 64195728671301541757 hp739631 (hp758109 rfl rfl rfl rfl rfl) (hp758112 (hp758142 rfl) (Enclosure.Real.IsNear.const Bool.true hp758105 hp758106) rfl rfl)) rfl

noncomputable def hp758144 := nat_lit 15181276922791112560607232

noncomputable def hp758145 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 111106659261) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp758144) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp758146 := BSN.sin_reduce_arg_pos_rat_q1 111106659261 67108864 226375608064910080 72057594037927936 263 hp758144 hp617687 rfl rfl rfl rfl

noncomputable def hp758147 := nat_lit 14340462194036978993539216142375451483226940089237090795813375893296143324052344077267894211698238997787175839481852304201219222469754442531281

noncomputable def hp758148 := nat_lit 10165810774483449057845143601671353564531886586622010467326791227355095739618558333410719449045768010260989891878174125308635554154070481

noncomputable def hp758149 := nat_lit 71613458462818193844120008980151885759808101254069098395188328095514165155663838660401627003972313227247522341575261282921206703427361825407441

noncomputable def hp758150 := BSN.sin_dyadic_bound_f 215738920741 137438953472 4 3 67108864 21801270 hp758147 hp737934 hp758148 hp758149 hp737937

noncomputable def hp758151 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215738920741) (BSN.sinEvenQ 137438953472) 0 3 hp758147 hp737934 hp758148 rfl rfl rfl

noncomputable def hp758152 := hp758150 hp758148 67108824 rfl rfl rfl rfl rfl rfl rfl rfl (hp758151 rfl)

noncomputable def hp758153 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215738920741) (BSN.sinOddQ 137438953472) 0 3 hp758149 hp737937 hp758148 rfl rfl rfl

noncomputable def hp758154 := @BSN.sin_arg_round Bool.false 67108824 67108864 hp758144 hp617687 215738920741 137438953472 21801270 21780000 (hp758152 (hp758153 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758155 := hp758145 67108824 67108864 263 1000000000000000 21780000 10890000 hp758146 BSN.pi_near_15 hp758154 rfl rfl

noncomputable def hp758156 := @hp758100 121 16777216 Bool.true 67108824 67108864 1 10890000 hp758143 (Enclosure.sfrac_false_div 111106659261 67108864) (hp758155 rfl rfl) rfl

noncomputable def hp758157 := @hp758097 8388603 8388608 83404201 11418992640000 536870592 536870912 3922 536870912 (@hp758098 Bool.true 8388603 8388608 83404201 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000)) (@hp758099 1334467216 182703882240000 8388603 8388608 83404201 11418992640000 (hp758156 rfl) rfl))

noncomputable def hp758158 := @hp758103 hp739631 888853274089 536870912 3865 536870912 (@hp758107 hp758101 hp758102 64195728671301541757 hp739631 (hp758109 rfl rfl rfl rfl rfl) (hp758112 (hp758142 rfl) (Enclosure.Real.IsNear.const Bool.true hp758105 hp758106) rfl rfl)) rfl

noncomputable def hp758159 := hp758096 (BSN.cos_quad_nat0 460 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 144087970 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl rfl (hp758157 rfl) hp758158

noncomputable def hp758160 := nat_lit 57128779066306434004099240763312524012640696872731297408389633904286263323465948939283673418983576503672701939281

noncomputable def hp758161 := nat_lit 4051017046841870579697906443255282132236664043689062773673220087647100943123532794228176491431499465715281

noncomputable def hp758162 := nat_lit 285531902927220750074599307359478762808988348051871425461037625462850714424607951328279379136818790360013155561041

noncomputable def hp758163 := BSN.sin_dyadic_bound_f 631873787 536870912 4 3 536870912 268435456 hp758160 hp642702 hp758161 hp758162 hp642705

noncomputable def hp758164 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 631873787) (BSN.sinEvenQ 536870912) 0 3 hp758160 hp642702 hp758161 rfl rfl rfl

noncomputable def hp758165 := hp758163 hp758161 495769386 rfl rfl rfl rfl rfl rfl rfl rfl (hp758164 rfl)

noncomputable def hp758166 := @BSN.binarySplit_of_base3 (BSN.sinOddP 631873787) (BSN.sinOddQ 536870912) 0 3 hp758162 hp642705 hp758161 rfl rfl rfl

noncomputable def hp758167 := nat_lit 32647068419578067973083421011508577275175997108731199982285763853082571495937554787213884613167995596766598660096

noncomputable def hp758168 := nat_lit 13245581871952091749312896825193351012023099009207446816617682347933096510292547909001815824281683116425216

noncomputable def hp758169 := nat_lit 197835353410728403711116456112462307399871308424046772362402645098712452358709907314234267085365919803753396961280

noncomputable def hp758170 := BSN.cos_dyadic_bound_f 697438504 536870912 4 3 536870912 268435456 hp758167 hp716712 hp758168 hp758169 hp716714

noncomputable def hp758171 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 697438504) (BSN.cosEvenQ 536870912) 0 3 hp758167 hp716712 hp758168 rfl rfl rfl

noncomputable def hp758172 := hp758170 hp758168 144087970 rfl rfl rfl rfl rfl rfl rfl rfl (hp758171 rfl)

noncomputable def hp758173 := @BSN.binarySplit_of_base3 (BSN.cosOddP 697438504) (BSN.cosOddQ 536870912) 0 3 hp758169 hp716714 hp758168 rfl rfl rfl

noncomputable def hp758174 := hp758159 hd4911 hd4913 hd4915 hd4917 hd4918 (hp758165 (hp758166 rfl) rfl rfl rfl rfl) (hp758172 (hp758173 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758175 := hp758091 (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 14858975 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl rfl (hp758174 rfl rfl rfl rfl rfl) hp758158

noncomputable def hp758176 := nat_lit 7893322253386748325874211359766499921196170605726866193345091399711784960

noncomputable def hp758177 := nat_lit 986934861067405581519785757489122838036627900284187485506491415330816

noncomputable def hp758178 := nat_lit 20671388959571184101586188193876326928061720855541332298070133632191758336

noncomputable def hp758179 := BSN.sin_dyadic_bound_f 421003844 536870912 3 2 536870912 268435456 hp758176 hp708845 hp758177 hp758178 hp708848

noncomputable def hp758180 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 421003844) (BSN.sinEvenQ 536870912) 0 2 hp758176 hp708845 hp758177 rfl rfl rfl

noncomputable def hp758181 := hp758179 hp758177 379162627 rfl rfl rfl rfl rfl rfl rfl rfl (hp758180 rfl)

noncomputable def hp758182 := @BSN.binarySplit_of_base2 (BSN.sinOddP 421003844) (BSN.sinOddQ 536870912) 0 2 hp758178 hp708848 hp758177 rfl rfl rfl

noncomputable def hp758183 := BSN.sin_dyadic_bound_f 14860873 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp758184 := hp758183 1 14858975 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 14860873) (BSN.sinEvenQ 536870912) 0 0 rfl)

noncomputable def hp758185 := hp758184 (@BSN.binarySplit_of_le (BSN.sinOddP 14860873) (BSN.sinOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp758186 := hp758175 hd4920 hd4922 hd4924 hd4926 hd4918 (hp758181 (hp758182 rfl) rfl rfl rfl rfl) hp758185 rfl

noncomputable def hp758187 := hp758086 (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 278071462 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl rfl (hp758186 rfl rfl rfl rfl rfl) hp758158

noncomputable def hp758188 := nat_lit 7826154554663727170232698693372905177569522133519673211824547836675850496

noncomputable def hp758189 := nat_lit 3141742055676731245394093533311890506768028625311518796528698654556416

noncomputable def hp758190 := nat_lit 23472180179879828048207307893052091751695030343308396597880586112718438656

noncomputable def hp758191 := BSN.cos_dyadic_bound_f 486571106 536870912 3 2 536870912 268435456 hp758188 hp708868 hp758189 hp758190 hp708870

noncomputable def hp758192 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 486571106) (BSN.cosEvenQ 536870912) 0 2 hp758188 hp708868 hp758189 rfl rfl rfl

noncomputable def hp758193 := hp758191 hp758189 331064333 rfl rfl rfl rfl rfl rfl rfl rfl (hp758192 rfl)

noncomputable def hp758194 := @BSN.binarySplit_of_base2 (BSN.cosOddP 486571106) (BSN.cosOddQ 536870912) 0 2 hp758190 hp708870 hp758189 rfl rfl rfl

noncomputable def hp758195 := nat_lit 1833953326953392109103288961862152286929440268915469342550900914299175265

noncomputable def hp758196 := nat_lit 53287917932856163200092931468273181406123133895852536281093767528801

noncomputable def hp758197 := nat_lit 4803124818725088042434861416321354975854828885895159754955523480874221921

noncomputable def hp758198 := BSN.sin_dyadic_bound_f 292299851 536870912 3 2 536870912 268435456 hp758195 hp708845 hp758196 hp758197 hp708848

noncomputable def hp758199 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 292299851) (BSN.sinEvenQ 536870912) 0 2 hp758195 hp708845 hp758196 rfl rfl rfl

noncomputable def hp758200 := hp758198 hp758196 278071462 rfl rfl rfl rfl rfl rfl rfl rfl (hp758199 rfl)

noncomputable def hp758201 := @BSN.binarySplit_of_base2 (BSN.sinOddP 292299851) (BSN.sinOddQ 536870912) 0 2 hp758197 hp708848 hp758196 rfl rfl rfl

noncomputable def hp758202 := hp758187 hd4928 hd4930 hd4932 hd4934 hd4918 (hp758193 (hp758194 rfl) rfl rfl rfl rfl) (hp758200 (hp758201 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758203 := hp758081 (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 459832693 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl rfl (hp758202 rfl rfl rfl rfl rfl) hp758158

noncomputable def hp758204 := nat_lit 22167871488106089083664419220986248562026926069258420202390475504353953554657760028358095742614962222134676422656

noncomputable def hp758205 := nat_lit 4153535110350873452965228001632486322350585698534620941779359665929139241172152920420400625497423610904576

noncomputable def hp758206 := nat_lit 134381924492907532709573144703483215726586033979098993288705307922437073663022980917004517326647846502944001228800

noncomputable def hp758207 := BSN.cos_dyadic_bound_f 633191132 536870912 4 3 536870912 268435456 hp758204 hp716712 hp758205 hp758206 hp716714

noncomputable def hp758208 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 633191132) (BSN.cosEvenQ 536870912) 0 3 hp758204 hp716712 hp758205 rfl rfl rfl

noncomputable def hp758209 := hp758207 hp758205 204800100 rfl rfl rfl rfl rfl rfl rfl rfl (hp758208 rfl)

noncomputable def hp758210 := @BSN.binarySplit_of_base3 (BSN.cosOddP 633191132) (BSN.cosOddQ 536870912) 0 3 hp758206 hp716714 hp758205 rfl rfl rfl

noncomputable def hp758211 := nat_lit 1003149159918138813874839368040403992199336949105336149580056413685063936

noncomputable def hp758212 := nat_lit 51654569119431118839310491798632934896040170137512553682280539136256

noncomputable def hp758213 := nat_lit 3009344170616177579386839483137614710728218766975733423632804679976919296

noncomputable def hp758214 := BSN.cos_dyadic_bound_f 291164614 536870912 3 2 536870912 268435456 hp758211 hp708868 hp758212 hp758213 hp708870

noncomputable def hp758215 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 291164614) (BSN.cosEvenQ 536870912) 0 2 hp758211 hp708868 hp758212 rfl rfl rfl

noncomputable def hp758216 := hp758214 hp758212 459832693 rfl rfl rfl rfl rfl rfl rfl rfl (hp758215 rfl)

noncomputable def hp758217 := @BSN.binarySplit_of_base2 (BSN.cosOddP 291164614) (BSN.cosOddQ 536870912) 0 2 hp758213 hp708870 hp758212 rfl rfl rfl

noncomputable def hp758218 := hp758203 hd4936 hd4938 hd4940 hd4942 hd4918 (hp758209 (hp758210 rfl) rfl rfl rfl rfl) (hp758216 (hp758217 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758219 := hp758076 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 248874508 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl rfl (hp758218 rfl rfl rfl rfl rfl) hp758158

noncomputable def hp758220 := nat_lit 1476368825309711838663449309046081

noncomputable def hp758221 := BSN.sin_dyadic_bound_f 196019247 536870912 2 1 536870912 268435456 hp758220 hp708890 hp758220 hp758220 hp708891

noncomputable def hp758222 := @BSN.binarySplit_of_base (BSN.sinEvenP 196019247) (BSN.sinEvenQ 536870912) 0 1 hp758220 hp708890 hp758220 rfl rfl rfl

noncomputable def hp758223 := hp758221 hp758220 191693013 rfl rfl rfl rfl rfl rfl rfl rfl (hp758222 rfl)

noncomputable def hp758224 := @BSN.binarySplit_of_base (BSN.sinOddP 196019247) (BSN.sinOddQ 536870912) 0 1 hp758220 hp708891 hp758220 rfl rfl rfl

noncomputable def hp758225 := nat_lit 16095007458922280258836980491434127099640694001611032379758942788410433505885700117312998764475117874543460631361

noncomputable def hp758226 := nat_lit 1591218762523164989248610769059576758349636745120084817904339076235802942452199280081187428414643969999681

noncomputable def hp758227 := nat_lit 97588631864005607960526783094677476770040022088735899701748319582585751214590914227106987660530250740553271755585

noncomputable def hp758228 := BSN.cos_dyadic_bound_f 584535409 536870912 4 3 536870912 268435456 hp758225 hp716712 hp758226 hp758227 hp716714

noncomputable def hp758229 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 584535409) (BSN.cosEvenQ 536870912) 0 3 hp758225 hp716712 hp758226 rfl rfl rfl

noncomputable def hp758230 := hp758228 hp758226 248874508 rfl rfl rfl rfl rfl rfl rfl rfl (hp758229 rfl)

noncomputable def hp758231 := @BSN.binarySplit_of_base3 (BSN.cosOddP 584535409) (BSN.cosOddQ 536870912) 0 3 hp758227 hp716714 hp758226 rfl rfl rfl

noncomputable def hp758232 := hp758219 hd4944 hd4946 hd4961 hd4963 hd4918 (hp758223 (hp758224 rfl) rfl rfl rfl rfl) (hp758230 (hp758231 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758233 := @hp758071 102901 134217728 (hp758232 rfl rfl rfl rfl rfl) (hp758232 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp758234 := @hp758069 Bool.true 44648031 134217728 102901 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 848118 1000)) (Enclosure.sfrac Bool.false 848118 1000) 11) hp758233

noncomputable def hp758235 := @Enclosure.Real.IsNear.mulLit_tf hp758060 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1))) 19688417 67108864 1

noncomputable def hp758236 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp758059 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp758237 := @hp758236 1 1 0 1 19688417 67108864 1 67108864 19688417 67108864 1

noncomputable def hp758238 := @Enclosure.Real.IsNear.of_eq (hp758059 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp758239 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 848118 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758240 := @hp758238 (@Inv.inv Real Real.instInv (Real.sqrt hp758061)) Bool.false 19688417 67108864 1 67108864 (hp758239 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 848118 1000) 848118 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000))))

noncomputable def hp758241 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp758061)) Bool.false 19688417 67108864 1 67108864 19688417 67108864

noncomputable def hp758242 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp758061) Bool.false 228743618 67108864 6 67108864 114371809 33554432 3 33554432

noncomputable def hp758243 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 848118 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758244 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 848118 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758245 := @hp758244 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 848118 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4529249929713

noncomputable def hp758246 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 848118 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 848118 1000 0

noncomputable def hp758247 := @hp758246 1 10680707 67108864 1 67108864 4529249929713 33554432000 424059 33554432000 (Enclosure.Real.IsNear.const Bool.false 848118 1000) hd4949

noncomputable def hp758248 := @hp758245 33554432000 424059 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 848118 1000) 848118 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000))) (hp758247 rfl)

noncomputable def hp758249 := @hp758243 4529249929713 33554432000 424059 33554432000 389841499 389841536 33554432 hp758248 rfl rfl rfl

noncomputable def hp758250 := @Enclosure.Real.IsNear.recentre' hp758061 Bool.false 779683035 67108864 37 67108864 779683035 67108864 37 67108864 (hp758249 rfl rfl rfl)

noncomputable def hp758251 := @Enclosure.Real.IsNear.sqrt_image hp758061 779683035 67108864 37 67108864 114371806 114371812 33554432 (hp758250 rfl) rfl rfl

noncomputable def hp758252 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp758061) 114371809 33554432 3 33554432 9844208 9844209 33554432 (hp758242 (hp758251 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp758253 := @hp758237 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp758240 (@hp758241 1 67108864 (hp758252 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp758254 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758255 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp758256 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1))) (hp758254 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758255 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp758257 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 848118 1000) 848118 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl

noncomputable def hp758258 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758259 := @hp758258 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758255 (Enclosure.sfrac Bool.false 1 16)))) 5693075

noncomputable def hp758260 := @hp758259 4194304 111 16777216 10074281 33554432 44764913 5709496320000 57353637304075 140737488355328 4838725621985347 383157812047380480000

noncomputable def hp758261 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758262 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758263 := @hp758261 (@Neg.neg Real Real.instNeg hp758262) Bool.true 5693075 4194304 111 16777216 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758264 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758265 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp758266 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp758267 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 130330639) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp758268 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1))) Bool.false 36684813695393270062705

noncomputable def hp758269 := nat_lit 998484790490987679645640131

noncomputable def hp758270 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp758271 := @Enclosure.Real.IsNear.subLit_ff_p hp758061 (Enclosure.sfrac Bool.false 11 1) 779683035 67108864 37 67108864 11 1 0

noncomputable def hp758272 := @hp758270 500000000000000 41485531 67108864 37 67108864 36684813695393270062705 9444732965739290427392 hp758269 hp738031 hd4948 (@hp758271 1 41485531 41485531 67108864 37 67108864 (hp758250 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758273 := @hp758267 130330639 33554432 117 33554432 Bool.true 49441642 67108864 1 10890000 (@hp758268 9444732965739290427392 hp758269 hp738031 130330639 33554432 117 33554432 (hp758272 rfl) rfl) (Enclosure.sfrac_false_div 130330639 33554432)

noncomputable def hp758274 := nat_lit 3590814656986122538713088

noncomputable def hp758275 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 130330639) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp758274) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp758276 := BSN.sin_reduce_arg_pos_rat_q2 130330639 33554432 226375608064910080 72057594037927936 0 hp758274 hp619237 rfl rfl rfl rfl

noncomputable def hp758277 := nat_lit 65042910666808258118394066659580208119599598525720466318732488204619690981448237988490519681

noncomputable def hp758278 := nat_lit 11769160207109796059487776546443867271642785145414504002127375260767993502168854521193601

noncomputable def hp758279 := nat_lit 195105193680010554763063224425647736624255510006870569948193209863337536957340376256429171841

noncomputable def hp758280 := BSN.cos_dyadic_bound_f 102057090799 137438953472 3 2 67108864 21801270 hp758277 hp746621 hp758278 hp758279 hp746624

noncomputable def hp758281 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 102057090799) (BSN.cosEvenQ 137438953472) 0 2 hp758277 hp746621 hp758278 rfl rfl rfl

noncomputable def hp758282 := hp758280 hp758278 49441642 rfl rfl rfl rfl rfl rfl rfl rfl (hp758281 rfl)

noncomputable def hp758283 := @BSN.binarySplit_of_base2 (BSN.cosOddP 102057090799) (BSN.cosOddQ 137438953472) 0 2 hp758279 hp746624 hp758278 rfl rfl rfl

noncomputable def hp758284 := @BSN.cos_arg_round Bool.false 49441642 67108864 hp758274 hp619237 102057090799 137438953472 21801270 21780000 (hp758282 (hp758283 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758285 := hp758275 49441642 67108864 0 1000000000000000 21780000 10890000 hp758276 BSN.pi_near_15 hp758284 rfl rfl

noncomputable def hp758286 := @hp758265 24720821 33554432 81730277 22837985280000 (@hp758266 49441642 67108864 1307684432 365407764480000 24720821 33554432 81730277 22837985280000 (hp758273 (hp758285 rfl rfl) rfl rfl) rfl)

noncomputable def hp758287 := @hp758264 24720821 33554432 81730277 22837985280000 45544378 45544822 33554432 hp758286 rfl rfl rfl

noncomputable def hp758288 := @Enclosure.Real.IsNear.recentre' hp758262 Bool.false 91089200 67108864 444 67108864 5693075 4194304 111 16777216 (hp758287 rfl rfl rfl)

noncomputable def hp758289 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758255 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp758290 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758255 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 125878605)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp758291 := nat_lit 1188889810672253400303491477845

noncomputable def hp758292 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758255 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp758291

noncomputable def hp758293 := nat_lit 29970512074203383790724241764006749

noncomputable def hp758294 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758255 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp758295 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp758296 := @hp758295 (Enclosure.sfrac Bool.false 1 16) 1062997575494823 4503599627370496 5552958631 4503599627370496 1 16 0

noncomputable def hp758297 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)) 1721049282351961

noncomputable def hp758298 := @hp758297 4503599627370496 3069930663 4503599627370496 41485531 67108864 37 67108864 71336559726211809411072 1062997575494823 4503599627370496 5552958631

noncomputable def hp758299 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)) 41485531 67108864 37

noncomputable def hp758300 := @hp758299 67108864 41485531 67108864 37 67108864 1721049282351961 4503599627370496 3069930663 4503599627370496 (@hp758271 1 41485531 41485531 67108864 37 67108864 (hp758250 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758301 := hp758300 (@hp758271 1 41485531 41485531 67108864 37 67108864 (hp758250 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758302 := @hp758298 4503599627370496 (hp758301 rfl) (@hp758271 1 41485531 41485531 67108864 37 67108864 (hp758250 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758303 := @hp758294 500000000000000 1344472552205479 4503599627370496 5552958631 4503599627370496 hp758291 hp627574 hp758293 hp742826 hd4948 (@hp758296 1 21511560835287664 1344472552205479 4503599627370496 5552958631 4503599627370496 (hp758302 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp758304 := @hp758290 125878605 67108864 65 8388608 Bool.true 10074281 33554432 1 10890000 (@hp758292 hp627574 hp758293 hp742826 125878605 67108864 65 8388608 (hp758303 rfl) rfl) (Enclosure.sfrac_true_div 125878605 67108864)

noncomputable def hp758305 := nat_lit 2076654181529411186118152797433047580415033510318732203110127340290726784028923335861372248099345640625

noncomputable def hp758306 := nat_lit 15827891205717536942316464235893756857840423563133899406094148473882668847266777400020273681640625

noncomputable def hp758307 := nat_lit 12536854302720281867711586487572455302315135061974795724045292088682383106561631280161029129315243240625

noncomputable def hp758308 := BSN.cos_dyadic_bound_t 125878605 67108864 4 3 33554432 10890000 hp758305 hp745658 hp758306 hp758307 hp745661

noncomputable def hp758309 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 125878605) (BSN.cosEvenQ 67108864) 0 3 hp758305 hp745658 hp758306 rfl rfl rfl

noncomputable def hp758310 := hp758308 hp758306 10074281 rfl rfl rfl rfl rfl rfl rfl rfl (hp758309 rfl)

noncomputable def hp758311 := @BSN.binarySplit_of_base3 (BSN.cosOddP 125878605) (BSN.cosOddQ 67108864) 0 3 hp758307 hp745661 hp758306 rfl rfl rfl

noncomputable def hp758312 := hp758304 (BSN.cos_neg_of_bound 125878605 67108864 Bool.true 10074281 33554432 1 10890000 (hp758310 (hp758311 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp758313 := hp758260 (hp758263 (@Enclosure.Real.IsNear.neg hp758262 Bool.false 5693075 4194304 111 16777216 (hp758288 rfl))) (@hp758289 10074281 33554432 716238608 91351941120000 10074281 33554432 44764913 5709496320000 (hp758312 rfl) rfl)

noncomputable def hp758314 := @hp758235 67108864 57353637304075 140737488355328 4838725621985347 383157812047380480000 1129202327709384399275 9444732965739290427392 5301277661695435877697 hp758057 (hp758253 rfl) (@hp758256 Bool.false 57353637304075 140737488355328 4838725621985347 383157812047380480000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758061 (Enclosure.sfrac Bool.false 11 1)) (hp758257 rfl (hp758064 rfl rfl))) (hp758313 rfl))

noncomputable def hp758315 := @hp758058 1100504667036348179557697 hp758057 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 848118 1000))) (@hp758063 1100504667036348179557697 hp758057 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 848118 1000) 11 (hp758064 rfl rfl)) (@hp758067 1100504667036348179557697 hp758057 hp758234 (hp758314 rfl) rfl rfl))

theorem hd5042 : hp758056 hp758057 := hp758315

noncomputable def hp758316 := nat_lit 39703786693814049292160479

noncomputable def hp758317 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 849559 1000)) Bool.false 66827976788258391850993 75557863725914323419136 hp758316

noncomputable def hp758318 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 849559 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 849559 1000)) Bool.false 66827976788258391850993 75557863725914323419136

noncomputable def hp758319 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 849559 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758320 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp758319 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp758321 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 849559 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758322 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp758320 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp758323 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 849559 1000)) hp758322 Bool.false 66827976788258391850993 75557863725914323419136

noncomputable def hp758324 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 849559 1000) 849559 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl

noncomputable def hp758325 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp758320 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp758326 := nat_lit 17938998422713556862347990007808

noncomputable def hp758327 := @hp758325 204993797 268435456 103073 134217728 9127352551854448050161 75557863725914323419136 210561532654401077120479 hp738860 hp758326 66827976788258391850993 75557863725914323419136

noncomputable def hp758328 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) 11)

noncomputable def hp758329 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) 11) hp758328

noncomputable def hp758330 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) 11)

noncomputable def hp758331 := @hp758330 204993797 536870912 206146 536870912 204993797 536870912 206146 536870912 220110413499465728 204993797 268435456

noncomputable def hp758332 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp758333 := hp758332 BSN.quadSignPos 9 10 11 849559 1000 189 240 536870912 268435456 9007199254740992

noncomputable def hp758334 := hp758333 Bool.false 890750987516 3870 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp758335 := hp758334 Bool.false 143912875 176971 Bool.true 79656987 Bool.true 541908059 28296951008113761 1 Bool.false 79365040

noncomputable def hp758336 := hp758335 Bool.true Bool.false 285821273 Bool.false Bool.false 204993797 206146 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 79365040 536870912) BSN.abs_quadSignPos

noncomputable def hp758337 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp758338 := hp758337 BSN.quadSignPos 7 8 9 849559 1000 68 132 536870912 268435456 9007199254740992

noncomputable def hp758339 := hp758338 Bool.false 890750987516 3870 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp758340 := hp758339 Bool.true 184469881 144532 Bool.true 344198110 Bool.true 93292178 28296951008113761 1 Bool.false 430262860

noncomputable def hp758341 := hp758340 Bool.false Bool.false 528785586 Bool.false Bool.false 143912875 176971 BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 430262860 536870912) BSN.abs_quadSignPos

noncomputable def hp758342 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp758343 := hp758342 BSN.quadSignPos 5 6 7 849559 1000 87 3 536870912 268435456 9007199254740992

noncomputable def hp758344 := hp758343 Bool.false 890750987516 3870 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp758345 := hp758344 Bool.true 440913200 107405 Bool.false 154809045 Bool.false 684596916 28296951008113761 1 Bool.false 152672597

noncomputable def hp758346 := hp758345 Bool.false Bool.false 513579986 Bool.false Bool.true 184469881 144532 BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 152672597 536870912) BSN.abs_quadSignPos

noncomputable def hp758347 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp758348 := hp758347 BSN.quadSignNeg 3 4 5 849559 1000 306 185 536870912 268435456 9007199254740992

noncomputable def hp758349 := hp758348 Bool.false 890750987516 3870 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp758350 := hp758349 Bool.true 17262706 63483 Bool.false 402922163 Bool.false 667463286 28296951008113761 1 Bool.false 392639074

noncomputable def hp758351 := hp758350 Bool.true Bool.false 508327475 Bool.true Bool.true 440913200 107405 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 306 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 392639074 536870912) BSN.abs_quadSignNeg

noncomputable def hp758352 := hp758332 BSN.quadSignNeg 1 2 3 849559 1000 681 462 536870912 268435456 9007199254740992

noncomputable def hp758353 := hp758352 Bool.false 890750987516 3870 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp758354 := hp758353 Bool.false 496130120 3930 Bool.false 306717387 Bool.false 58601720 28296951008113761 1 Bool.false 290302647

noncomputable def hp758355 := hp758354 Bool.true Bool.false 533675774 Bool.true Bool.true 17262706 63483 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 681 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 290302647 536870912) BSN.abs_quadSignNeg

noncomputable def hp758356 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) 1) Bool.false

noncomputable def hp758357 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)))

noncomputable def hp758358 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000))) Bool.false 62016265 67108864

noncomputable def hp758359 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 111343873439) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 111343873439 67108864

noncomputable def hp758360 := nat_lit 101137085694936788960471312620705797405660386835383746328809

noncomputable def hp758361 := nat_lit 60957057802964424819404556714632810726501057556381696000

noncomputable def hp758362 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) Bool.false hp758360 hp758361 42869635229579421419

noncomputable def hp758363 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 849559 4000) (Real.log (Enclosure.sfrac Bool.false 2887002977924 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1699118))))))

noncomputable def hp758364 := nat_lit 212426817982283766535052786463520000

noncomputable def hp758365 := nat_lit 1082814865380122612126792999636265526080

noncomputable def hp758366 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp758363 (Enclosure.sfrac Bool.false 849559 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 849559 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp758364 hp758365)) Bool.false

noncomputable def hp758367 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 849559 1000) 849559 1000 2887002977924 16000000 1699118

noncomputable def hp758368 := hp758367 4000 2000 hp758364 hp758365 (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl rfl rfl rfl

noncomputable def hp758369 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp758363 (Enclosure.sfrac Bool.false 849559 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 849559 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp758364 hp758365) 29888646973607787644161 18014398509481984000

noncomputable def hp758370 := nat_lit 32363867422379772467350820038625855169811323787322798825218880

noncomputable def hp758371 := @hp758369 42869635229579421419 hp737908 hp758364 hp758365 0 1 hp758370 hp758360 hp758361 42869635229579421419 hp737908

noncomputable def hp758372 := @Enclosure.Real.IsNear.subLit_ff_p (hp758363 (Enclosure.sfrac Bool.false 849559 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 849559 2000) (Real.log Real.pi)) 7729657705804969283021 3602879701896396800 3573167742810089 1452000000000000000000

noncomputable def hp758373 := nat_lit 401158628979171322070576188620800

noncomputable def hp758374 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 849559 4000) (Real.log (Enclosure.sfrac Bool.false 2887002977924 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1699118))))))

noncomputable def hp758375 := @hp758374 (Enclosure.sfrac Bool.false 849559 2000) 46300435720683348837633 18014398509481984000 3573167742810089 1452000000000000000000 849559 2000 0

noncomputable def hp758376 := nat_lit 77296577058049692830210000

noncomputable def hp758377 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 849559 4000) (Real.log (Enclosure.sfrac Bool.false 2887002977924 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1699118))))) 46307507307903684733633

noncomputable def hp758378 := nat_lit 104259312529380566121522580186919337984

noncomputable def hp758379 := @hp758377 18014398509481984000 10619503227885767 4356000000000000000000 883948402541987 2251799813685248 200000001089 8712000000000000000 hp758378 46300435720683348837633 18014398509481984000 3573167742810089

noncomputable def hp758380 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 849559 4000) (Real.log (Enclosure.sfrac Bool.false 2887002977924 16000000)) 849559 4000 0 1 54507700239658087 4503599627370496

noncomputable def hp758381 := nat_lit 117054394954751422943461376

noncomputable def hp758382 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2887002977924) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp758381 hp617687

noncomputable def hp758383 := BSN.log_rat_reduce_isNear 2887002977924 16000000 17 5774005955848 4194304000000 85802359 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp758384 := nat_lit 98342189295987009172599518941073985705052298863857894388768844431231304699750417357772437865219282946706168487275141482273985003520

noncomputable def hp758385 := nat_lit 835870457735995503362018768016540386404817528319883778632584366868676941432630125387311946121154553137792227124543160026743701504

noncomputable def hp758386 := nat_lit 89306570138142530119832746719607351799119725792727846517773799466650879478818371366319958939328577731712538688510435000320

noncomputable def hp758387 := BSN.log_dyadic_bound 789850977924 4984154977924 6 5 hp758384 268435456 87120000 hp758385 hp758386 85802359 5774005955848

noncomputable def hp758388 := hp758387 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp758389 := @BSN.binarySplit_of_base5 (BSN.artanhP 789850977924) (BSN.artanhQ 4984154977924) 0 5 hp758385 hp758384 hp758386 rfl rfl rfl

noncomputable def hp758390 := hp758383 rfl rfl rfl rfl (hp758388 (hp758389 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp758391 := @hp758380 12500018513 1089000000000000000 46307507307903684733633 18014398509481984000 10619503227885767 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 849559 4000) (BSN.isNear_log_sfrac 2887002977924 16000000 54507700239658087 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp758382 1000001481040000 87120000000000000000000 54507700239658087 4503599627370496 12500018513 1089000000000000000 (hp758390 rfl rfl rfl) rfl)) rfl

noncomputable def hp758392 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1699118)))) 1 4

noncomputable def hp758393 := @hp758392 0 1 883948402541987 562949953421312 200000001089 2178000000000000000 883948402541987 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp758394 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1699118))) 884279719003555 562949953421312 1

noncomputable def hp758395 := @hp758394 2000000000000000 19748 33554432 1 10890000 29660386564603729936384 883948402541987 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp758396 := BSN.arctan_dyadic_bound_f 1000 1699118 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp758397 := hp758396 1 19748 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1699118) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1699118) 0 0 rfl)

noncomputable def hp758398 := hp758393 (hp758395 (hp758397 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp758399 := @hp758372 32632207704399 67108864000 2548677 536870912000 hp758373 29888646973607787644161 18014398509481984000 42869635229579421419 hp737908 (@hp758375 1 hp758376 7729657705804969283021 3602879701896396800 3573167742810089 1452000000000000000000 (@hp758379 1452000000000000000000 hp758391 hp758398 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 849559 2000) rfl rfl)

noncomputable def hp758400 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 849559 2000) (Real.log Real.pi) 849559 2000 0 1 38410761 33554432

noncomputable def hp758401 := hp758399 (@hp758400 3 268435456 32632207704399 67108864000 2548677 536870912000 (Enclosure.Real.IsNear.const Bool.false 849559 2000) hd4909 rfl) rfl

noncomputable def hp758402 := @hp758362 hp737908 111343873439 67108864 485 67108864 (@hp758366 hp758360 hp758361 42869635229579421419 hp737908 (hp758368 rfl rfl rfl rfl rfl) (hp758371 (hp758401 rfl) (Enclosure.Real.IsNear.const Bool.true hp758364 hp758365) rfl rfl)) rfl

noncomputable def hp758403 := nat_lit 3792013115884603690713088

noncomputable def hp758404 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 111343873439) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp758403) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp758405 := BSN.sin_reduce_arg_pos_rat_q0 111343873439 67108864 226375608064910080 72057594037927936 264 hp758403 hp617687 rfl rfl rfl rfl

noncomputable def hp758406 := nat_lit 5054926792765795756068252884568230909455680980269708653602347973921952828349313350132653921

noncomputable def hp758407 := nat_lit 71108291175669425189861260147723481705929511549516687821634206155133482910734189158241

noncomputable def hp758408 := nat_lit 15164638161715035929354378931184397281403631081786026927431400653353548218082118582019645281

noncomputable def hp758409 := BSN.cos_dyadic_bound_f 53887747467 137438953472 3 2 67108864 21801270 hp758406 hp746621 hp758407 hp758408 hp746624

noncomputable def hp758410 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 53887747467) (BSN.cosEvenQ 137438953472) 0 2 hp758406 hp746621 hp758407 rfl rfl rfl

noncomputable def hp758411 := hp758409 hp758407 62016265 rfl rfl rfl rfl rfl rfl rfl rfl (hp758410 rfl)

noncomputable def hp758412 := @BSN.binarySplit_of_base2 (BSN.cosOddP 53887747467) (BSN.cosOddQ 137438953472) 0 2 hp758408 hp746624 hp758407 rfl rfl rfl

noncomputable def hp758413 := @BSN.cos_arg_round Bool.false 62016265 67108864 hp758403 hp617687 53887747467 137438953472 21801270 21780000 (hp758411 (hp758412 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758414 := hp758404 62016265 67108864 264 1000000000000000 21780000 10890000 hp758405 BSN.pi_near_15 hp758413 rfl rfl

noncomputable def hp758415 := @hp758359 485 67108864 Bool.false 62016265 67108864 1 10890000 hp758402 (Enclosure.sfrac_false_div 111343873439 67108864) (hp758414 rfl rfl) rfl

noncomputable def hp758416 := @hp758356 62016265 67108864 334297429 45675970560000 496130120 536870912 3930 536870912 (@hp758357 Bool.false 62016265 67108864 334297429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000)) (@hp758358 5348758864 730815528960000 62016265 67108864 334297429 45675970560000 (hp758415 rfl) rfl))

noncomputable def hp758417 := @hp758362 hp737908 890750987516 536870912 3870 536870912 (@hp758366 hp758360 hp758361 42869635229579421419 hp737908 (hp758368 rfl rfl rfl rfl rfl) (hp758371 (hp758401 rfl) (Enclosure.Real.IsNear.const Bool.true hp758364 hp758365) rfl rfl)) rfl

noncomputable def hp758418 := hp758355 (BSN.cos_quad_nat2 462 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533675774 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl rfl (hp758416 rfl) hp758417

noncomputable def hp758419 := nat_lit 2223464325699189913060380724361829019615227173244815255935005435584208225

noncomputable def hp758420 := nat_lit 78326219529168960870877980903003995258744389370081434039798838484321

noncomputable def hp758421 := nat_lit 5823232134380545403507206189930947330618985581867916967031806942696332641

noncomputable def hp758422 := BSN.sin_dyadic_bound_f 306717387 536870912 3 2 536870912 268435456 hp758419 hp708845 hp758420 hp758421 hp708848

noncomputable def hp758423 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 306717387) (BSN.sinEvenQ 536870912) 0 2 hp758419 hp708845 hp758420 rfl rfl rfl

noncomputable def hp758424 := hp758422 hp758420 290302647 rfl rfl rfl rfl rfl rfl rfl rfl (hp758423 rfl)

noncomputable def hp758425 := @BSN.binarySplit_of_base2 (BSN.sinOddP 306717387) (BSN.sinOddQ 536870912) 0 2 hp758421 hp708848 hp758420 rfl rfl rfl

noncomputable def hp758426 := nat_lit 11793465805340636324963330560000

noncomputable def hp758427 := BSN.cos_dyadic_bound_f 58601720 536870912 2 1 536870912 268435456 hp758426 hp708767 hp758426 hp758426 hp708768

noncomputable def hp758428 := @BSN.binarySplit_of_base (BSN.cosEvenP 58601720) (BSN.cosEvenQ 536870912) 0 1 hp758426 hp708767 hp758426 rfl rfl rfl

noncomputable def hp758429 := hp758427 hp758426 533675774 rfl rfl rfl rfl rfl rfl rfl rfl (hp758428 rfl)

noncomputable def hp758430 := @BSN.binarySplit_of_base (BSN.cosOddP 58601720) (BSN.cosOddQ 536870912) 0 1 hp758426 hp708768 hp758426 rfl rfl rfl

noncomputable def hp758431 := hp758418 hd4911 hd4913 hd4915 hd4917 hd4918 (hp758424 (hp758425 rfl) rfl rfl rfl rfl) (hp758429 (hp758430 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758432 := hp758351 (BSN.cos_quad_nat1 185 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 508327475 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl rfl (hp758431 rfl rfl rfl rfl rfl) hp758417

noncomputable def hp758433 := nat_lit 3679217059966621529962076445562315700086775337666829468598633681402618401

noncomputable def hp758434 := nat_lit 694655140070225906530790638682029048513788324982454104248598642713121

noncomputable def hp758435 := nat_lit 11036261869619724138073167755409583042163298436350523497587403846922428961

noncomputable def hp758436 := BSN.cos_dyadic_bound_f 402922163 536870912 3 2 536870912 268435456 hp758433 hp708868 hp758434 hp758435 hp708870

noncomputable def hp758437 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 402922163) (BSN.cosEvenQ 536870912) 0 2 hp758433 hp708868 hp758434 rfl rfl rfl

noncomputable def hp758438 := hp758436 hp758434 392639074 rfl rfl rfl rfl rfl rfl rfl rfl (hp758437 rfl)

noncomputable def hp758439 := @BSN.binarySplit_of_base2 (BSN.cosOddP 402922163) (BSN.cosOddQ 536870912) 0 2 hp758435 hp708870 hp758434 rfl rfl rfl

noncomputable def hp758440 := nat_lit 71139468285545281652282113629711237921847061080360068113530185083594757152573454903830308238392659483297102237696

noncomputable def hp758441 := nat_lit 7818592642498582110665222139456853114869094989838155218064991214991228133668406623376176909609037458640896

noncomputable def hp758442 := nat_lit 355523729199692402741835643170679796139048156871556412760719183298696144000992030547692828223553010684449894240256

noncomputable def hp758443 := BSN.sin_dyadic_bound_f 667463286 536870912 4 3 536870912 268435456 hp758440 hp642702 hp758441 hp758442 hp642705

noncomputable def hp758444 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 667463286) (BSN.sinEvenQ 536870912) 0 3 hp758440 hp642702 hp758441 rfl rfl rfl

noncomputable def hp758445 := hp758443 hp758441 508327475 rfl rfl rfl rfl rfl rfl rfl rfl (hp758444 rfl)

noncomputable def hp758446 := @BSN.binarySplit_of_base3 (BSN.sinOddP 667463286) (BSN.sinOddQ 536870912) 0 3 hp758442 hp642705 hp758441 rfl rfl rfl

noncomputable def hp758447 := hp758432 hd4920 hd4922 hd4924 hd4926 hd4918 (hp758438 (hp758439 rfl) rfl rfl rfl rfl) (hp758445 (hp758446 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758448 := hp758346 (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 513579986 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl rfl (hp758447 rfl rfl rfl rfl rfl) hp758417

noncomputable def hp758449 := nat_lit 574361506740305733692392034600625

noncomputable def hp758450 := BSN.sin_dyadic_bound_f 154809045 536870912 2 1 536870912 268435456 hp758449 hp708890 hp758449 hp758449 hp708891

noncomputable def hp758451 := @BSN.binarySplit_of_base (BSN.sinEvenP 154809045) (BSN.sinEvenQ 536870912) 0 1 hp758449 hp708890 hp758449 rfl rfl rfl

noncomputable def hp758452 := hp758450 hp758449 152672597 rfl rfl rfl rfl rfl rfl rfl rfl (hp758451 rfl)

noncomputable def hp758453 := @BSN.binarySplit_of_base (BSN.sinOddP 154809045) (BSN.sinOddQ 536870912) 0 1 hp758449 hp708891 hp758449 rfl rfl rfl

noncomputable def hp758454 := nat_lit 78736740083703185362804620189068793383718299319107860096234246432480297697645474691364565549367288652429006995456

noncomputable def hp758455 := nat_lit 10597886414563814470983248926438419695167365855741890497102858110335740899480611899812355888611810613395456

noncomputable def hp758456 := nat_lit 393471058389583144320669859401233210728064506265835908784333868770647055468668879735743233306050015177794929033216

noncomputable def hp758457 := BSN.sin_dyadic_bound_f 684596916 536870912 4 3 536870912 268435456 hp758454 hp642702 hp758455 hp758456 hp642705

noncomputable def hp758458 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 684596916) (BSN.sinEvenQ 536870912) 0 3 hp758454 hp642702 hp758455 rfl rfl rfl

noncomputable def hp758459 := hp758457 hp758455 513579986 rfl rfl rfl rfl rfl rfl rfl rfl (hp758458 rfl)

noncomputable def hp758460 := @BSN.binarySplit_of_base3 (BSN.sinOddP 684596916) (BSN.sinOddQ 536870912) 0 3 hp758456 hp642705 hp758455 rfl rfl rfl

noncomputable def hp758461 := hp758448 hd4928 hd4930 hd4932 hd4934 hd4918 (hp758452 (hp758453 rfl) rfl rfl rfl rfl) (hp758459 (hp758460 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758462 := hp758341 (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 528785586 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl rfl (hp758461 rfl rfl rfl rfl rfl) hp758417

noncomputable def hp758463 := nat_lit 1959144080534533787969611477389931480773284434391177968713507337136800000

noncomputable def hp758464 := nat_lit 197000736686665757714219179248715672571530402815776359776528100000000

noncomputable def hp758465 := nat_lit 5877038240130228032393405993811297010974710242367902353420968955210400000

noncomputable def hp758466 := BSN.cos_dyadic_bound_f 344198110 536870912 3 2 536870912 268435456 hp758463 hp708868 hp758464 hp758465 hp708870

noncomputable def hp758467 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 344198110) (BSN.cosEvenQ 536870912) 0 2 hp758463 hp708868 hp758464 rfl rfl rfl

noncomputable def hp758468 := hp758466 hp758464 430262860 rfl rfl rfl rfl rfl rfl rfl rfl (hp758467 rfl)

noncomputable def hp758469 := @BSN.binarySplit_of_base2 (BSN.cosOddP 344198110) (BSN.cosOddQ 536870912) 0 2 hp758465 hp708870 hp758464 rfl rfl rfl

noncomputable def hp758470 := nat_lit 75749702050281576232707434211856

noncomputable def hp758471 := BSN.cos_dyadic_bound_f 93292178 536870912 2 1 536870912 268435456 hp758470 hp708767 hp758470 hp758470 hp708768

noncomputable def hp758472 := @BSN.binarySplit_of_base (BSN.cosEvenP 93292178) (BSN.cosEvenQ 536870912) 0 1 hp758470 hp708767 hp758470 rfl rfl rfl

noncomputable def hp758473 := hp758471 hp758470 528785586 rfl rfl rfl rfl rfl rfl rfl rfl (hp758472 rfl)

noncomputable def hp758474 := @BSN.binarySplit_of_base (BSN.cosOddP 93292178) (BSN.cosOddQ 536870912) 0 1 hp758470 hp708768 hp758470 rfl rfl rfl

noncomputable def hp758475 := hp758462 hd4936 hd4938 hd4940 hd4942 hd4918 (hp758468 (hp758469 rfl) rfl rfl rfl rfl) (hp758473 (hp758474 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758476 := hp758336 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 285821273 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl rfl (hp758475 rfl rfl rfl rfl rfl) hp758417

noncomputable def hp758477 := nat_lit 40262014539278520138840060312561

noncomputable def hp758478 := BSN.sin_dyadic_bound_f 79656987 536870912 2 1 536870912 268435456 hp758477 hp708890 hp758477 hp758477 hp708891

noncomputable def hp758479 := @BSN.binarySplit_of_base (BSN.sinEvenP 79656987) (BSN.sinEvenQ 536870912) 0 1 hp758477 hp708890 hp758477 rfl rfl rfl

noncomputable def hp758480 := hp758478 hp758477 79365040 rfl rfl rfl rfl rfl rfl rfl rfl (hp758479 rfl)

noncomputable def hp758481 := @BSN.binarySplit_of_base (BSN.sinOddP 79656987) (BSN.sinOddQ 536870912) 0 1 hp758477 hp708891 hp758477 rfl rfl rfl

noncomputable def hp758482 := nat_lit 11886539652319811379354207583033532636617421738885743390083829542687722809805406334029767700413224443607342276561

noncomputable def hp758483 := nat_lit 641368042032939651666906109446482877176411586761505505761416474554106680121247160660645200946019597180881

noncomputable def hp758484 := nat_lit 72081984093875542956609454327451543781958559092649882858080833110105088797506350870981084639112969818249320619985

noncomputable def hp758485 := BSN.cos_dyadic_bound_f 541908059 536870912 4 3 536870912 268435456 hp758482 hp716712 hp758483 hp758484 hp716714

noncomputable def hp758486 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 541908059) (BSN.cosEvenQ 536870912) 0 3 hp758482 hp716712 hp758483 rfl rfl rfl

noncomputable def hp758487 := hp758485 hp758483 285821273 rfl rfl rfl rfl rfl rfl rfl rfl (hp758486 rfl)

noncomputable def hp758488 := @BSN.binarySplit_of_base3 (BSN.cosOddP 541908059) (BSN.cosOddQ 536870912) 0 3 hp758484 hp716714 hp758483 rfl rfl rfl

noncomputable def hp758489 := hp758476 hd4944 hd4946 hd4961 hd4963 hd4918 (hp758480 (hp758481 rfl) rfl rfl rfl rfl) (hp758487 (hp758488 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758490 := @hp758331 103073 134217728 (hp758489 rfl rfl rfl rfl rfl) (hp758489 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp758491 := @hp758329 Bool.false 204993797 268435456 103073 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 849559 1000)) (Enclosure.sfrac Bool.false 849559 1000) 11) hp758490

noncomputable def hp758492 := @Enclosure.Real.IsNear.mulLit_tf hp758320 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1))) 9840031 33554432 1

noncomputable def hp758493 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp758319 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp758494 := @hp758493 1 1 0 1 9840031 33554432 1 33554432 9840031 33554432 1

noncomputable def hp758495 := @Enclosure.Real.IsNear.of_eq (hp758319 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp758496 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 849559 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758497 := @hp758495 (@Inv.inv Real Real.instInv (Real.sqrt hp758321)) Bool.false 9840031 33554432 1 33554432 (hp758496 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 849559 1000) 849559 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000))))

noncomputable def hp758498 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp758321)) Bool.false 19680062 67108864 2 67108864 9840031 33554432

noncomputable def hp758499 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp758321) Bool.false 228840718 67108864 6 67108864 114420359 33554432 3 33554432

noncomputable def hp758500 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 849559 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758501 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 849559 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758502 := @hp758501 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 849559 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9073890758213

noncomputable def hp758503 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 849559 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 849559 1000 0

noncomputable def hp758504 := @hp758503 1 10680707 67108864 1 67108864 9073890758213 67108864000 849559 67108864000 (Enclosure.Real.IsNear.const Bool.false 849559 1000) hd4949

noncomputable def hp758505 := @hp758502 67108864000 849559 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 849559 1000) 849559 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000))) (hp758504 rfl)

noncomputable def hp758506 := @hp758500 9073890758213 67108864000 849559 67108864000 390172539 390172577 33554432 hp758505 rfl rfl rfl

noncomputable def hp758507 := @Enclosure.Real.IsNear.recentre' hp758321 Bool.false 780345116 67108864 38 67108864 195086279 16777216 19 33554432 (hp758506 rfl rfl rfl)

noncomputable def hp758508 := @Enclosure.Real.IsNear.sqrt_image hp758321 195086279 16777216 19 33554432 114420356 114420362 33554432 (hp758507 rfl) rfl rfl

noncomputable def hp758509 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp758321) 114420359 33554432 3 33554432 9840030 9840032 33554432 (hp758499 (hp758508 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp758510 := @hp758494 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp758497 (@hp758498 1 33554432 (hp758509 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp758511 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758512 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp758513 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1))) (hp758511 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758512 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp758514 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 849559 1000) 849559 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl

noncomputable def hp758515 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758516 := @hp758515 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758512 (Enclosure.sfrac Bool.false 1 16)))) 96777523

noncomputable def hp758517 := @hp758516 67108864 513 67108864 9584597 33554432 92932951 11418992640000 927573556613231 2251799813685248 21334300833821597 1532631248189521920000

noncomputable def hp758518 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758519 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758520 := @hp758518 (@Neg.neg Real Real.instNeg hp758519) Bool.true 96777523 67108864 513 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758521 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758522 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp758523 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp758524 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 33102657) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false

noncomputable def hp758525 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1))) Bool.false 9317569624007715690165

noncomputable def hp758526 := nat_lit 20509417318114379151708301

noncomputable def hp758527 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp758528 := @Enclosure.Real.IsNear.subLit_ff_p hp758321 (Enclosure.sfrac Bool.false 11 1) 195086279 16777216 19 33554432 11 1 0

noncomputable def hp758529 := @hp758527 500000000000000 10536903 16777216 19 33554432 9317569624007715690165 2361183241434822606848 hp758526 hp684593 hd4948 (@hp758528 1 10536903 10536903 16777216 19 33554432 (hp758507 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758530 := @hp758524 33102657 8388608 15 4194304 Bool.true 46535595 67108864 1 10890000 (@hp758525 2361183241434822606848 hp758526 hp684593 33102657 8388608 15 4194304 (hp758529 rfl) rfl) (Enclosure.sfrac_false_div 33102657 8388608)

noncomputable def hp758531 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 33102657) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 972643165729208479514624) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp758532 := BSN.sin_reduce_arg_pos_rat_q2 33102657 8388608 226375608064910080 72057594037927936 0 972643165729208479514624 hp630689 rfl rfl rfl rfl

noncomputable def hp758533 := nat_lit 89642063688169051565491762262485453441533680067642643387344461753909035791889106113089610881

noncomputable def hp758534 := nat_lit 22351661315257744958363158270287012494510216196239568225237999986717144525039355955356801

noncomputable def hp758535 := nat_lit 268881487741876639206558560470915786299612019770535451025582909261753673086617239627358119041

noncomputable def hp758536 := BSN.cos_dyadic_bound_f 110576725743 137438953472 3 2 67108864 21801270 hp758533 hp746621 hp758534 hp758535 hp746624

noncomputable def hp758537 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 110576725743) (BSN.cosEvenQ 137438953472) 0 2 hp758533 hp746621 hp758534 rfl rfl rfl

noncomputable def hp758538 := hp758536 hp758534 46535595 rfl rfl rfl rfl rfl rfl rfl rfl (hp758537 rfl)

noncomputable def hp758539 := @BSN.binarySplit_of_base2 (BSN.cosOddP 110576725743) (BSN.cosOddQ 137438953472) 0 2 hp758535 hp746624 hp758534 rfl rfl rfl

noncomputable def hp758540 := @BSN.cos_arg_round Bool.false 46535595 67108864 972643165729208479514624 hp630689 110576725743 137438953472 21801270 21780000 (hp758538 (hp758539 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758541 := hp758531 46535595 67108864 0 1000000000000000 21780000 10890000 hp758532 BSN.pi_near_15 hp758540 rfl rfl

noncomputable def hp758542 := @hp758522 46535595 67108864 10471519 2854748160000 (@hp758523 46535595 67108864 167544304 45675970560000 46535595 67108864 10471519 2854748160000 (hp758530 (hp758541 rfl rfl) rfl rfl) rfl)

noncomputable def hp758543 := @hp758521 46535595 67108864 10471519 2854748160000 48388505 48389018 33554432 hp758542 rfl rfl rfl

noncomputable def hp758544 := @Enclosure.Real.IsNear.recentre' hp758519 Bool.false 96777523 67108864 513 67108864 96777523 67108864 513 67108864 (hp758543 rfl rfl rfl)

noncomputable def hp758545 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758512 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp758546 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758512 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 124854289)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp758547 := nat_lit 73700964185114902542132520525

noncomputable def hp758548 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758512 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp758547

noncomputable def hp758549 := nat_lit 38815130036889597344586950993629739

noncomputable def hp758550 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758512 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp758551 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp758552 := @hp758551 (Enclosure.sfrac Bool.false 1 16) 65753572770639 281474976710656 1438339197 1125899906842624 1 16 0

noncomputable def hp758553 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)) 111026324831409

noncomputable def hp758554 := @hp758553 281474976710656 800804989 1125899906842624 10536903 16777216 19 33554432 1103161893144728961024 65753572770639 281474976710656 1438339197

noncomputable def hp758555 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)) 10536903 16777216 19

noncomputable def hp758556 := @hp758555 33554432 10536903 16777216 19 33554432 111026324831409 281474976710656 800804989 1125899906842624 (@hp758528 1 10536903 10536903 16777216 19 33554432 (hp758507 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758557 := hp758556 (@hp758528 1 10536903 10536903 16777216 19 33554432 (hp758507 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758558 := @hp758554 1125899906842624 (hp758557 rfl) (@hp758528 1 10536903 10536903 16777216 19 33554432 (hp758507 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758559 := @hp758550 500000000000000 83345758815055 281474976710656 1438339197 1125899906842624 hp758547 hp631146 hp758549 hp682143 hd4948 (@hp758552 1 1333532141040880 83345758815055 281474976710656 1438339197 1125899906842624 (hp758558 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp758560 := @hp758546 124854289 67108864 135 16777216 Bool.true 9584597 33554432 1 10890000 (@hp758548 hp631146 hp758549 hp682143 124854289 67108864 135 16777216 (hp758559 rfl) rfl) (Enclosure.sfrac_true_div 124854289 67108864)

noncomputable def hp758561 := nat_lit 2009407385792463743092354198466331425627329317326780459465041708991210298498851175265121264488814904001

noncomputable def hp758562 := nat_lit 14349659309965987625518022598503702950642669834115927868353958819557184405005911566714615628989121

noncomputable def hp758563 := nat_lit 12132785115124776954463452928588747041037639094655895710996826072101796101341823150466743082962455265985

noncomputable def hp758564 := BSN.cos_dyadic_bound_t 124854289 67108864 4 3 33554432 10890000 hp758561 hp745658 hp758562 hp758563 hp745661

noncomputable def hp758565 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 124854289) (BSN.cosEvenQ 67108864) 0 3 hp758561 hp745658 hp758562 rfl rfl rfl

noncomputable def hp758566 := hp758564 hp758562 9584597 rfl rfl rfl rfl rfl rfl rfl rfl (hp758565 rfl)

noncomputable def hp758567 := @BSN.binarySplit_of_base3 (BSN.cosOddP 124854289) (BSN.cosOddQ 67108864) 0 3 hp758563 hp745661 hp758562 rfl rfl rfl

noncomputable def hp758568 := hp758560 (BSN.cos_neg_of_bound 124854289 67108864 Bool.true 9584597 33554432 1 10890000 (hp758566 (hp758567 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp758569 := hp758517 (hp758520 (@Enclosure.Real.IsNear.neg hp758519 Bool.false 96777523 67108864 513 67108864 (hp758544 rfl))) (@hp758545 9584597 33554432 1486927216 182703882240000 9584597 33554432 92932951 11418992640000 (hp758568 rfl) rfl)

noncomputable def hp758570 := @hp758492 33554432 927573556613231 2251799813685248 21334300833821597 1532631248189521920000 9127352551854448050161 75557863725914323419136 210561532654401077120479 hp738860 (hp758510 rfl) (@hp758513 Bool.false 927573556613231 2251799813685248 21334300833821597 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758321 (Enclosure.sfrac Bool.false 11 1)) (hp758514 rfl (hp758324 rfl rfl))) (hp758569 rfl))

noncomputable def hp758571 := @hp758318 hp758316 hp738860 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 849559 1000))) (@hp758323 hp758316 hp738860 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 849559 1000) 11 (hp758324 rfl rfl)) (@hp758327 hp758316 hp738860 hp758491 (hp758570 rfl) rfl rfl))

theorem hd5043 : hp758317 hp738860 := hp758571

noncomputable def hp758572 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 850199 1000)) Bool.true 14915937657103259141907 18889465931478580854784 60205498711294375500991

noncomputable def hp758573 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 850199 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 850199 1000)) Bool.true 14915937657103259141907 18889465931478580854784

noncomputable def hp758574 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 850199 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758575 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp758574 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp758576 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 850199 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758577 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp758575 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp758578 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 850199 1000)) hp758577 Bool.true 14915937657103259141907 18889465931478580854784

noncomputable def hp758579 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 850199 1000) 850199 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl

noncomputable def hp758580 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp758575 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp758581 := nat_lit 4003966526652085006843974254592

noncomputable def hp758582 := @hp758580 244552383 268435456 6447 8388608 2292906420261847431405 18889465931478580854784 321415941125600844991 hp746784 hp758581 14915937657103259141907 18889465931478580854784

noncomputable def hp758583 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) 11)

noncomputable def hp758584 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) 11) hp758583

noncomputable def hp758585 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) 11)

noncomputable def hp758586 := @hp758585 244552383 536870912 206304 536870912 244552383 536870912 206304 536870912 262586121785966592 244552383 268435456

noncomputable def hp758587 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp758588 := hp758587 BSN.quadSignPos 9 10 11 850199 1000 189 240 536870912 268435456 9007199254740992

noncomputable def hp758589 := hp758588 Bool.false 891594041099 3874 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp758590 := hp758589 Bool.true 326784462 177106 Bool.true 27765616 Bool.true 522765016 28296951008113761 1 Bool.false 27753240

noncomputable def hp758591 := hp758590 Bool.true Bool.false 301840810 Bool.false Bool.true 244552383 206304 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 27753240 536870912) BSN.abs_quadSignPos

noncomputable def hp758592 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp758593 := hp758592 BSN.quadSignPos 7 8 9 850199 1000 68 132 536870912 268435456 9007199254740992

noncomputable def hp758594 := hp758593 Bool.false 891594041099 3874 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp758595 := hp758594 Bool.true 680439622 144642 Bool.true 215635200 Bool.true 5199202 28296951008113761 1 Bool.false 494144831

noncomputable def hp758596 := hp758595 Bool.false Bool.false 536845736 Bool.false Bool.true 326784462 177106 BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 494144831 536870912) BSN.abs_quadSignPos

noncomputable def hp758597 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp758598 := hp758597 BSN.quadSignPos 5 6 7 850199 1000 87 4 536870912 268435456 9007199254740992

noncomputable def hp758599 := hp758598 Bool.false 891594041099 3874 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp758600 := hp758599 Bool.true 1026459285 107486 Bool.false 382218767 Bool.false 15726017 28296951008113761 1 Bool.false 350738947

noncomputable def hp758601 := hp758600 Bool.false Bool.false 536640605 Bool.false Bool.true 680439622 144642 BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 350738947 536870912) BSN.abs_quadSignPos

noncomputable def hp758602 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp758603 := hp758602 BSN.quadSignNeg 3 4 5 850199 1000 306 186 536870912 268435456 9007199254740992

noncomputable def hp758604 := hp758603 Bool.false 891594041099 3874 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp758605 := hp758604 Bool.true 755057385 63530 Bool.false 769648640 Bool.false 114203367 28296951008113761 1 Bool.false 73435273

noncomputable def hp758606 := hp758605 Bool.true Bool.false 524769956 Bool.true Bool.true 1026459285 107486 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 306 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 73435273 536870912) BSN.abs_quadSignNeg

noncomputable def hp758607 := hp758602 BSN.quadSignNeg 1 2 3 850199 1000 682 462 536870912 268435456 9007199254740992

noncomputable def hp758608 := hp758607 Bool.false 891594041099 3874 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp758609 := hp758608 Bool.true 204905488 3930 Bool.false 68292565 Bool.false 524174998 28296951008113761 1 Bool.false 532533194

noncomputable def hp758610 := hp758609 Bool.true Bool.false 300673734 Bool.true Bool.true 755057385 63530 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 682 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 532533194 536870912) BSN.abs_quadSignNeg

noncomputable def hp758611 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) 1) Bool.true

noncomputable def hp758612 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)))

noncomputable def hp758613 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000))) Bool.true 25613186 67108864

noncomputable def hp758614 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 111449255137) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 111449255137 67108864

noncomputable def hp758615 := nat_lit 101691241109635929007383802172668903946461179918217724589929

noncomputable def hp758616 := nat_lit 61233102555987860290826108647643331709487426259910656000

noncomputable def hp758617 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) Bool.false hp758615 hp758616 128705482331018982977

noncomputable def hp758618 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 850199 4000) (Real.log (Enclosure.sfrac Bool.false 2891354358404 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1700398))))))

noncomputable def hp758619 := nat_lit 213228163773301394198670344479520000

noncomputable def hp758620 := nat_lit 1087718405230259937802836643208396546880

noncomputable def hp758621 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp758618 (Enclosure.sfrac Bool.false 850199 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 850199 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp758619 hp758620)) Bool.false

noncomputable def hp758622 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 850199 1000) 850199 1000 2891354358404 16000000 1700398

noncomputable def hp758623 := hp758622 4000 2000 hp758619 hp758620 (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl rfl rfl rfl

noncomputable def hp758624 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp758618 (Enclosure.sfrac Bool.false 850199 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 850199 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp758619 hp758620) 29916935155079904446081 18014398509481984000

noncomputable def hp758625 := nat_lit 32541197155083497282362816695254049262867577573829671868777280

noncomputable def hp758626 := @hp758624 128705482331018982977 hp738659 hp758619 hp758620 0 1 hp758625 hp758615 hp758616 128705482331018982977 hp738659

noncomputable def hp758627 := @Enclosure.Real.IsNear.subLit_ff_p (hp758618 (Enclosure.sfrac Bool.false 850199 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 850199 2000) (Real.log Real.pi)) 7736635125797868421453 3602879701896396800 10727503240278587 4356000000000000000000

noncomputable def hp758628 := nat_lit 401538306523815243321009032396800

noncomputable def hp758629 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 850199 4000) (Real.log (Enclosure.sfrac Bool.false 2891354358404 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1700398))))))

noncomputable def hp758630 := @hp758629 (Enclosure.sfrac Bool.false 850199 2000) 46341087428170878764673 18014398509481984000 10727503240278587 4356000000000000000000 850199 2000 0

noncomputable def hp758631 := nat_lit 77366351257978684214530000

noncomputable def hp758632 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 850199 4000) (Real.log (Enclosure.sfrac Bool.false 2891354358404 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1700398))))) 46348159017404480580673

noncomputable def hp758633 := nat_lit 104350852036726973212315570737883643904

noncomputable def hp758634 := @hp758632 18014398509481984000 10627503239734087 4356000000000000000000 883948654200227 2251799813685248 200000001089 8712000000000000000 hp758633 46341087428170878764673 18014398509481984000 10727503240278587

noncomputable def hp758635 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 850199 4000) (Real.log (Enclosure.sfrac Bool.false 2891354358404 16000000)) 850199 4000 0 1 54514483100314727 4503599627370496

noncomputable def hp758636 := nat_lit 117068961037098219886084096

noncomputable def hp758637 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2891354358404) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp758636 hp617687

noncomputable def hp758638 := BSN.log_rat_reduce_isNear 2891354358404 16000000 17 5782708716808 4194304000000 86206649 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp758639 := nat_lit 99204139591770116603675194068969684702742789091129459003959497896024143485453230885890096986352333007021395325149111053640421867520

noncomputable def hp758640 := nat_lit 851147842097063594219054104943660231365823152141638170998114624726709665888132805524299221266306526318422482792162228849217634304

noncomputable def hp758641 := nat_lit 94350353636393973501476848888947985579145369857963881114079333454729240433044830132491638267962570134427043601549565624320

noncomputable def hp758642 := BSN.log_dyadic_bound 794202358404 4988506358404 6 5 hp758639 268435456 87120000 hp758640 hp758641 86206649 5782708716808

noncomputable def hp758643 := hp758642 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp758644 := @BSN.binarySplit_of_base5 (BSN.artanhP 794202358404) (BSN.artanhQ 4988506358404) 0 5 hp758640 hp758639 hp758641 rfl rfl rfl

noncomputable def hp758645 := hp758638 rfl rfl rfl rfl (hp758643 (hp758644 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp758646 := @hp758635 12500018513 1089000000000000000 46348159017404480580673 18014398509481984000 10627503239734087 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 850199 4000) (BSN.isNear_log_sfrac 2891354358404 16000000 54514483100314727 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp758637 1000001481040000 87120000000000000000000 54514483100314727 4503599627370496 12500018513 1089000000000000000 (hp758645 rfl rfl rfl) rfl)) rfl

noncomputable def hp758647 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1700398)))) 1 4

noncomputable def hp758648 := @hp758647 0 1 883948654200227 562949953421312 200000001089 2178000000000000000 883948654200227 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp758649 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1700398))) 884279719003555 562949953421312 1

noncomputable def hp758650 := @hp758649 2000000000000000 19733 33554432 1 10890000 29660395008853031256064 883948654200227 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp758651 := BSN.arctan_dyadic_bound_f 1000 1700398 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp758652 := hp758651 1 19733 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1700398) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1700398) 0 0 rfl)

noncomputable def hp758653 := hp758648 (hp758650 (hp758652 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp758654 := @hp758627 32656790591439 67108864000 2550597 536870912000 hp758628 29916935155079904446081 18014398509481984000 128705482331018982977 hp738659 (@hp758630 1 hp758631 7736635125797868421453 3602879701896396800 10727503240278587 4356000000000000000000 (@hp758634 4356000000000000000000 hp758646 hp758653 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 850199 2000) rfl rfl)

noncomputable def hp758655 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 850199 2000) (Real.log Real.pi) 850199 2000 0 1 38410761 33554432

noncomputable def hp758656 := hp758654 (@hp758655 3 268435456 32656790591439 67108864000 2550597 536870912000 (Enclosure.Real.IsNear.const Bool.false 850199 2000) hd4909 rfl) rfl

noncomputable def hp758657 := @hp758617 hp738659 111449255137 67108864 485 67108864 (@hp758621 hp758615 hp758616 128705482331018982977 hp738659 (hp758623 rfl rfl rfl rfl rfl) (hp758626 (hp758656 rfl) (Enclosure.Real.IsNear.const Bool.true hp758619 hp758620) rfl rfl)) rfl

noncomputable def hp758658 := nat_lit 3787306448362294554394624

noncomputable def hp758659 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 111449255137) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp758658) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp758660 := BSN.sin_reduce_arg_pos_rat_q1 111449255137 67108864 226375608064910080 72057594037927936 264 hp758658 hp617687 rfl rfl rfl rfl

noncomputable def hp758661 := nat_lit 8390784881536585960680390413958355525893201

noncomputable def hp758662 := BSN.sin_dyadic_bound_f 53820861699 137438953472 2 1 67108864 21801270 hp758661 hp749778 hp758661 hp758661 hp749779

noncomputable def hp758663 := @BSN.binarySplit_of_base (BSN.sinEvenP 53820861699) (BSN.sinEvenQ 137438953472) 0 1 hp758661 hp749778 hp758661 rfl rfl rfl

noncomputable def hp758664 := hp758662 hp758661 25613186 rfl rfl rfl rfl rfl rfl rfl rfl (hp758663 rfl)

noncomputable def hp758665 := @BSN.binarySplit_of_base (BSN.sinOddP 53820861699) (BSN.sinOddQ 137438953472) 0 1 hp758661 hp749779 hp758661 rfl rfl rfl

noncomputable def hp758666 := @BSN.sin_arg_round Bool.false 25613186 67108864 hp758658 hp617687 53820861699 137438953472 21801270 21780000 (hp758664 (hp758665 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758667 := hp758659 25613186 67108864 264 1000000000000000 21780000 10890000 hp758660 BSN.pi_near_15 hp758666 rfl rfl

noncomputable def hp758668 := @hp758614 485 67108864 Bool.true 25613186 67108864 1 10890000 hp758657 (Enclosure.sfrac_false_div 111449255137 67108864) (hp758667 rfl rfl) rfl

noncomputable def hp758669 := @hp758611 12806593 33554432 334297429 45675970560000 204905488 536870912 3930 536870912 (@hp758612 Bool.true 12806593 33554432 334297429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000)) (@hp758613 5348758864 730815528960000 12806593 33554432 334297429 45675970560000 (hp758668 rfl) rfl))

noncomputable def hp758670 := @hp758617 hp738659 891594041099 536870912 3874 536870912 (@hp758621 hp758615 hp758616 128705482331018982977 hp738659 (hp758623 rfl rfl rfl rfl rfl) (hp758626 (hp758656 rfl) (Enclosure.Real.IsNear.const Bool.true hp758619 hp758620) rfl rfl)) rfl

noncomputable def hp758671 := hp758610 (BSN.cos_quad_nat2 462 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 300673734 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl rfl (hp758669 rfl) hp758670

noncomputable def hp758672 := nat_lit 21751724738723361033745266600625

noncomputable def hp758673 := BSN.cos_dyadic_bound_f 68292565 536870912 2 1 536870912 268435456 hp758672 hp708767 hp758672 hp758672 hp708768

noncomputable def hp758674 := @BSN.binarySplit_of_base (BSN.cosEvenP 68292565) (BSN.cosEvenQ 536870912) 0 1 hp758672 hp708767 hp758672 rfl rfl rfl

noncomputable def hp758675 := hp758673 hp758672 532533194 rfl rfl rfl rfl rfl rfl rfl rfl (hp758674 rfl)

noncomputable def hp758676 := @BSN.binarySplit_of_base (BSN.cosOddP 68292565) (BSN.cosOddQ 536870912) 0 1 hp758672 hp708768 hp758672 rfl rfl rfl

noncomputable def hp758677 := nat_lit 10404585641489681182607563262018112033606125856136421246112626979235512814642835420444464922826566228372704792576

noncomputable def hp758678 := nat_lit 430244796448726699415698792025790717599609544658588675132950006736195292109139586262998461346477875204096

noncomputable def hp758679 := nat_lit 63098401558903434847518000330179543138589683442688321382360252847655992640864260053727000987721466838264887971840

noncomputable def hp758680 := BSN.cos_dyadic_bound_f 524174998 536870912 4 3 536870912 268435456 hp758677 hp716712 hp758678 hp758679 hp716714

noncomputable def hp758681 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 524174998) (BSN.cosEvenQ 536870912) 0 3 hp758677 hp716712 hp758678 rfl rfl rfl

noncomputable def hp758682 := hp758680 hp758678 300673734 rfl rfl rfl rfl rfl rfl rfl rfl (hp758681 rfl)

noncomputable def hp758683 := @BSN.binarySplit_of_base3 (BSN.cosOddP 524174998) (BSN.cosOddQ 536870912) 0 3 hp758679 hp716714 hp758678 rfl rfl rfl

noncomputable def hp758684 := hp758671 hd4911 hd4913 hd4915 hd4917 hd4918 (hp758675 (hp758676 rfl) rfl rfl rfl rfl) (hp758682 (hp758683 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758685 := hp758606 (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 524769956 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl rfl (hp758684 rfl rfl rfl rfl rfl) hp758670

noncomputable def hp758686 := nat_lit 48455782924454576351249429610435314533025244822669752800712278972030426027758728696210012853923312853581824000000

noncomputable def hp758687 := nat_lit 43202619042975286676347104179226991160499395806092314516076872776035689275303177046706771460096000000000000

noncomputable def hp758688 := nat_lit 293473396615709520460343818791106255460299621864210458344095624073159559881282705974599622830575906975226265600000

noncomputable def hp758689 := BSN.cos_dyadic_bound_f 769648640 536870912 4 3 536870912 268435456 hp758686 hp716712 hp758687 hp758688 hp716714

noncomputable def hp758690 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 769648640) (BSN.cosEvenQ 536870912) 0 3 hp758686 hp716712 hp758687 rfl rfl rfl

noncomputable def hp758691 := hp758689 hp758687 73435273 rfl rfl rfl rfl rfl rfl rfl rfl (hp758690 rfl)

noncomputable def hp758692 := @BSN.binarySplit_of_base3 (BSN.cosOddP 769648640) (BSN.cosOddQ 536870912) 0 3 hp758688 hp716714 hp758687 rfl rfl rfl

noncomputable def hp758693 := nat_lit 170104433413730320852915535882721

noncomputable def hp758694 := BSN.cos_dyadic_bound_f 114203367 536870912 2 1 536870912 268435456 hp758693 hp708767 hp758693 hp758693 hp708768

noncomputable def hp758695 := @BSN.binarySplit_of_base (BSN.cosEvenP 114203367) (BSN.cosEvenQ 536870912) 0 1 hp758693 hp708767 hp758693 rfl rfl rfl

noncomputable def hp758696 := hp758694 hp758693 524769956 rfl rfl rfl rfl rfl rfl rfl rfl (hp758695 rfl)

noncomputable def hp758697 := @BSN.binarySplit_of_base (BSN.cosOddP 114203367) (BSN.cosOddQ 536870912) 0 1 hp758693 hp708768 hp758693 rfl rfl rfl

noncomputable def hp758698 := hp758685 hd4920 hd4922 hd4924 hd4926 hd4918 (hp758691 (hp758692 rfl) rfl rfl rfl rfl) (hp758696 (hp758697 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758699 := hp758601 (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536640605 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl rfl (hp758698 rfl rfl rfl rfl rfl) hp758670

noncomputable def hp758700 := nat_lit 5362239484844947203067513165027692297550457320343714446992660350385523585

noncomputable def hp758701 := nat_lit 455508050908584223562433367479997898149323475700275757229150747757441

noncomputable def hp758702 := nat_lit 14043223066321009728814861968668036020797051220034785009945263245037144961

noncomputable def hp758703 := BSN.sin_dyadic_bound_f 382218767 536870912 3 2 536870912 268435456 hp758700 hp708845 hp758701 hp758702 hp708848

noncomputable def hp758704 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 382218767) (BSN.sinEvenQ 536870912) 0 2 hp758700 hp708845 hp758701 rfl rfl rfl

noncomputable def hp758705 := hp758703 hp758701 350738947 rfl rfl rfl rfl rfl rfl rfl rfl (hp758704 rfl)

noncomputable def hp758706 := @BSN.binarySplit_of_base2 (BSN.sinOddP 382218767) (BSN.sinOddQ 536870912) 0 2 hp758702 hp708848 hp758701 rfl rfl rfl

noncomputable def hp758707 := nat_lit 61161054302371854746831435521

noncomputable def hp758708 := BSN.cos_dyadic_bound_f 15726017 536870912 2 1 536870912 268435456 hp758707 hp708767 hp758707 hp758707 hp708768

noncomputable def hp758709 := @BSN.binarySplit_of_base (BSN.cosEvenP 15726017) (BSN.cosEvenQ 536870912) 0 1 hp758707 hp708767 hp758707 rfl rfl rfl

noncomputable def hp758710 := hp758708 hp758707 536640605 rfl rfl rfl rfl rfl rfl rfl rfl (hp758709 rfl)

noncomputable def hp758711 := @BSN.binarySplit_of_base (BSN.cosOddP 15726017) (BSN.cosOddQ 536870912) 0 1 hp758707 hp708768 hp758707 rfl rfl rfl

noncomputable def hp758712 := hp758699 hd4928 hd4930 hd4932 hd4934 hd4918 (hp758705 (hp758706 rfl) rfl rfl rfl rfl) (hp758710 (hp758711 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758713 := hp758596 (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536845736 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl rfl (hp758712 rfl rfl rfl rfl rfl) hp758670

noncomputable def hp758714 := nat_lit 301768657160812915179713890289595537461424508364697272863162368000000000

noncomputable def hp758715 := nat_lit 4674737700044560618100464617472248209047263180226560000000000000000

noncomputable def hp758716 := nat_lit 905296622007038656417905469939551667887855430567731365469487104000000000

noncomputable def hp758717 := BSN.cos_dyadic_bound_f 215635200 536870912 3 2 536870912 268435456 hp758714 hp708868 hp758715 hp758716 hp708870

noncomputable def hp758718 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 215635200) (BSN.cosEvenQ 536870912) 0 2 hp758714 hp708868 hp758715 rfl rfl rfl

noncomputable def hp758719 := hp758717 hp758715 494144831 rfl rfl rfl rfl rfl rfl rfl rfl (hp758718 rfl)

noncomputable def hp758720 := @BSN.binarySplit_of_base2 (BSN.cosOddP 215635200) (BSN.cosOddQ 536870912) 0 2 hp758716 hp708870 hp758715 rfl rfl rfl

noncomputable def hp758721 := BSN.cos_dyadic_bound_f 5199202 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp758722 := hp758721 1 536845736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5199202) (BSN.cosEvenQ 536870912) 0 0 rfl)

noncomputable def hp758723 := hp758722 (@BSN.binarySplit_of_le (BSN.cosOddP 5199202) (BSN.cosOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp758724 := hp758713 hd4936 hd4938 hd4940 hd4942 hd4918 (hp758719 (hp758720 rfl) rfl rfl rfl rfl) hp758723 rfl

noncomputable def hp758725 := hp758591 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 301840810 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl rfl (hp758724 rfl rfl rfl rfl rfl) hp758670

noncomputable def hp758726 := nat_lit 594332188907143611837736615936

noncomputable def hp758727 := BSN.sin_dyadic_bound_f 27765616 536870912 2 1 536870912 268435456 hp758726 hp708890 hp758726 hp758726 hp708891

noncomputable def hp758728 := @BSN.binarySplit_of_base (BSN.sinEvenP 27765616) (BSN.sinEvenQ 536870912) 0 1 hp758726 hp708890 hp758726 rfl rfl rfl

noncomputable def hp758729 := hp758727 hp758726 27753240 rfl rfl rfl rfl rfl rfl rfl rfl (hp758728 rfl)

noncomputable def hp758730 := @BSN.binarySplit_of_base (BSN.sinOddP 27765616) (BSN.sinOddQ 536870912) 0 1 hp758726 hp708891 hp758726 rfl rfl rfl

noncomputable def hp758731 := nat_lit 10293027421198982653498242048368107382209008006081648282117330166137442803122569830500034372351727378464124174336

noncomputable def hp758732 := nat_lit 416560606604157308862372865186410358051543061087741430655272053680098064931961300258704347349978139590656

noncomputable def hp758733 := nat_lit 62422100052459067157377381202214071341322629849279047064806177569043738087767825869029466046712307074415628124160

noncomputable def hp758734 := BSN.cos_dyadic_bound_f 522765016 536870912 4 3 536870912 268435456 hp758731 hp716712 hp758732 hp758733 hp716714

noncomputable def hp758735 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 522765016) (BSN.cosEvenQ 536870912) 0 3 hp758731 hp716712 hp758732 rfl rfl rfl

noncomputable def hp758736 := hp758734 hp758732 301840810 rfl rfl rfl rfl rfl rfl rfl rfl (hp758735 rfl)

noncomputable def hp758737 := @BSN.binarySplit_of_base3 (BSN.cosOddP 522765016) (BSN.cosOddQ 536870912) 0 3 hp758733 hp716714 hp758732 rfl rfl rfl

noncomputable def hp758738 := hp758725 hd4944 hd4946 hd4961 hd4963 hd4918 (hp758729 (hp758730 rfl) rfl rfl rfl rfl) (hp758736 (hp758737 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758739 := @hp758586 6447 8388608 (hp758738 rfl rfl rfl rfl rfl) (hp758738 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp758740 := @hp758584 Bool.true 244552383 268435456 6447 8388608 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 850199 1000)) (Enclosure.sfrac Bool.false 850199 1000) 11) hp758739

noncomputable def hp758741 := @Enclosure.Real.IsNear.mulLit_tf hp758575 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1))) 9838179 33554432 1

noncomputable def hp758742 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp758574 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp758743 := @hp758742 1 1 0 1 9838179 33554432 1 33554432 9838179 33554432 1

noncomputable def hp758744 := @Enclosure.Real.IsNear.of_eq (hp758574 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp758745 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 850199 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758746 := @hp758744 (@Inv.inv Real Real.instInv (Real.sqrt hp758576)) Bool.false 9838179 33554432 1 33554432 (hp758745 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 850199 1000) 850199 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000))))

noncomputable def hp758747 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp758576)) Bool.false 19676358 67108864 2 67108864 9838179 33554432

noncomputable def hp758748 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp758576) Bool.false 228883804 67108864 6 67108864 57220951 16777216 3 33554432

noncomputable def hp758749 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 850199 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758750 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 850199 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758751 := @hp758750 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 850199 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9080726410693

noncomputable def hp758752 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 850199 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 850199 1000 0

noncomputable def hp758753 := @hp758752 1 10680707 67108864 1 67108864 9080726410693 67108864000 850199 67108864000 (Enclosure.Real.IsNear.const Bool.false 850199 1000) hd4949

noncomputable def hp758754 := @hp758751 67108864000 850199 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 850199 1000) 850199 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000))) (hp758753 rfl)

noncomputable def hp758755 := @hp758749 9080726410693 67108864000 850199 67108864000 390319477 390319514 33554432 hp758754 rfl rfl rfl

noncomputable def hp758756 := @Enclosure.Real.IsNear.recentre' hp758576 Bool.false 780638991 67108864 37 67108864 780638991 67108864 37 67108864 (hp758755 rfl rfl rfl)

noncomputable def hp758757 := @Enclosure.Real.IsNear.sqrt_image hp758576 780638991 67108864 37 67108864 114441899 114441905 33554432 (hp758756 rfl) rfl rfl

noncomputable def hp758758 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp758576) 57220951 16777216 3 33554432 9838178 9838180 33554432 (hp758748 (hp758757 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp758759 := @hp758743 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp758746 (@hp758747 1 33554432 (hp758758 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp758760 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758761 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp758762 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1))) (hp758760 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758761 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp758763 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 850199 1000) 850199 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl

noncomputable def hp758764 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758765 := @hp758764 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758761 (Enclosure.sfrac Bool.false 1 16)))) 99664215

noncomputable def hp758766 := @hp758765 67108864 531 67108864 2338473 8388608 22722769 2854748160000 233062075843695 562949953421312 1791489971056741 127719270682460160000

noncomputable def hp758767 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758768 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758769 := @hp758767 (@Neg.neg Real Real.instNeg hp758768) Bool.true 99664215 67108864 531 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758770 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp758771 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp758772 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp758773 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 266667727) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp758774 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1))) Bool.false 37530146198453032486285

noncomputable def hp758775 := nat_lit 998484790499199279158470083

noncomputable def hp758776 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp758777 := @Enclosure.Real.IsNear.subLit_ff_p hp758576 (Enclosure.sfrac Bool.false 11 1) 780638991 67108864 37 67108864 11 1 0

noncomputable def hp758778 := @hp758776 500000000000000 42441487 67108864 37 67108864 37530146198453032486285 9444732965739290427392 hp758775 hp738031 hd4948 (@hp758777 1 42441487 42441487 67108864 37 67108864 (hp758756 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758779 := @hp758773 266667727 67108864 117 33554432 Bool.true 45187730 67108864 1 10890000 (@hp758774 9444732965739290427392 hp758775 hp738031 266667727 67108864 117 33554432 (hp758778 rfl) rfl) (Enclosure.sfrac_false_div 266667727 67108864)

noncomputable def hp758780 := nat_lit 8047249841275281503944704

noncomputable def hp758781 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 266667727) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp758780) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp758782 := BSN.sin_reduce_arg_pos_rat_q2 266667727 67108864 226375608064910080 72057594037927936 0 hp758780 hp617687 rfl rfl rfl rfl

noncomputable def hp758783 := nat_lit 102551795879254841412868394689261357062666246879990848546461093133382572707984491627165770881

noncomputable def hp758784 := nat_lit 29251051032908305869876555520050668725054301585564977113402646581383413254779343401116801

noncomputable def hp758785 := nat_lit 307596885535698707626865430956743969850548632036801415685156474106984951297443916194695079041

noncomputable def hp758786 := BSN.cos_dyadic_bound_f 114358298351 137438953472 3 2 67108864 21801270 hp758783 hp746621 hp758784 hp758785 hp746624

noncomputable def hp758787 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 114358298351) (BSN.cosEvenQ 137438953472) 0 2 hp758783 hp746621 hp758784 rfl rfl rfl

noncomputable def hp758788 := hp758786 hp758784 45187730 rfl rfl rfl rfl rfl rfl rfl rfl (hp758787 rfl)

noncomputable def hp758789 := @BSN.binarySplit_of_base2 (BSN.cosOddP 114358298351) (BSN.cosOddQ 137438953472) 0 2 hp758785 hp746624 hp758784 rfl rfl rfl

noncomputable def hp758790 := @BSN.cos_arg_round Bool.false 45187730 67108864 hp758780 hp617687 114358298351 137438953472 21801270 21780000 (hp758788 (hp758789 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758791 := hp758781 45187730 67108864 0 1000000000000000 21780000 10890000 hp758782 BSN.pi_near_15 hp758790 rfl rfl

noncomputable def hp758792 := @hp758771 22593865 33554432 81730277 22837985280000 (@hp758772 45187730 67108864 1307684432 365407764480000 22593865 33554432 81730277 22837985280000 (hp758779 (hp758791 rfl rfl) rfl rfl) rfl)

noncomputable def hp758793 := @hp758770 22593865 33554432 81730277 22837985280000 49831842 49832373 33554432 hp758792 rfl rfl rfl

noncomputable def hp758794 := @Enclosure.Real.IsNear.recentre' hp758768 Bool.false 99664215 67108864 531 67108864 99664215 67108864 531 67108864 (hp758793 rfl rfl rfl)

noncomputable def hp758795 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758761 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp758796 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758761 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 7773333)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true

noncomputable def hp758797 := nat_lit 1174672878454588844660309806525

noncomputable def hp758798 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758761 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp758797

noncomputable def hp758799 := nat_lit 30352315084590939022539316216555317

noncomputable def hp758800 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp758761 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp758801 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp758802 := @hp758801 (Enclosure.sfrac Bool.false 1 16) 1046920160269599 4503599627370496 5623699375 4503599627370496 1 16 0

noncomputable def hp758803 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)) 1801279818771169

noncomputable def hp758804 := @hp758803 4503599627370496 3140671407 4503599627370496 42441487 67108864 37 67108864 70257622654390722625536 1046920160269599 4503599627370496 5623699375

noncomputable def hp758805 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)) 42441487 67108864 37

noncomputable def hp758806 := @hp758805 67108864 42441487 67108864 37 67108864 1801279818771169 4503599627370496 3140671407 4503599627370496 (@hp758777 1 42441487 42441487 67108864 37 67108864 (hp758756 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758807 := hp758806 (@hp758777 1 42441487 42441487 67108864 37 67108864 (hp758756 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758808 := @hp758804 4503599627370496 (hp758807 rfl) (@hp758777 1 42441487 42441487 67108864 37 67108864 (hp758756 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp758809 := @hp758800 500000000000000 1328395136980255 4503599627370496 5623699375 4503599627370496 hp758797 hp627574 hp758799 hp742826 hd4948 (@hp758802 1 21254322191684080 1328395136980255 4503599627370496 5623699375 4503599627370496 (hp758808 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp758810 := @hp758796 7773333 4194304 33 4194304 Bool.true 9353892 33554432 1 10890000 (@hp758798 hp627574 hp758799 hp742826 7773333 4194304 33 4194304 (hp758809 rfl) rfl) (Enclosure.sfrac_true_div 7773333 4194304)

noncomputable def hp758811 := nat_lit 7028718516486521801870219341747015922205549892347044293880549578218131237046869130625041

noncomputable def hp758812 := nat_lit 48672905607790927464602605592109040719461903388798794971216608595785317269334278161

noncomputable def hp758813 := nat_lit 42442414019480956274020549571540228061423546583403631574228554501765730128334935584555025

noncomputable def hp758814 := BSN.cos_dyadic_bound_t 7773333 4194304 4 3 33554432 10890000 hp758811 hp633286 hp758812 hp758813 hp633289

noncomputable def hp758815 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 7773333) (BSN.cosEvenQ 4194304) 0 3 hp758811 hp633286 hp758812 rfl rfl rfl

noncomputable def hp758816 := hp758814 hp758812 9353892 rfl rfl rfl rfl rfl rfl rfl rfl (hp758815 rfl)

noncomputable def hp758817 := @BSN.binarySplit_of_base3 (BSN.cosOddP 7773333) (BSN.cosOddQ 4194304) 0 3 hp758813 hp633289 hp758812 rfl rfl rfl

noncomputable def hp758818 := hp758810 (BSN.cos_neg_of_bound 7773333 4194304 Bool.true 9353892 33554432 1 10890000 (hp758816 (hp758817 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp758819 := hp758766 (hp758769 (@Enclosure.Real.IsNear.neg hp758768 Bool.false 99664215 67108864 531 67108864 (hp758794 rfl))) (@hp758795 9353892 33554432 363564304 45675970560000 2338473 8388608 22722769 2854748160000 (hp758818 rfl) rfl)

noncomputable def hp758820 := @hp758741 33554432 233062075843695 562949953421312 1791489971056741 127719270682460160000 2292906420261847431405 18889465931478580854784 321415941125600844991 hp746784 (hp758759 rfl) (@hp758762 Bool.false 233062075843695 562949953421312 1791489971056741 127719270682460160000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758576 (Enclosure.sfrac Bool.false 11 1)) (hp758763 rfl (hp758579 rfl rfl))) (hp758819 rfl))

noncomputable def hp758821 := @hp758573 60205498711294375500991 hp746784 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 850199 1000))) (@hp758578 60205498711294375500991 hp746784 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 850199 1000) 11 (hp758579 rfl rfl)) (@hp758582 60205498711294375500991 hp746784 hp758740 (hp758820 rfl) rfl rfl))

theorem hd5044 : hp758572 hp746784 := hp758821

noncomputable def hp758822 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 851320 1000)) Bool.false 207964028705560656893247 37778931862957161709568 442233252000319433268739

noncomputable def hp758823 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 851320 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 851320 1000)) Bool.false 207964028705560656893247 37778931862957161709568

noncomputable def hp758824 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 851320 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758825 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp758824 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp758826 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 851320 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp758827 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp758825 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp758828 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 851320 1000)) hp758827 Bool.false 207964028705560656893247 37778931862957161709568

noncomputable def hp758829 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 851320 1000) 851320 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl

noncomputable def hp758830 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp758825 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp758831 := nat_lit 13956229719293566167199575441408

noncomputable def hp758832 := @hp758830 361199901 67108864 103289 134217728 4626561261828151203135 37778931862957161709568 2500060349631851060739 hp751106 hp758831 207964028705560656893247 37778931862957161709568

noncomputable def hp758833 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) 11)

noncomputable def hp758834 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) 11) hp758833

noncomputable def hp758835 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) 11)

noncomputable def hp758836 := @hp758835 1444799604 536870912 206578 536870912 1444799604 536870912 206578 536870912 1551341762113437696 361199901 67108864

noncomputable def hp758837 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp758838 := hp758837 BSN.quadSignPos 9 10 11 851320 1000 188 240 536870912 268435456 9007199254740992

noncomputable def hp758839 := hp758838 Bool.false 893071013563 3879 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp758840 := hp758839 Bool.false 1325525416 177342 Bool.true 779878070 Bool.true 488923359 28296951008113761 1 Bool.false 63289273

noncomputable def hp758841 := hp758840 Bool.false Bool.false 329209390 Bool.false Bool.false 1444799604 206578 BSN.abs_quadSignPos (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 63289273 536870912) BSN.abs_quadSignPos

noncomputable def hp758842 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp758843 := hp758842 BSN.quadSignPos 7 8 9 851320 1000 67 131 536870912 268435456 9007199254740992

noncomputable def hp758844 := hp758843 Bool.false 893071013563 3879 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp758845 := hp758844 Bool.false 963673641 144835 Bool.true 833452661 Bool.true 693902282 28296951008113761 1 Bool.false 536780331

noncomputable def hp758846 := hp758845 Bool.false Bool.false 516213803 Bool.false Bool.false 1325525416 177342 BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536780331 536870912) BSN.abs_quadSignPos

noncomputable def hp758847 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp758848 := hp758847 BSN.quadSignPos 5 6 7 851320 1000 87 4 536870912 268435456 9007199254740992

noncomputable def hp758849 := hp758848 Bool.false 893071013563 3879 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp758850 := hp758849 Bool.false 578388957 107630 Bool.false 780852531 Bool.false 321586932 28296951008113761 1 Bool.false 533241414

noncomputable def hp758851 := hp758850 Bool.false Bool.false 443400894 Bool.false Bool.false 963673641 144835 BSN.abs_quadSignPos (BSN.cos_quad_nat3 87 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 533241414 536870912) BSN.abs_quadSignPos

noncomputable def hp758852 := hp758847 BSN.quadSignNeg 3 4 5 851320 1000 307 186 536870912 268435456 9007199254740992

noncomputable def hp758853 := hp758852 Bool.false 893071013563 3879 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp758854 := hp758853 Bool.false 440205026 63616 Bool.false 568989550 Bool.false 622564141 28296951008113761 1 Bool.false 468296509

noncomputable def hp758855 := hp758854 Bool.false Bool.false 214582730 Bool.true Bool.false 578388957 107630 BSN.abs_quadSignPos (BSN.cos_quad_nat3 307 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 468296509 536870912) BSN.abs_quadSignNeg

noncomputable def hp758856 := hp758842 BSN.quadSignPos 1 2 3 851320 1000 683 463 536870912 268435456 9007199254740992

noncomputable def hp758857 := hp758856 Bool.false 893071013563 3879 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp758858 := hp758857 Bool.false 580488 3938 Bool.false 284791833 Bool.false 496652260 28296951008113761 1 Bool.false 271622033

noncomputable def hp758859 := hp758858 Bool.false Bool.false 428784341 Bool.false Bool.false 440205026 63616 BSN.abs_quadSignPos (BSN.cos_quad_nat3 683 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 271622033 536870912) BSN.abs_quadSignPos

noncomputable def hp758860 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) 1) Bool.false

noncomputable def hp758861 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)))

noncomputable def hp758862 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000))) Bool.false 72561 67108864

noncomputable def hp758863 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 111633876695) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 111633876695 67108864

noncomputable def hp758864 := nat_lit 8020951543525215781497567705323211832168529290061

noncomputable def hp758865 := nat_lit 4821806446385625910931843563166896868535828480

noncomputable def hp758866 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) Bool.false hp758864 hp758865 32544101605053991

noncomputable def hp758867 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 851320 4000) (Real.log (Enclosure.sfrac Bool.false 2898983969600 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1702640))))))

noncomputable def hp758868 := nat_lit 214637597594314785323508736000000000

noncomputable def hp758869 := nat_lit 1096351853990569432183256950149120000000

noncomputable def hp758870 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp758867 (Enclosure.sfrac Bool.false 851320 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 851320 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp758868 hp758869)) Bool.false

noncomputable def hp758871 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 851320 1000) 851320 1000 2898983969600 16000000 1702640

noncomputable def hp758872 := hp758871 4000 2000 hp758868 hp758869 (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl rfl rfl rfl

noncomputable def hp758873 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp758867 (Enclosure.sfrac Bool.false 851320 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 851320 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp758868 hp758869) 149832470612710356569 90071992547409920

noncomputable def hp758874 := nat_lit 164269087611396419205070186605019378322811479860449280000000

noncomputable def hp758875 := @hp758873 32544101605053991 4505600000000000000000 hp758868 hp758869 0 1 hp758874 hp758864 hp758865 32544101605053991 4505600000000000000000

noncomputable def hp758876 := @Enclosure.Real.IsNear.subLit_ff_p (hp758867 (Enclosure.sfrac Bool.false 851320 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 851320 2000) (Real.log Real.pi)) 968607325365582909373 450359962737049600 5425007960117 2200000000000000000

noncomputable def hp758877 := nat_lit 1256885861641546998797565952000

noncomputable def hp758878 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 851320 4000) (Real.log (Enclosure.sfrac Bool.false 2898983969600 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1702640))))))

noncomputable def hp758879 := @hp758878 (Enclosure.sfrac Bool.false 851320 2000) 1160307547104235442109 450359962737049600 5425007960117 2200000000000000000 851320 2000 0

noncomputable def hp758880 := nat_lit 1937214650731165818746000

noncomputable def hp758881 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 851320 4000) (Real.log (Enclosure.sfrac Bool.false 2898983969600 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1702640))))) 1160484336922317010709

noncomputable def hp758882 := nat_lit 2612780318386904486087101653851308032

noncomputable def hp758883 := @hp758881 450359962737049600 266037894012179 108900000000000000000 883949090407843 2251799813685248 200000001089 8712000000000000000 hp758882 1160307547104235442109 450359962737049600 5425007960117

noncomputable def hp758884 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 851320 4000) (Real.log (Enclosure.sfrac Bool.false 2898983969600 16000000)) 851320 4000 0 1 54526351403576423 4503599627370496

noncomputable def hp758885 := nat_lit 117094448024282217110831104

noncomputable def hp758886 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2898983969600) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp758885 hp617687

noncomputable def hp758887 := BSN.log_rat_reduce_isNear 2898983969600 16000000 17 5797967939200 4194304000000 86914055 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp758888 := nat_lit 100731890643949199717627853431959744759783009309444733179560365993688843724745930460510171886852906429030858752000000000000000000000

noncomputable def hp758889 := nat_lit 878473015992117150130880144529353014224835106532275606831842768657883381419110642250513056608598326667273830400000000000000000000

noncomputable def hp758890 := nat_lit 103816285831407001298205332311622590866748906057891120007709379995914265066606010721976795906736914432000000000000000000000

noncomputable def hp758891 := BSN.log_dyadic_bound 801831969600 4996135969600 6 5 hp758888 268435456 87120000 hp758889 hp758890 86914055 5797967939200

noncomputable def hp758892 := hp758891 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp758893 := @BSN.binarySplit_of_base5 (BSN.artanhP 801831969600) (BSN.artanhQ 4996135969600) 0 5 hp758889 hp758888 hp758890 rfl rfl rfl

noncomputable def hp758894 := hp758887 rfl rfl rfl rfl (hp758892 (hp758893 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp758895 := @hp758884 12500018513 1089000000000000000 1160484336922317010709 450359962737049600 266037894012179 108900000000000000000 (Enclosure.Real.IsNear.const Bool.false 851320 4000) (BSN.isNear_log_sfrac 2898983969600 16000000 54526351403576423 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp758886 1000001481040000 87120000000000000000000 54526351403576423 4503599627370496 12500018513 1089000000000000000 (hp758894 rfl rfl rfl) rfl)) rfl

noncomputable def hp758896 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1702640)))) 1 4

noncomputable def hp758897 := @hp758896 0 1 883949090407843 562949953421312 200000001089 2178000000000000000 883949090407843 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp758898 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1702640))) 884279719003555 562949953421312 1

noncomputable def hp758899 := @hp758898 2000000000000000 19707 33554432 1 10890000 29660409645551820210176 883949090407843 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp758900 := BSN.arctan_dyadic_bound_f 1000 1702640 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp758901 := hp758900 1 19707 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1702640) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1702640) 0 0 rfl)

noncomputable def hp758902 := hp758897 (hp758899 (hp758901 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp758903 := @hp758876 817496226363 1677721600 63849 13421772800 hp758877 149832470612710356569 90071992547409920 32544101605053991 4505600000000000000000 (@hp758879 1 hp758880 968607325365582909373 450359962737049600 5425007960117 2200000000000000000 (@hp758883 2200000000000000000 hp758895 hp758902 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 851320 2000) rfl rfl)

noncomputable def hp758904 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 851320 2000) (Real.log Real.pi) 851320 2000 0 1 38410761 33554432

noncomputable def hp758905 := hp758903 (@hp758904 3 268435456 817496226363 1677721600 63849 13421772800 (Enclosure.Real.IsNear.const Bool.false 851320 2000) hd4909 rfl) rfl

noncomputable def hp758906 := @hp758866 4505600000000000000000 111633876695 67108864 243 33554432 (@hp758870 hp758864 hp758865 32544101605053991 4505600000000000000000 (hp758872 rfl rfl rfl rfl rfl) (hp758875 (hp758905 rfl) (Enclosure.Real.IsNear.const Bool.true hp758868 hp758869) rfl rfl)) rfl

noncomputable def hp758907 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 111633876695) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 10457213299120364584960) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp758908 := BSN.sin_reduce_arg_pos_rat_q3 111633876695 67108864 226375608064910080 72057594037927936 264 10457213299120364584960 hp617687 rfl rfl rfl rfl

noncomputable def hp758909 := BSN.sin_dyadic_bound_f 148605938 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp758910 := hp758909 1 72561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 148605938) (BSN.sinEvenQ 137438953472) 0 0 rfl)

noncomputable def hp758911 := hp758910 (@BSN.binarySplit_of_le (BSN.sinOddP 148605938) (BSN.sinOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp758912 := @BSN.sin_arg_round Bool.false 72561 67108864 10457213299120364584960 hp617687 148605938 137438953472 21801270 21780000 hp758911 rfl

noncomputable def hp758913 := hp758907 72561 67108864 264 1000000000000000 21780000 10890000 hp758908 BSN.pi_near_15 hp758912 rfl rfl

noncomputable def hp758914 := @hp758863 243 33554432 Bool.false 72561 67108864 1 10890000 hp758906 (Enclosure.sfrac_false_div 111633876695 67108864) (hp758913 rfl rfl) rfl

noncomputable def hp758915 := @hp758860 72561 67108864 167489027 22837985280000 580488 536870912 3938 536870912 (@hp758861 Bool.false 72561 67108864 167489027 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000)) (@hp758862 2679824432 365407764480000 72561 67108864 167489027 22837985280000 (hp758914 rfl) rfl))

noncomputable def hp758916 := @hp758866 4505600000000000000000 893071013563 536870912 3879 536870912 (@hp758870 hp758864 hp758865 32544101605053991 4505600000000000000000 (hp758872 rfl rfl rfl rfl rfl) (hp758875 (hp758905 rfl) (Enclosure.Real.IsNear.const Bool.true hp758868 hp758869) rfl rfl)) rfl

noncomputable def hp758917 := hp758859 (BSN.cos_quad_nat3 463 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 428784341 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl rfl (hp758915 rfl) hp758916

noncomputable def hp758918 := nat_lit 1652657196048101909185861543900533167545363019900891696773684841233256385

noncomputable def hp758919 := nat_lit 43273323037344784720732873308690278419889826432331015781167957807041

noncomputable def hp758920 := nat_lit 4328317832841063584882946666516039464072794754307159241334100312250650561

noncomputable def hp758921 := BSN.sin_dyadic_bound_f 284791833 536870912 3 2 536870912 268435456 hp758918 hp708845 hp758919 hp758920 hp708848

noncomputable def hp758922 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 284791833) (BSN.sinEvenQ 536870912) 0 2 hp758918 hp708845 hp758919 rfl rfl rfl

noncomputable def hp758923 := hp758921 hp758919 271622033 rfl rfl rfl rfl rfl rfl rfl rfl (hp758922 rfl)

noncomputable def hp758924 := @BSN.binarySplit_of_base2 (BSN.sinOddP 284791833) (BSN.sinOddQ 536870912) 0 2 hp758920 hp708848 hp758919 rfl rfl rfl

noncomputable def hp758925 := nat_lit 15288895604475045963581532245858621351906684823468493307790247469424640000

noncomputable def hp758926 := nat_lit 3701854359106684699186490259471469812027806118069515501678617600000000

noncomputable def hp758927 := nat_lit 40036352152281804796057711088257244970536129518226322304828882753331200000

noncomputable def hp758928 := BSN.sin_dyadic_bound_f 496652260 536870912 3 2 536870912 268435456 hp758925 hp708845 hp758926 hp758927 hp708848

noncomputable def hp758929 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 496652260) (BSN.sinEvenQ 536870912) 0 2 hp758925 hp708845 hp758926 rfl rfl rfl

noncomputable def hp758930 := hp758928 hp758926 428784341 rfl rfl rfl rfl rfl rfl rfl rfl (hp758929 rfl)

noncomputable def hp758931 := @BSN.binarySplit_of_base2 (BSN.sinOddP 496652260) (BSN.sinOddQ 536870912) 0 2 hp758927 hp708848 hp758926 rfl rfl rfl

noncomputable def hp758932 := hp758917 hd4911 hd4913 hd4915 hd4917 hd4918 (hp758923 (hp758924 rfl) rfl rfl rfl rfl) (hp758930 (hp758931 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758933 := hp758855 (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 214582730 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl rfl (hp758932 rfl rfl rfl rfl rfl) hp758916

noncomputable def hp758934 := nat_lit 26342658365716598090858246844662272364341255078713925604062788796900000000

noncomputable def hp758935 := nat_lit 10985866624587213489923073295790861553702651940158904575039062500000000

noncomputable def hp758936 := nat_lit 68974890030913187130406961522112766225997292341109547879423907414500000000

noncomputable def hp758937 := BSN.sin_dyadic_bound_f 568989550 536870912 3 2 536870912 268435456 hp758934 hp708845 hp758935 hp758936 hp708848

noncomputable def hp758938 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 568989550) (BSN.sinEvenQ 536870912) 0 2 hp758934 hp708845 hp758935 rfl rfl rfl

noncomputable def hp758939 := hp758937 hp758935 468296509 rfl rfl rfl rfl rfl rfl rfl rfl (hp758938 rfl)

noncomputable def hp758940 := @BSN.binarySplit_of_base2 (BSN.sinOddP 568989550) (BSN.sinOddQ 536870912) 0 2 hp758936 hp708848 hp758935 rfl rfl rfl

noncomputable def hp758941 := nat_lit 20715164738140399554938483102776094085011166924723446899285573954382193629551193727760191944698184825352694086961

noncomputable def hp758942 := nat_lit 3390074374657211954223329549144072369362799345149590762081883291083234448361541881427738794572618942463281

noncomputable def hp758943 := nat_lit 125581902390180169029605768023177191201784575364158238996683341071186246541328986010018529075274881905893804948785

noncomputable def hp758944 := BSN.cos_dyadic_bound_f 622564141 536870912 4 3 536870912 268435456 hp758941 hp716712 hp758942 hp758943 hp716714

noncomputable def hp758945 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 622564141) (BSN.cosEvenQ 536870912) 0 3 hp758941 hp716712 hp758942 rfl rfl rfl

noncomputable def hp758946 := hp758944 hp758942 214582730 rfl rfl rfl rfl rfl rfl rfl rfl (hp758945 rfl)

noncomputable def hp758947 := @BSN.binarySplit_of_base3 (BSN.cosOddP 622564141) (BSN.cosOddQ 536870912) 0 3 hp758943 hp716714 hp758942 rfl rfl rfl

noncomputable def hp758948 := hp758933 hd4920 hd4922 hd4924 hd4926 hd4918 (hp758939 (hp758940 rfl) rfl rfl rfl rfl) (hp758946 (hp758947 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758949 := hp758851 (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 443400894 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl rfl (hp758948 rfl rfl rfl rfl rfl) hp758916

noncomputable def hp758950 := nat_lit 133344937572903016745925336063877345001790299694903765565828089924911723342635736844235769892298845153684385949361

noncomputable def hp758951 := nat_lit 51384042466787405418347106455324873917395735091292413203214741970277301089820931178963826027631819282179761

noncomputable def hp758952 := nat_lit 666115457229350906307247779665142444891675591598986479851834276560357382546979459191908748986928665268573582124721

noncomputable def hp758953 := BSN.sin_dyadic_bound_f 780852531 536870912 4 3 536870912 268435456 hp758950 hp642702 hp758951 hp758952 hp642705

noncomputable def hp758954 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 780852531) (BSN.sinEvenQ 536870912) 0 3 hp758950 hp642702 hp758951 rfl rfl rfl

noncomputable def hp758955 := hp758953 hp758951 533241414 rfl rfl rfl rfl rfl rfl rfl rfl (hp758954 rfl)

noncomputable def hp758956 := @BSN.binarySplit_of_base3 (BSN.sinOddP 780852531) (BSN.sinOddQ 536870912) 0 3 hp758952 hp642705 hp758951 rfl rfl rfl

noncomputable def hp758957 := nat_lit 1492848127521991925400298195479018502679805972599566851807712996040441856

noncomputable def hp758958 := nat_lit 114389757582274630088565393946851658088523704830689792521136074981376

noncomputable def hp758959 := nat_lit 4478315603050811226940717455649161804723240870389039175838096715971362816

noncomputable def hp758960 := BSN.cos_dyadic_bound_f 321586932 536870912 3 2 536870912 268435456 hp758957 hp708868 hp758958 hp758959 hp708870

noncomputable def hp758961 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 321586932) (BSN.cosEvenQ 536870912) 0 2 hp758957 hp708868 hp758958 rfl rfl rfl

noncomputable def hp758962 := hp758960 hp758958 443400894 rfl rfl rfl rfl rfl rfl rfl rfl (hp758961 rfl)

noncomputable def hp758963 := @BSN.binarySplit_of_base2 (BSN.cosOddP 321586932) (BSN.cosOddQ 536870912) 0 2 hp758959 hp708870 hp758958 rfl rfl rfl

noncomputable def hp758964 := hp758949 hd4928 hd4930 hd4932 hd4934 hd4918 (hp758955 (hp758956 rfl) rfl rfl rfl rfl) (hp758962 (hp758963 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758965 := hp758846 (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 516213803 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl rfl (hp758964 rfl rfl rfl rfl rfl) hp758916

noncomputable def hp758966 := nat_lit 173147191370584458230815518571105262934053109746028837317566416485359737306411909769015058090030845410594898738321

noncomputable def hp758967 := nat_lit 112349527480412025153315885252684451909648214817966333108035035339981656352128835122823483662342489699941521

noncomputable def hp758968 := nat_lit 864709547257160309400249243656422847298280552597924316176734040242080957811876610972580593468306584116581021940881

noncomputable def hp758969 := BSN.sin_dyadic_bound_f 833452661 536870912 4 3 536870912 268435456 hp758966 hp642702 hp758967 hp758968 hp642705

noncomputable def hp758970 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 833452661) (BSN.sinEvenQ 536870912) 0 3 hp758966 hp642702 hp758967 rfl rfl rfl

noncomputable def hp758971 := hp758969 hp758967 536780331 rfl rfl rfl rfl rfl rfl rfl rfl (hp758970 rfl)

noncomputable def hp758972 := @BSN.binarySplit_of_base3 (BSN.sinOddP 833452661) (BSN.sinOddQ 536870912) 0 3 hp758968 hp642705 hp758967 rfl rfl rfl

noncomputable def hp758973 := nat_lit 83109754048439109756205275072893835612041104602826462731197545565764147641689480585946683749704520411370920677376

noncomputable def hp758974 := nat_lit 12461771645604082124110519992617002363336881866035041435712745335426476095951250537496867419678756320382976

noncomputable def hp758975 := nat_lit 415311872495185099922803986649329589625294518366892207993576998310210078546495687880939308480552370762279627329536

noncomputable def hp758976 := BSN.sin_dyadic_bound_f 693902282 536870912 4 3 536870912 268435456 hp758973 hp642702 hp758974 hp758975 hp642705

noncomputable def hp758977 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 693902282) (BSN.sinEvenQ 536870912) 0 3 hp758973 hp642702 hp758974 rfl rfl rfl

noncomputable def hp758978 := hp758976 hp758974 516213803 rfl rfl rfl rfl rfl rfl rfl rfl (hp758977 rfl)

noncomputable def hp758979 := @BSN.binarySplit_of_base3 (BSN.sinOddP 693902282) (BSN.sinOddQ 536870912) 0 3 hp758975 hp642705 hp758974 rfl rfl rfl

noncomputable def hp758980 := hp758965 hd4936 hd4938 hd4940 hd4942 hd4918 (hp758971 (hp758972 rfl) rfl rfl rfl rfl) (hp758978 (hp758979 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758981 := hp758841 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 329209390 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl rfl (hp758980 rfl rfl rfl rfl rfl) hp758916

noncomputable def hp758982 := nat_lit 51090661836085662915432096953009621854509544505162763999736627272935381249846781682211628343743980905996864000000

noncomputable def hp758983 := nat_lit 50619808631321120885267852109542109453525170660861588058819493561617568857383878005965970672001000000000000

noncomputable def hp758984 := nat_lit 309403537558496328380053706284646332451312336002939173010816412455569811322277730199335415776190301934074841600000

noncomputable def hp758985 := BSN.cos_dyadic_bound_f 779878070 536870912 4 3 536870912 268435456 hp758982 hp716712 hp758983 hp758984 hp716714

noncomputable def hp758986 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 779878070) (BSN.cosEvenQ 536870912) 0 3 hp758982 hp716712 hp758983 rfl rfl rfl

noncomputable def hp758987 := hp758985 hp758983 63289273 rfl rfl rfl rfl rfl rfl rfl rfl (hp758986 rfl)

noncomputable def hp758988 := @BSN.binarySplit_of_base3 (BSN.cosOddP 779878070) (BSN.cosOddQ 536870912) 0 3 hp758984 hp716714 hp758983 rfl rfl rfl

noncomputable def hp758989 := nat_lit 7978655259189613100434811744246615724508209920587162940082927627525843201

noncomputable def hp758990 := nat_lit 3265324104678094570268729923723378255540144481785962286222568678385921

noncomputable def hp758991 := nat_lit 23929435129359483112163897772892400417013549472797916895676337745220757761

noncomputable def hp758992 := BSN.cos_dyadic_bound_f 488923359 536870912 3 2 536870912 268435456 hp758989 hp708868 hp758990 hp758991 hp708870

noncomputable def hp758993 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 488923359) (BSN.cosEvenQ 536870912) 0 2 hp758989 hp708868 hp758990 rfl rfl rfl

noncomputable def hp758994 := hp758992 hp758990 329209390 rfl rfl rfl rfl rfl rfl rfl rfl (hp758993 rfl)

noncomputable def hp758995 := @BSN.binarySplit_of_base2 (BSN.cosOddP 488923359) (BSN.cosOddQ 536870912) 0 2 hp758991 hp708870 hp758990 rfl rfl rfl

noncomputable def hp758996 := hp758981 hd4944 hd4946 hd4961 hd4963 hd4918 (hp758987 (hp758988 rfl) rfl rfl rfl rfl) (hp758994 (hp758995 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp758997 := @hp758836 103289 134217728 (hp758996 rfl rfl rfl rfl rfl) (hp758996 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp758998 := @hp758834 Bool.false 361199901 67108864 103289 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 851320 1000)) (Enclosure.sfrac Bool.false 851320 1000) 11) hp758997

noncomputable def hp758999 := @Enclosure.Real.IsNear.mulLit_tf hp758825 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1))) 19669877 67108864 1

noncomputable def hp759000 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp758824 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759001 := @hp759000 1 1 0 1 19669877 67108864 1 67108864 19669877 67108864 1

noncomputable def hp759002 := @Enclosure.Real.IsNear.of_eq (hp758824 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759003 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 851320 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759004 := @hp759002 (@Inv.inv Real Real.instInv (Real.sqrt hp758826)) Bool.false 19669877 67108864 1 67108864 (hp759003 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 851320 1000) 851320 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000))))

noncomputable def hp759005 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp758826)) Bool.false 19669877 67108864 1 67108864 19669877 67108864

noncomputable def hp759006 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp758826) Bool.false 228959214 67108864 6 67108864 114479607 33554432 3 33554432

noncomputable def hp759007 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 851320 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759008 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 851320 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759009 := @hp759008 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 851320 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 227317487081

noncomputable def hp759010 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 851320 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 851320 1000 0

noncomputable def hp759011 := @hp759010 1 10680707 67108864 1 67108864 227317487081 1677721600 21283 1677721600 (Enclosure.Real.IsNear.const Bool.false 851320 1000) hd4949

noncomputable def hp759012 := @hp759009 1677721600 21283 1677721600 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 851320 1000) 851320 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000))) (hp759011 rfl)

noncomputable def hp759013 := @hp759007 227317487081 1677721600 21283 1677721600 390576713 390576750 33554432 hp759012 rfl rfl rfl

noncomputable def hp759014 := @Enclosure.Real.IsNear.recentre' hp758826 Bool.false 781153463 67108864 37 67108864 781153463 67108864 37 67108864 (hp759013 rfl rfl rfl)

noncomputable def hp759015 := @Enclosure.Real.IsNear.sqrt_image hp758826 781153463 67108864 37 67108864 114479604 114479610 33554432 (hp759014 rfl) rfl rfl

noncomputable def hp759016 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp758826) 114479607 33554432 3 33554432 9834938 9834939 33554432 (hp759006 (hp759015 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp759017 := @hp759001 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp759004 (@hp759005 1 67108864 (hp759016 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp759018 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759019 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp759020 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1))) (hp759018 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759019 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp759021 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 851320 1000) 851320 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl

noncomputable def hp759022 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759023 := @hp759022 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759019 (Enclosure.sfrac Bool.false 1 16)))) 52678165

noncomputable def hp759024 := @hp759023 33554432 295 33554432 4465047 16777216 365606179 45675970560000 235210482598755 562949953421312 571140429029171 38315781204738048000

noncomputable def hp759025 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759026 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759027 := @hp759025 (@Neg.neg Real Real.instNeg hp759026) Bool.true 52678165 33554432 295 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759028 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759029 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp759030 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp759031 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 134950125) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp759032 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1))) Bool.false 37985083354048229434245

noncomputable def hp759033 := nat_lit 998484790503618559987885507

noncomputable def hp759034 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp759035 := @Enclosure.Real.IsNear.subLit_ff_p hp758826 (Enclosure.sfrac Bool.false 11 1) 781153463 67108864 37 67108864 11 1 0

noncomputable def hp759036 := @hp759034 500000000000000 42955959 67108864 37 67108864 37985083354048229434245 9444732965739290427392 hp759033 hp738031 hd4948 (@hp759035 1 42955959 42955959 67108864 37 67108864 (hp759014 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759037 := @hp759031 134950125 33554432 233 67108864 Bool.true 42746360 67108864 1 10890000 (@hp759032 9444732965739290427392 hp759033 hp738031 134950125 33554432 233 67108864 (hp759036 rfl) rfl) (Enclosure.sfrac_false_div 134950125 33554432)

noncomputable def hp759038 := nat_lit 4256552750689905677434880

noncomputable def hp759039 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 134950125) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp759038) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp759040 := BSN.sin_reduce_arg_pos_rat_q2 134950125 33554432 226375608064910080 72057594037927936 0 hp759038 hp619237 rfl rfl rfl rfl

noncomputable def hp759041 := nat_lit 128450755818441688147828515918553667152439338616840071926567937456566032524412797631699690625

noncomputable def hp759042 := nat_lit 45884470050125783013809918510499716073071530318857313289138051976490339231860781062890625

noncomputable def hp759043 := nat_lit 385260498515224812877457927918640002025171872789882501153125536265745116894774671332973290625

noncomputable def hp759044 := BSN.cos_dyadic_bound_f 120978505455 137438953472 3 2 67108864 21801270 hp759041 hp746621 hp759042 hp759043 hp746624

noncomputable def hp759045 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 120978505455) (BSN.cosEvenQ 137438953472) 0 2 hp759041 hp746621 hp759042 rfl rfl rfl

noncomputable def hp759046 := hp759044 hp759042 42746360 rfl rfl rfl rfl rfl rfl rfl rfl (hp759045 rfl)

noncomputable def hp759047 := @BSN.binarySplit_of_base2 (BSN.cosOddP 120978505455) (BSN.cosOddQ 137438953472) 0 2 hp759043 hp746624 hp759042 rfl rfl rfl

noncomputable def hp759048 := @BSN.cos_arg_round Bool.false 42746360 67108864 hp759038 hp619237 120978505455 137438953472 21801270 21780000 (hp759046 (hp759047 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759049 := hp759039 42746360 67108864 0 1000000000000000 21780000 10890000 hp759040 BSN.pi_near_15 hp759048 rfl rfl

noncomputable def hp759050 := @hp759029 5343295 8388608 162779929 45675970560000 (@hp759030 42746360 67108864 2604478864 730815528960000 5343295 8388608 162779929 45675970560000 (hp759037 (hp759049 rfl rfl) rfl rfl) rfl)

noncomputable def hp759051 := @hp759028 5343295 8388608 162779929 45675970560000 52677870 52678460 33554432 hp759050 rfl rfl rfl

noncomputable def hp759052 := @Enclosure.Real.IsNear.recentre' hp759026 Bool.false 105356330 67108864 590 67108864 52678165 33554432 295 33554432 (hp759051 rfl rfl rfl)

noncomputable def hp759053 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759019 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp759054 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759019 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 61746199)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp759055 := nat_lit 1166352722979639326471393613805

noncomputable def hp759056 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759019 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp759055

noncomputable def hp759057 := nat_lit 152788960356774159136219254059379193

noncomputable def hp759058 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759019 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp759059 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp759060 := @hp759059 (Enclosure.sfrac Bool.false 1 16) 1037511196910895 4503599627370496 5661770303 4503599627370496 1 16 0

noncomputable def hp759061 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)) 1845214413609681

noncomputable def hp759062 := @hp759061 4503599627370496 3178742335 4503599627370496 42955959 67108864 37 67108864 69626197811970472673280 1037511196910895 4503599627370496 5661770303

noncomputable def hp759063 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)) 42955959 67108864 37

noncomputable def hp759064 := @hp759063 67108864 42955959 67108864 37 67108864 1845214413609681 4503599627370496 3178742335 4503599627370496 (@hp759035 1 42955959 42955959 67108864 37 67108864 (hp759014 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759065 := hp759064 (@hp759035 1 42955959 42955959 67108864 37 67108864 (hp759014 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759066 := @hp759062 4503599627370496 (hp759065 rfl) (@hp759035 1 42955959 42955959 67108864 37 67108864 (hp759014 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759067 := @hp759058 500000000000000 1318986173621551 4503599627370496 5661770303 4503599627370496 hp759055 hp627574 hp759057 hp738055 hd4948 (@hp759060 1 21103778777944816 1318986173621551 4503599627370496 5661770303 4503599627370496 (hp759066 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp759068 := @hp759054 61746199 33554432 531 67108864 Bool.true 8930094 33554432 1 10890000 (@hp759056 hp627574 hp759057 hp738055 61746199 33554432 531 67108864 (hp759067 rfl) rfl) (Enclosure.sfrac_true_div 61746199 33554432)

noncomputable def hp759069 := nat_lit 469378075628959210106571097296973500396065993872157535362683539745673358115082479539088926733142881

noncomputable def hp759070 := nat_lit 3071303531627963084397881149359490235888814076999257015648556036715820034261094271815252085601

noncomputable def hp759071 := nat_lit 2834675411394249213963982782956811457047599765733245502013437842702459936580843531587793690330041185

noncomputable def hp759072 := BSN.cos_dyadic_bound_t 61746199 33554432 4 3 33554432 10890000 hp759069 hp681868 hp759070 hp759071 hp681871

noncomputable def hp759073 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 61746199) (BSN.cosEvenQ 33554432) 0 3 hp759069 hp681868 hp759070 rfl rfl rfl

noncomputable def hp759074 := hp759072 hp759070 8930094 rfl rfl rfl rfl rfl rfl rfl rfl (hp759073 rfl)

noncomputable def hp759075 := @BSN.binarySplit_of_base3 (BSN.cosOddP 61746199) (BSN.cosOddQ 33554432) 0 3 hp759071 hp681871 hp759070 rfl rfl rfl

noncomputable def hp759076 := hp759068 (BSN.cos_neg_of_bound 61746199 33554432 Bool.true 8930094 33554432 1 10890000 (hp759074 (hp759075 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp759077 := hp759024 (hp759027 (@Enclosure.Real.IsNear.neg hp759026 Bool.false 52678165 33554432 295 33554432 (hp759052 rfl))) (@hp759053 8930094 33554432 5849698864 730815528960000 4465047 16777216 365606179 45675970560000 (hp759076 rfl) rfl)

noncomputable def hp759078 := @hp758999 67108864 235210482598755 562949953421312 571140429029171 38315781204738048000 4626561261828151203135 37778931862957161709568 2500060349631851060739 hp751106 (hp759017 rfl) (@hp759020 Bool.false 235210482598755 562949953421312 571140429029171 38315781204738048000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp758826 (Enclosure.sfrac Bool.false 11 1)) (hp759021 rfl (hp758829 rfl rfl))) (hp759077 rfl))

noncomputable def hp759079 := @hp758823 442233252000319433268739 hp751106 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 851320 1000))) (@hp758828 442233252000319433268739 hp751106 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 851320 1000) 11 (hp758829 rfl rfl)) (@hp758832 442233252000319433268739 hp751106 hp758998 (hp759078 rfl) rfl rfl))

theorem hd5045 : hp758822 hp751106 := hp759079

noncomputable def hp759080 := nat_lit 3991951877892674242857709

noncomputable def hp759081 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 853239 1000)) Bool.true 507836835258337612835 1180591620717411303424 hp759080

noncomputable def hp759082 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 853239 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 853239 1000)) Bool.true 507836835258337612835 1180591620717411303424

noncomputable def hp759083 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 853239 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759084 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp759083 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759085 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 853239 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759086 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp759084 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp759087 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 853239 1000)) hp759086 Bool.true 507836835258337612835 1180591620717411303424

noncomputable def hp759088 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 853239 1000) 853239 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl

noncomputable def hp759089 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp759084 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp759090 := nat_lit 136321412446168734903314677760

noncomputable def hp759091 := @hp759089 148880015 268435456 207043 268435456 146944395285523573725 1180591620717411303424 25444733906384406825709 hp743344 hp759090 507836835258337612835 1180591620717411303424

noncomputable def hp759092 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) 11)

noncomputable def hp759093 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) 11) hp759092

noncomputable def hp759094 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) 11)

noncomputable def hp759095 := @hp759094 148880015 536870912 207043 536870912 148880015 536870912 207043 536870912 159858698863247360 148880015 268435456

noncomputable def hp759096 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp759097 := hp759096 BSN.quadSignPos 9 10 11 853239 1000 188 240 536870912 268435456 9007199254740992

noncomputable def hp759098 := hp759097 Bool.false 895600309282 3888 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp759099 := hp759098 Bool.true 329312452 177741 Bool.true 622832796 Bool.true 430071902 28296951008113761 1 Bool.false 214336440

noncomputable def hp759100 := hp759099 Bool.false Bool.false 373628748 Bool.false Bool.true 148880015 207043 BSN.abs_quadSignPos (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 214336440 536870912) BSN.abs_quadSignPos

noncomputable def hp759101 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp759102 := hp759101 BSN.quadSignPos 7 8 9 853239 1000 67 131 536870912 268435456 9007199254740992

noncomputable def hp759103 := hp759102 Bool.false 895600309282 3888 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp759104 := hp759103 Bool.true 597697604 145161 Bool.true 446512568 Bool.true 428308757 28296951008113761 1 Bool.false 396787261

noncomputable def hp759105 := hp759104 Bool.false Bool.false 384299008 Bool.false Bool.true 329312452 177741 BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 396787261 536870912) BSN.abs_quadSignPos

noncomputable def hp759106 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp759107 := hp759106 BSN.quadSignNeg 5 6 7 853239 1000 88 5 536870912 268435456 9007199254740992

noncomputable def hp759108 := hp759107 Bool.false 895600309282 3888 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp759109 := hp759108 Bool.true 684884412 107872 Bool.false 620863753 Bool.false 2783619 28296951008113761 1 Bool.false 216140311

noncomputable def hp759110 := hp759109 Bool.false Bool.false 2783606 Bool.true Bool.true 597697604 145161 BSN.abs_quadSignPos (BSN.cos_quad_nat0 88 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 216140311 536870912) BSN.abs_quadSignNeg

noncomputable def hp759111 := hp759106 BSN.quadSignPos 3 4 5 853239 1000 308 187 536870912 268435456 9007199254740992

noncomputable def hp759112 := hp759111 Bool.false 895600309282 3888 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp759113 := hp759112 Bool.true 917937425 63759 Bool.false 826733354 Bool.false 650413126 28296951008113761 1 Bool.false 16578866

noncomputable def hp759114 := hp759113 Bool.false Bool.false 502586635 Bool.false Bool.true 684884412 107872 BSN.abs_quadSignPos (BSN.cos_quad_nat0 308 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 16578866 536870912) BSN.abs_quadSignPos

noncomputable def hp759115 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp759116 := hp759115 BSN.quadSignNeg 1 2 3 853239 1000 685 465 536870912 268435456 9007199254740992

noncomputable def hp759117 := hp759116 Bool.false 895600309282 3888 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp759118 := hp759117 Bool.true 536870904 3946 Bool.false 413339325 Bool.false 207467165 28296951008113761 1 Bool.false 373697946

noncomputable def hp759119 := hp759118 Bool.true Bool.false 202341929 Bool.true Bool.true 917937425 63759 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 685 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 373697946 536870912) BSN.abs_quadSignNeg

noncomputable def hp759120 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) 1) Bool.true

noncomputable def hp759121 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)))

noncomputable def hp759122 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000))) Bool.true 67108863 67108864

noncomputable def hp759123 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 27987509665) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false 27987509665 16777216

noncomputable def hp759124 := nat_lit 11595480827100630628064024310840015663047744891468000379457

noncomputable def hp759125 := nat_lit 6950953792890942665758067047224195531039926621569024000

noncomputable def hp759126 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) Bool.false hp759124 hp759125 129164221381852396897

noncomputable def hp759127 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 853239 4000) (Real.log (Enclosure.sfrac Bool.false 2912068164484 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1706478))))))

noncomputable def hp759128 := nat_lit 217067650417763778512219438495520000

noncomputable def hp759129 := nat_lit 1111263687932124426393134147606249935680

noncomputable def hp759130 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp759127 (Enclosure.sfrac Bool.false 853239 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 853239 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp759128 hp759129)) Bool.false

noncomputable def hp759131 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 853239 1000) 853239 1000 2912068164484 16000000 1706478

noncomputable def hp759132 := hp759131 4000 2000 hp759128 hp759129 (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl rfl rfl rfl

noncomputable def hp759133 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp759127 (Enclosure.sfrac Bool.false 853239 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 853239 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp759128 hp759129) 30051363195836493368737 18014398509481984000

noncomputable def hp759134 := nat_lit 33394984782049816208824390015219245109577505287427841092836160

noncomputable def hp759135 := @hp759133 129164221381852396897 hp738659 hp759128 hp759129 0 1 hp759134 hp759124 hp759125 129164221381852396897 hp738659

noncomputable def hp759136 := @Enclosure.Real.IsNear.subLit_ff_p (hp759127 (Enclosure.sfrac Bool.false 853239 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 853239 2000) (Real.log Real.pi)) 38848948532584730758561 18014398509481984000 10765503296558107 4356000000000000000000

noncomputable def hp759137 := nat_lit 2016712845723996599719473184768000

noncomputable def hp759138 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 853239 4000) (Real.log (Enclosure.sfrac Bool.false 2912068164484 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1706478))))))

noncomputable def hp759139 := @hp759138 (Enclosure.sfrac Bool.false 853239 2000) 46534242217500680031649 18014398509481984000 10765503296558107 4356000000000000000000 853239 2000 0

noncomputable def hp759140 := nat_lit 77697897065169461517122000

noncomputable def hp759141 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 853239 4000) (Real.log (Enclosure.sfrac Bool.false 2912068164484 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1706478))))) 46541313816263740535649

noncomputable def hp759142 := nat_lit 104785797955352233033697958271964413952

noncomputable def hp759143 := @hp759141 18014398509481984000 3555167765337869 1452000000000000000000 883949845382563 2251799813685248 200000001089 8712000000000000000 hp759142 46534242217500680031649 18014398509481984000 10765503296558107

noncomputable def hp759144 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 853239 4000) (Real.log (Enclosure.sfrac Bool.false 2912068164484 16000000)) 853239 4000 0 1 54546632088153191 4503599627370496

noncomputable def hp759145 := nat_lit 117138000462781072191520768

noncomputable def hp759146 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2912068164484) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp759145 hp617687

noncomputable def hp759147 := BSN.log_rat_reduce_isNear 2912068164484 16000000 17 5824136328968 4194304000000 88122878 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp759148 := nat_lit 103401227692729212355526555920886430937168253724632915666677425097859063497298392391805906774911740218635372796522371763241636331520

noncomputable def hp759149 := nat_lit 926964866570328668588411177745224171076991692846677407267241364845403462387083011130094547657990864497935133831483173724151087104

noncomputable def hp759150 := nat_lit 122056562035206930560708910968645135166412707162495125214438461801274117949783990417361162149084615791390803201511857848320

noncomputable def hp759151 := BSN.log_dyadic_bound 814916164484 5009220164484 6 5 hp759148 268435456 87120000 hp759149 hp759150 88122878 5824136328968

noncomputable def hp759152 := hp759151 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp759153 := @BSN.binarySplit_of_base5 (BSN.artanhP 814916164484) (BSN.artanhQ 5009220164484) 0 5 hp759149 hp759148 hp759150 rfl rfl rfl

noncomputable def hp759154 := hp759147 rfl rfl rfl rfl (hp759152 (hp759153 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp759155 := @hp759144 12500018513 1089000000000000000 46541313816263740535649 18014398509481984000 3555167765337869 1452000000000000000000 (Enclosure.Real.IsNear.const Bool.false 853239 4000) (BSN.isNear_log_sfrac 2912068164484 16000000 54546632088153191 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp759146 1000001481040000 87120000000000000000000 54546632088153191 4503599627370496 12500018513 1089000000000000000 (hp759154 rfl rfl rfl) rfl)) rfl

noncomputable def hp759156 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1706478)))) 1 4

noncomputable def hp759157 := @hp759156 0 1 883949845382563 562949953421312 200000001089 2178000000000000000 883949845382563 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp759158 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1706478))) 884279719003555 562949953421312 1

noncomputable def hp759159 := @hp759158 2000000000000000 19662 33554432 1 10890000 29660434978299724169216 883949845382563 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp759160 := BSN.arctan_dyadic_bound_f 1000 1706478 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp759161 := hp759160 1 19662 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1706478) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1706478) 0 0 rfl)

noncomputable def hp759162 := hp759157 (hp759159 (hp759161 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp759163 := @hp759136 32773559304879 67108864000 2559717 536870912000 hp759137 30051363195836493368737 18014398509481984000 129164221381852396897 hp738659 (@hp759139 1 hp759140 38848948532584730758561 18014398509481984000 10765503296558107 4356000000000000000000 (@hp759143 4356000000000000000000 hp759155 hp759162 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 853239 2000) rfl rfl)

noncomputable def hp759164 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 853239 2000) (Real.log Real.pi) 853239 2000 0 1 38410761 33554432

noncomputable def hp759165 := hp759163 (@hp759164 3 268435456 32773559304879 67108864000 2559717 536870912000 (Enclosure.Real.IsNear.const Bool.false 853239 2000) hd4909 rfl) rfl

noncomputable def hp759166 := @hp759126 hp738659 27987509665 16777216 487 67108864 (@hp759130 hp759124 hp759125 129164221381852396897 hp738659 (hp759132 rfl rfl rfl rfl rfl) (hp759135 (hp759165 rfl) (Enclosure.Real.IsNear.const Bool.true hp759128 hp759129) rfl rfl)) rfl

noncomputable def hp759167 := nat_lit 3797644618153893612748800

noncomputable def hp759168 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 27987509665) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp759167) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp759169 := BSN.sin_reduce_arg_pos_rat_q1 27987509665 16777216 226375608064910080 72057594037927936 265 hp759167 hp619230 rfl rfl rfl rfl

noncomputable def hp759170 := nat_lit 14375710749289972031100238443010494023049350368841856803548885178191245452253645797465330435127849444053034896437463714844755032726439913066496

noncomputable def hp759171 := nat_lit 10240806119660912803901099213220763505362079166394293327350139583514855443594674244244796927980894854232770031785160631353391371865296896

noncomputable def hp759172 := nat_lit 71789264685171846119035629299120877713788677924595649516092394061332314689752716321546483210060289919899427031437814527948329584930722824851456

noncomputable def hp759173 := BSN.sin_dyadic_bound_f 215871103714 137438953472 4 3 67108864 21801270 hp759170 hp737934 hp759171 hp759172 hp737937

noncomputable def hp759174 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215871103714) (BSN.sinEvenQ 137438953472) 0 3 hp759170 hp737934 hp759171 rfl rfl rfl

noncomputable def hp759175 := hp759173 hp759171 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (hp759174 rfl)

noncomputable def hp759176 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215871103714) (BSN.sinOddQ 137438953472) 0 3 hp759172 hp737937 hp759171 rfl rfl rfl

noncomputable def hp759177 := @BSN.sin_arg_round Bool.false 67108863 67108864 hp759167 hp619230 215871103714 137438953472 21801270 21780000 (hp759175 (hp759176 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759178 := hp759168 67108863 67108864 265 1000000000000000 21780000 10890000 hp759169 BSN.pi_near_15 hp759177 rfl rfl

noncomputable def hp759179 := @hp759123 487 67108864 Bool.true 67108863 67108864 1 10890000 hp759166 (Enclosure.sfrac_false_div 27987509665 16777216) (hp759178 rfl rfl) rfl

noncomputable def hp759180 := @hp759120 67108863 67108864 335658679 45675970560000 536870904 536870912 3946 536870912 (@hp759121 Bool.true 67108863 67108864 335658679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000)) (@hp759122 5370538864 730815528960000 67108863 67108864 335658679 45675970560000 (hp759179 rfl) rfl))

noncomputable def hp759181 := @hp759126 hp738659 895600309282 536870912 3888 536870912 (@hp759130 hp759124 hp759125 129164221381852396897 hp738659 (hp759132 rfl rfl rfl rfl rfl) (hp759135 (hp759165 rfl) (Enclosure.Real.IsNear.const Bool.true hp759128 hp759129) rfl rfl)) rfl

noncomputable def hp759182 := hp759119 (BSN.cos_quad_nat1 465 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 202341929 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl rfl (hp759180 rfl) hp759181

noncomputable def hp759183 := nat_lit 7333961822793801687467186246027349889060371898424218065105069940175390625

noncomputable def hp759184 := nat_lit 852027882690488572829314943262278979011870505791818373120269775390625

noncomputable def hp759185 := nat_lit 19206615776459410295200906991592063162525430991244527226480607501775390625

noncomputable def hp759186 := BSN.sin_dyadic_bound_f 413339325 536870912 3 2 536870912 268435456 hp759183 hp708845 hp759184 hp759185 hp708848

noncomputable def hp759187 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 413339325) (BSN.sinEvenQ 536870912) 0 2 hp759183 hp708845 hp759184 rfl rfl rfl

noncomputable def hp759188 := hp759186 hp759184 373697946 rfl rfl rfl rfl rfl rfl rfl rfl (hp759187 rfl)

noncomputable def hp759189 := @BSN.binarySplit_of_base2 (BSN.sinOddP 413339325) (BSN.sinOddQ 536870912) 0 2 hp759185 hp708848 hp759184 rfl rfl rfl

noncomputable def hp759190 := nat_lit 1852667528422331498117589680700625

noncomputable def hp759191 := BSN.sin_dyadic_bound_f 207467165 536870912 2 1 536870912 268435456 hp759190 hp708890 hp759190 hp759190 hp708891

noncomputable def hp759192 := @BSN.binarySplit_of_base (BSN.sinEvenP 207467165) (BSN.sinEvenQ 536870912) 0 1 hp759190 hp708890 hp759190 rfl rfl rfl

noncomputable def hp759193 := hp759191 hp759190 202341929 rfl rfl rfl rfl rfl rfl rfl rfl (hp759192 rfl)

noncomputable def hp759194 := @BSN.binarySplit_of_base (BSN.sinOddP 207467165) (BSN.sinOddQ 536870912) 0 1 hp759190 hp708891 hp759190 rfl rfl rfl

noncomputable def hp759195 := hp759182 hd4911 hd4913 hd4915 hd4917 hd4918 (hp759188 (hp759189 rfl) rfl rfl rfl rfl) (hp759193 (hp759194 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759196 := hp759114 (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 502586635 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl rfl (hp759195 rfl rfl rfl rfl rfl) hp759181

noncomputable def hp759197 := nat_lit 64565193020914945969228895955419899747908783412084416112480333627426310111821982932742730616171320119769656528896

noncomputable def hp759198 := nat_lit 101949596580425441769744162687165326512180263436230353770405775127291784897345804328685582734274354829398016

noncomputable def hp759199 := nat_lit 390823866776391911556724857335007033685089737511940993564831521909479084725745157263490308474324122322238332538880

noncomputable def hp759200 := BSN.cos_dyadic_bound_f 826733354 536870912 4 3 536870912 268435456 hp759197 hp716712 hp759198 hp759199 hp716714

noncomputable def hp759201 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 826733354) (BSN.cosEvenQ 536870912) 0 3 hp759197 hp716712 hp759198 rfl rfl rfl

noncomputable def hp759202 := hp759200 hp759198 16578866 rfl rfl rfl rfl rfl rfl rfl rfl (hp759201 rfl)

noncomputable def hp759203 := @BSN.binarySplit_of_base3 (BSN.cosOddP 826733354) (BSN.cosOddQ 536870912) 0 3 hp759199 hp716714 hp759198 rfl rfl rfl

noncomputable def hp759204 := nat_lit 64139349825576613839923208306147309233633314496444430892368338099063803066060588556690617974342505461788262731776

noncomputable def hp759205 := nat_lit 5731543147495295920533848080467274744870425074942014941863312852340979133912413108701152319469834918629376

noncomputable def hp759206 := nat_lit 320555603335030878266547055186414054602924047713458987582545450079064206091503553693214130545743972938171797671936

noncomputable def hp759207 := BSN.sin_dyadic_bound_f 650413126 536870912 4 3 536870912 268435456 hp759204 hp642702 hp759205 hp759206 hp642705

noncomputable def hp759208 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 650413126) (BSN.sinEvenQ 536870912) 0 3 hp759204 hp642702 hp759205 rfl rfl rfl

noncomputable def hp759209 := hp759207 hp759205 502586635 rfl rfl rfl rfl rfl rfl rfl rfl (hp759208 rfl)

noncomputable def hp759210 := @BSN.binarySplit_of_base3 (BSN.sinOddP 650413126) (BSN.sinOddQ 536870912) 0 3 hp759206 hp642705 hp759205 rfl rfl rfl

noncomputable def hp759211 := hp759196 hd4920 hd4922 hd4924 hd4926 hd4918 (hp759202 (hp759203 rfl) rfl rfl rfl rfl) (hp759209 (hp759210 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759212 := hp759110 (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 2783606 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl rfl (hp759211 rfl rfl rfl rfl rfl) hp759181

noncomputable def hp759213 := nat_lit 20489536004792414101470256629098708289068989798657327430848491502702472030564263618178797962843023166064761988321

noncomputable def hp759214 := nat_lit 3280618045884692732603939289214802795579227145469520278228669755749938125542731714775878837007541143561441

noncomputable def hp759215 := nat_lit 124215038171967158353913412598211063392562155977011222727533464425021250863745115398840424223043632293992127227105

noncomputable def hp759216 := BSN.cos_dyadic_bound_f 620863753 536870912 4 3 536870912 268435456 hp759213 hp716712 hp759214 hp759215 hp716714

noncomputable def hp759217 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 620863753) (BSN.cosEvenQ 536870912) 0 3 hp759213 hp716712 hp759214 rfl rfl rfl

noncomputable def hp759218 := hp759216 hp759214 216140311 rfl rfl rfl rfl rfl rfl rfl rfl (hp759217 rfl)

noncomputable def hp759219 := @BSN.binarySplit_of_base3 (BSN.cosOddP 620863753) (BSN.cosOddQ 536870912) 0 3 hp759215 hp716714 hp759214 rfl rfl rfl

noncomputable def hp759220 := BSN.sin_dyadic_bound_f 2783619 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp759221 := hp759220 1 2783606 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 2783619) (BSN.sinEvenQ 536870912) 0 0 rfl)

noncomputable def hp759222 := hp759221 (@BSN.binarySplit_of_le (BSN.sinOddP 2783619) (BSN.sinOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp759223 := hp759212 hd4928 hd4930 hd4932 hd4934 hd4918 (hp759218 (hp759219 rfl) rfl rfl rfl rfl) hp759222 rfl

noncomputable def hp759224 := hp759105 (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 384299008 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl rfl (hp759223 rfl rfl rfl rfl rfl) hp759181

noncomputable def hp759225 := nat_lit 9987682875601033838243988572599561040251844985452675458085205708101386240

noncomputable def hp759226 := nat_lit 1580045160174177710240618694694596231476538170558153585415164186853376

noncomputable def hp759227 := nat_lit 26155658886790997098155770974159820997237203423909436808227723731582058496

noncomputable def hp759228 := BSN.sin_dyadic_bound_f 446512568 536870912 3 2 536870912 268435456 hp759225 hp708845 hp759226 hp759227 hp708848

noncomputable def hp759229 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 446512568) (BSN.sinEvenQ 536870912) 0 2 hp759225 hp708845 hp759226 rfl rfl rfl

noncomputable def hp759230 := hp759228 hp759226 396787261 rfl rfl rfl rfl rfl rfl rfl rfl (hp759229 rfl)

noncomputable def hp759231 := @BSN.binarySplit_of_base2 (BSN.sinOddP 446512568) (BSN.sinOddQ 536870912) 0 2 hp759227 hp708848 hp759226 rfl rfl rfl

noncomputable def hp759232 := nat_lit 8455655338690164748028053511862891074614500335084302722911297427268743265

noncomputable def hp759233 := nat_lit 1132545427344820739564862095854922837443853290822274284559263745224801

noncomputable def hp759234 := nat_lit 22143930337306158916018939897199997225110687019892794877830778263449677921

noncomputable def hp759235 := BSN.sin_dyadic_bound_f 428308757 536870912 3 2 536870912 268435456 hp759232 hp708845 hp759233 hp759234 hp708848

noncomputable def hp759236 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 428308757) (BSN.sinEvenQ 536870912) 0 2 hp759232 hp708845 hp759233 rfl rfl rfl

noncomputable def hp759237 := hp759235 hp759233 384299008 rfl rfl rfl rfl rfl rfl rfl rfl (hp759236 rfl)

noncomputable def hp759238 := @BSN.binarySplit_of_base2 (BSN.sinOddP 428308757) (BSN.sinOddQ 536870912) 0 2 hp759234 hp708848 hp759233 rfl rfl rfl

noncomputable def hp759239 := hp759224 hd4936 hd4938 hd4940 hd4942 hd4918 (hp759230 (hp759231 rfl) rfl rfl rfl rfl) (hp759237 (hp759238 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759240 := hp759100 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 373628748 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl rfl (hp759239 rfl rfl rfl rfl rfl) hp759181

noncomputable def hp759241 := nat_lit 20750983284419914743795649259644258403549529690621239176664318862418966856305809563072927034340671021212233629696

noncomputable def hp759242 := nat_lit 3407671118735243111506407845048380048726615664748615515087408026452624811319948401054422833697354537762816

noncomputable def hp759243 := nat_lit 125798890034571070190576931737565257133107963136854348900067660940346857726663606954016566792900308824840711700480

noncomputable def hp759244 := BSN.cos_dyadic_bound_f 622832796 536870912 4 3 536870912 268435456 hp759241 hp716712 hp759242 hp759243 hp716714

noncomputable def hp759245 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 622832796) (BSN.cosEvenQ 536870912) 0 3 hp759241 hp716712 hp759242 rfl rfl rfl

noncomputable def hp759246 := hp759244 hp759242 214336440 rfl rfl rfl rfl rfl rfl rfl rfl (hp759245 rfl)

noncomputable def hp759247 := @BSN.binarySplit_of_base3 (BSN.cosOddP 622832796) (BSN.cosOddQ 536870912) 0 3 hp759243 hp716714 hp759242 rfl rfl rfl

noncomputable def hp759248 := nat_lit 4775946988252004890657294164087838155944835802067003850282243310357217536

noncomputable def hp759249 := nat_lit 1170384487270642682993440408943568307333933586775346385872270862745856

noncomputable def hp759250 := nat_lit 14325500195781473386605895611445627331219839539027460858074985389346160896

noncomputable def hp759251 := BSN.cos_dyadic_bound_f 430071902 536870912 3 2 536870912 268435456 hp759248 hp708868 hp759249 hp759250 hp708870

noncomputable def hp759252 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 430071902) (BSN.cosEvenQ 536870912) 0 2 hp759248 hp708868 hp759249 rfl rfl rfl

noncomputable def hp759253 := hp759251 hp759249 373628748 rfl rfl rfl rfl rfl rfl rfl rfl (hp759252 rfl)

noncomputable def hp759254 := @BSN.binarySplit_of_base2 (BSN.cosOddP 430071902) (BSN.cosOddQ 536870912) 0 2 hp759250 hp708870 hp759249 rfl rfl rfl

noncomputable def hp759255 := hp759240 hd4944 hd4946 hd4961 hd4963 hd4918 (hp759246 (hp759247 rfl) rfl rfl rfl rfl) (hp759253 (hp759254 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759256 := @hp759095 207043 268435456 (hp759255 rfl rfl rfl rfl rfl) (hp759255 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp759257 := @hp759093 Bool.true 148880015 268435456 207043 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 853239 1000)) (Enclosure.sfrac Bool.false 853239 1000) 11) hp759256

noncomputable def hp759258 := @Enclosure.Real.IsNear.mulLit_tf hp759084 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1))) 2457351 8388608 1

noncomputable def hp759259 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp759083 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759260 := @hp759259 1 1 0 1 2457351 8388608 1 33554432 2457351 8388608 1

noncomputable def hp759261 := @Enclosure.Real.IsNear.of_eq (hp759083 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759262 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 853239 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759263 := @hp759261 (@Inv.inv Real Real.instInv (Real.sqrt hp759085)) Bool.false 2457351 8388608 1 33554432 (hp759262 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 853239 1000) 853239 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000))))

noncomputable def hp759264 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp759085)) Bool.false 19658808 67108864 2 67108864 2457351 8388608

noncomputable def hp759265 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp759085) Bool.false 229088132 67108864 6 67108864 57272033 16777216 3 33554432

noncomputable def hp759266 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 853239 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759267 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 853239 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759268 := @hp759267 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 853239 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9113195759973

noncomputable def hp759269 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 853239 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 853239 1000 0

noncomputable def hp759270 := @hp759269 1 10680707 67108864 1 67108864 9113195759973 67108864000 853239 67108864000 (Enclosure.Real.IsNear.const Bool.false 853239 1000) hd4949

noncomputable def hp759271 := @hp759268 67108864000 853239 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 853239 1000) 853239 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000))) (hp759270 rfl)

noncomputable def hp759272 := @hp759266 9113195759973 67108864000 853239 67108864000 391016674 391016711 33554432 hp759271 rfl rfl rfl

noncomputable def hp759273 := @Enclosure.Real.IsNear.recentre' hp759085 Bool.false 782033385 67108864 37 67108864 782033385 67108864 37 67108864 (hp759272 rfl rfl rfl)

noncomputable def hp759274 := @Enclosure.Real.IsNear.sqrt_image hp759085 782033385 67108864 37 67108864 114544063 114544069 33554432 (hp759273 rfl) rfl rfl

noncomputable def hp759275 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp759085) 57272033 16777216 3 33554432 9829403 9829405 33554432 (hp759265 (hp759274 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp759276 := @hp759260 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp759263 (@hp759264 1 33554432 (hp759275 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp759277 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759278 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp759279 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1))) (hp759277 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759278 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp759280 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 853239 1000) 853239 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl

noncomputable def hp759281 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759282 := @hp759281 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759278 (Enclosure.sfrac Bool.false 1 16)))) 29362995

noncomputable def hp759283 := @hp759282 16777216 367 33554432 2036505 8388608 185185277 22837985280000 59797886132475 140737488355328 12910045932783389 766315624094760960000

noncomputable def hp759284 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759285 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759286 := @hp759284 (@Neg.neg Real Real.instNeg hp759285) Bool.true 29362995 16777216 367 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759287 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759288 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp759289 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp759290 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 275428963) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp759291 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1))) Bool.false 38763180532953275556955

noncomputable def hp759292 := nat_lit 998484790511177032413947331

noncomputable def hp759293 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp759294 := @Enclosure.Real.IsNear.subLit_ff_p hp759085 (Enclosure.sfrac Bool.false 11 1) 782033385 67108864 37 67108864 11 1 0

noncomputable def hp759295 := @hp759293 500000000000000 43835881 67108864 37 67108864 38763180532953275556955 9444732965739290427392 hp759292 hp738031 hd4948 (@hp759294 1 43835881 43835881 67108864 37 67108864 (hp759273 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759296 := @hp759290 275428963 67108864 233 67108864 Bool.true 38344178 67108864 1 10890000 (@hp759291 9444732965739290427392 hp759292 hp738031 275428963 67108864 233 67108864 (hp759295 rfl) rfl) (Enclosure.sfrac_false_div 275428963 67108864)

noncomputable def hp759297 := nat_lit 9309877015192240700522496

noncomputable def hp759298 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 275428963) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp759297) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp759299 := BSN.sin_reduce_arg_pos_rat_q2 275428963 67108864 226375608064910080 72057594037927936 0 hp759297 hp617687 rfl rfl rfl rfl

noncomputable def hp759300 := nat_lit 183749906081973770826768269245529740827304115004589503183491590976184491012433257699662554241

noncomputable def hp759301 := nat_lit 93867045189098779383827446262300724942516756419782783355518957248980627314489285094597761

noncomputable def hp759302 := nat_lit 551061984155543114921537152844064621032027311500928943983763735014055511782670794528798467201

noncomputable def hp759303 := BSN.cos_dyadic_bound_f 132301309679 137438953472 3 2 67108864 21801270 hp759300 hp746621 hp759301 hp759302 hp746624

noncomputable def hp759304 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 132301309679) (BSN.cosEvenQ 137438953472) 0 2 hp759300 hp746621 hp759301 rfl rfl rfl

noncomputable def hp759305 := hp759303 hp759301 38344178 rfl rfl rfl rfl rfl rfl rfl rfl (hp759304 rfl)

noncomputable def hp759306 := @BSN.binarySplit_of_base2 (BSN.cosOddP 132301309679) (BSN.cosOddQ 137438953472) 0 2 hp759302 hp746624 hp759301 rfl rfl rfl

noncomputable def hp759307 := @BSN.cos_arg_round Bool.false 38344178 67108864 hp759297 hp617687 132301309679 137438953472 21801270 21780000 (hp759305 (hp759306 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759308 := hp759298 38344178 67108864 0 1000000000000000 21780000 10890000 hp759299 BSN.pi_near_15 hp759307 rfl rfl

noncomputable def hp759309 := @hp759288 19172089 33554432 162779929 45675970560000 (@hp759289 38344178 67108864 2604478864 730815528960000 19172089 33554432 162779929 45675970560000 (hp759296 (hp759308 rfl rfl) rfl rfl) rfl)

noncomputable def hp759310 := @hp759287 19172089 33554432 162779929 45675970560000 58725623 58726357 33554432 hp759309 rfl rfl rfl

noncomputable def hp759311 := @Enclosure.Real.IsNear.recentre' hp759285 Bool.false 117451980 67108864 734 67108864 29362995 16777216 367 33554432 (hp759310 rfl rfl rfl)

noncomputable def hp759312 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759278 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp759313 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759278 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 60935415)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp759314 := nat_lit 1151037454881583597359199628845

noncomputable def hp759315 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759278 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp759314

noncomputable def hp759316 := nat_lit 30909227564727014628534130659766689

noncomputable def hp759317 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759278 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp759318 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp759319 := @hp759318 (Enclosure.sfrac Bool.false 1 16) 1020191713303023 4503599627370496 5726884531 4503599627370496 1 16 0

noncomputable def hp759320 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)) 1921584463046161

noncomputable def hp759321 := @hp759320 4503599627370496 3243856563 4503599627370496 43835881 67108864 37 67108864 68463906941979561295872 1020191713303023 4503599627370496 5726884531

noncomputable def hp759322 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)) 43835881 67108864 37

noncomputable def hp759323 := @hp759322 67108864 43835881 67108864 37 67108864 1921584463046161 4503599627370496 3243856563 4503599627370496 (@hp759294 1 43835881 43835881 67108864 37 67108864 (hp759273 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759324 := hp759323 (@hp759294 1 43835881 43835881 67108864 37 67108864 (hp759273 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759325 := @hp759321 4503599627370496 (hp759324 rfl) (@hp759294 1 43835881 43835881 67108864 37 67108864 (hp759273 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759326 := @hp759317 500000000000000 1301666690013679 4503599627370496 5726884531 4503599627370496 hp759314 hp627574 hp759316 hp742826 hd4948 (@hp759319 1 20826667040218864 1301666690013679 4503599627370496 5726884531 4503599627370496 (hp759325 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp759327 := @hp759313 60935415 33554432 269 33554432 Bool.true 8146020 33554432 1 10890000 (@hp759315 hp627574 hp759316 hp742826 60935415 33554432 269 33554432 (hp759326 rfl) rfl) (Enclosure.sfrac_true_div 60935415 33554432)

noncomputable def hp759328 := nat_lit 445050250873772958907141925560465750246550097267380128489973033127921221027757561308175647804390625

noncomputable def hp759329 := nat_lit 2620820510213438433330989827608593960257051825333732714022271993326594639918335341347900390625

noncomputable def hp759330 := nat_lit 2688380255889256025907205533492659182330189454441651056145704742979501683397036157713276034517990625

noncomputable def hp759331 := BSN.cos_dyadic_bound_t 60935415 33554432 4 3 33554432 10890000 hp759328 hp681868 hp759329 hp759330 hp681871

noncomputable def hp759332 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 60935415) (BSN.cosEvenQ 33554432) 0 3 hp759328 hp681868 hp759329 rfl rfl rfl

noncomputable def hp759333 := hp759331 hp759329 8146020 rfl rfl rfl rfl rfl rfl rfl rfl (hp759332 rfl)

noncomputable def hp759334 := @BSN.binarySplit_of_base3 (BSN.cosOddP 60935415) (BSN.cosOddQ 33554432) 0 3 hp759330 hp681871 hp759329 rfl rfl rfl

noncomputable def hp759335 := hp759327 (BSN.cos_neg_of_bound 60935415 33554432 Bool.true 8146020 33554432 1 10890000 (hp759333 (hp759334 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp759336 := hp759283 (hp759286 (@Enclosure.Real.IsNear.neg hp759285 Bool.false 29362995 16777216 367 33554432 (hp759311 rfl))) (@hp759312 8146020 33554432 2962964432 365407764480000 2036505 8388608 185185277 22837985280000 (hp759335 rfl) rfl)

noncomputable def hp759337 := @hp759258 33554432 59797886132475 140737488355328 12910045932783389 766315624094760960000 146944395285523573725 1180591620717411303424 25444733906384406825709 hp743344 (hp759276 rfl) (@hp759279 Bool.false 59797886132475 140737488355328 12910045932783389 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759085 (Enclosure.sfrac Bool.false 11 1)) (hp759280 rfl (hp759088 rfl rfl))) (hp759336 rfl))

noncomputable def hp759338 := @hp759082 hp759080 hp743344 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 853239 1000))) (@hp759087 hp759080 hp743344 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 853239 1000) 11 (hp759088 rfl rfl)) (@hp759091 hp759080 hp743344 hp759257 (hp759337 rfl) rfl rfl))

theorem hd5046 : hp759081 hp743344 := hp759338

noncomputable def hp759339 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 854518 1000)) Bool.false 2886959732546382594731 2361183241434822606848 800074579515153408265423

noncomputable def hp759340 := nat_lit 1028531419969008727542988800

noncomputable def hp759341 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 854518 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 854518 1000)) Bool.false 2886959732546382594731 2361183241434822606848

noncomputable def hp759342 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 854518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759343 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp759342 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759344 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 854518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759345 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp759343 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp759346 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 854518 1000)) hp759345 Bool.false 2886959732546382594731 2361183241434822606848

noncomputable def hp759347 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 854518 1000) 854518 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl

noncomputable def hp759348 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp759343 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp759349 := nat_lit 96870294032465781620884897792

noncomputable def hp759350 := @hp759348 36801239 33554432 51839 67108864 297302759934311269035 2361183241434822606848 5573866766187140156623 hp759340 hp759349 2886959732546382594731 2361183241434822606848

noncomputable def hp759351 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) 11)

noncomputable def hp759352 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) 11) hp759351

noncomputable def hp759353 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) 11)

noncomputable def hp759354 := @hp759353 294409912 536870912 207356 536870912 294409912 536870912 207356 536870912 316120235914559488 36801239 33554432

noncomputable def hp759355 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp759356 := hp759355 BSN.quadSignPos 9 10 11 854518 1000 188 240 536870912 268435456 9007199254740992

noncomputable def hp759357 := hp759356 Bool.false 897286710614 3894 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp759358 := hp759357 Bool.false 76625431 178010 Bool.true 517519697 Bool.true 390204292 28296951008113761 1 Bool.false 306164140

noncomputable def hp759359 := hp759358 Bool.false Bool.false 401201756 Bool.false Bool.false 294409912 207356 BSN.abs_quadSignPos (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 306164140 536870912) BSN.abs_quadSignPos

noncomputable def hp759360 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp759361 := hp759360 BSN.quadSignPos 7 8 9 854518 1000 67 131 536870912 268435456 9007199254740992

noncomputable def hp759362 := hp759361 Bool.false 897286710614 3894 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp759363 := hp759362 Bool.true 69031962 145381 Bool.true 187976190 Bool.true 250649013 28296951008113761 1 Bool.false 184158900

noncomputable def hp759364 := hp759363 Bool.false Bool.false 241642168 Bool.false Bool.false 76625431 178010 BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 184158900 536870912) BSN.abs_quadSignPos

noncomputable def hp759365 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp759366 := hp759365 BSN.quadSignNeg 5 6 7 854518 1000 89 5 536870912 268435456 9007199254740992

noncomputable def hp759367 := hp759366 Bool.false 897286710614 3894 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp759368 := hp759367 Bool.false 147379741 108036 Bool.false 233624450 Bool.false 353010401 28296951008113761 1 Bool.false 226320614

noncomputable def hp759369 := hp759368 Bool.true Bool.false 328117336 Bool.true Bool.true 69031962 145381 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 226320614 536870912) BSN.abs_quadSignNeg

noncomputable def hp759370 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp759371 := hp759370 BSN.quadSignPos 3 4 5 854518 1000 309 188 536870912 268435456 9007199254740992

noncomputable def hp759372 := hp759371 Bool.false 897286710614 3894 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp759373 := hp759372 Bool.false 228557241 63857 Bool.false 717909877 Bool.false 388366370 28296951008113761 1 Bool.false 522291025

noncomputable def hp759374 := hp759373 Bool.true Bool.false 402420684 Bool.false Bool.false 147379741 108036 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 309 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 522291025 536870912) BSN.abs_quadSignPos

noncomputable def hp759375 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp759376 := hp759375 BSN.quadSignNeg 1 2 3 854518 1000 686 466 536870912 268435456 9007199254740992

noncomputable def hp759377 := hp759376 Bool.false 897286710614 3894 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp759378 := hp759377 Bool.false 536870824 3954 Bool.false 780470834 Bool.false 296182844 28296951008113761 1 Bool.false 62700604

noncomputable def hp759379 := hp759378 Bool.true Bool.false 457222542 Bool.true Bool.false 228557241 63857 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 686 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 62700604 536870912) BSN.abs_quadSignNeg

noncomputable def hp759380 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) 1) Bool.false

noncomputable def hp759381 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)))

noncomputable def hp759382 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000))) Bool.false 67108853 67108864

noncomputable def hp759383 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 56080419413) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 56080419413 33554432

noncomputable def hp759384 := nat_lit 824216691250407749167895041508582246403522616779894255161

noncomputable def hp759385 := nat_lit 493151142753561181608026559234952231364733853237248000

noncomputable def hp759386 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) Bool.false hp759384 hp759385 21559537294235045119

noncomputable def hp759387 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 854518 4000) (Real.log (Enclosure.sfrac Bool.false 2920805049296 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1709036))))))

noncomputable def hp759388 := nat_lit 218699449985367358363065015792640000

noncomputable def hp759389 := nat_lit 1121295878769072218365241858998506885120

noncomputable def hp759390 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp759387 (Enclosure.sfrac Bool.false 854518 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 854518 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp759388 hp759389)) Bool.false

noncomputable def hp759391 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 854518 1000) 854518 1000 2920805049296 16000000 1709036

noncomputable def hp759392 := hp759391 4000 2000 hp759388 hp759389 (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl rfl rfl rfl

noncomputable def hp759393 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp759387 (Enclosure.sfrac Bool.false 854518 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 854518 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp759388 hp759389) 15053974714691923530269 9007199254740992000

noncomputable def hp759394 := nat_lit 16879957836808350702958490450095764406344143191652234345697280

noncomputable def hp759395 := @hp759393 21559537294235045119 hp740893 hp759388 hp759389 0 1 hp759394 hp759384 hp759385 21559537294235045119 hp740893

noncomputable def hp759396 := @Enclosure.Real.IsNear.subLit_ff_p (hp759387 (Enclosure.sfrac Bool.false 854518 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 854518 2000) (Real.log Real.pi)) 19459361146153348944413 9007199254740992000 1796915136706039 726000000000000000000

noncomputable def hp759397 := nat_lit 505127570893849549045611102208000

noncomputable def hp759398 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 854518 4000) (Real.log (Enclosure.sfrac Bool.false 2920805049296 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1709036))))))

noncomputable def hp759399 := @hp759398 (Enclosure.sfrac Bool.false 854518 2000) 23307768092534730445341 9007199254740992000 1796915136706039 726000000000000000000 854518 2000 0

noncomputable def hp759400 := nat_lit 38918722292306697888826000

noncomputable def hp759401 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 854518 4000) (Real.log (Enclosure.sfrac Bool.false 2920805049296 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1709036))))) 23311303893862417753341

noncomputable def hp759402 := nat_lit 52484427848188674182697509489442029568

noncomputable def hp759403 := @hp759401 9007199254740992000 5340745409845867 2178000000000000000000 883950331921827 2251799813685248 200000001089 8712000000000000000 hp759402 23307768092534730445341 9007199254740992000 1796915136706039

noncomputable def hp759404 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 854518 4000) (Real.log (Enclosure.sfrac Bool.false 2920805049296 16000000)) 854518 4000 0 1 54560123704503399 4503599627370496

noncomputable def hp759405 := nat_lit 117166973488278233312919552

noncomputable def hp759406 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2920805049296) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp759405 hp617687

noncomputable def hp759407 := BSN.log_rat_reduce_isNear 2920805049296 16000000 17 5841610098592 4194304000000 88927041 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp759408 := nat_lit 105218932321958715693927568212020856343602246762372739647895099014183849450408436274313491825813257022251093071961590516021744107520

noncomputable def hp759409 := nat_lit 960522532753912740350236332796251321616662351631144797276519091609962867762916097052891614908287892548078080040674282255683682304

noncomputable def hp759410 := nat_lit 135792228137691583088346882491679084121213780065200205656988562216746275753534314520291623343290333495287966990252449464320

noncomputable def hp759411 := BSN.log_dyadic_bound 823653049296 5017957049296 6 5 hp759408 268435456 87120000 hp759409 hp759410 88927041 5841610098592

noncomputable def hp759412 := hp759411 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp759413 := @BSN.binarySplit_of_base5 (BSN.artanhP 823653049296) (BSN.artanhQ 5017957049296) 0 5 hp759409 hp759408 hp759410 rfl rfl rfl

noncomputable def hp759414 := hp759407 rfl rfl rfl rfl (hp759412 (hp759413 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp759415 := @hp759404 12500018513 1089000000000000000 23311303893862417753341 9007199254740992000 5340745409845867 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 854518 4000) (BSN.isNear_log_sfrac 2920805049296 16000000 54560123704503399 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp759406 1000001481040000 87120000000000000000000 54560123704503399 4503599627370496 12500018513 1089000000000000000 (hp759414 rfl rfl rfl) rfl)) rfl

noncomputable def hp759416 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1709036)))) 1 4

noncomputable def hp759417 := @hp759416 0 1 883950331921827 562949953421312 200000001089 2178000000000000000 883950331921827 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp759418 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1709036))) 884279719003555 562949953421312 1

noncomputable def hp759419 := @hp759418 2000000000000000 19633 33554432 1 10890000 29660451303848373387264 883950331921827 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp759420 := BSN.arctan_dyadic_bound_f 1000 1709036 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp759421 := hp759420 1 19633 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1709036) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1709036) 0 0 rfl)

noncomputable def hp759422 := hp759417 (hp759419 (hp759421 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp759423 := @hp759396 16411343334099 33554432000 1281777 268435456000 hp759397 15053974714691923530269 9007199254740992000 21559537294235045119 hp740893 (@hp759399 1 hp759400 19459361146153348944413 9007199254740992000 1796915136706039 726000000000000000000 (@hp759403 726000000000000000000 hp759415 hp759422 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 854518 2000) rfl rfl)

noncomputable def hp759424 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 854518 2000) (Real.log Real.pi) 854518 2000 0 1 38410761 33554432

noncomputable def hp759425 := hp759423 (@hp759424 3 268435456 16411343334099 33554432000 1281777 268435456000 (Enclosure.Real.IsNear.const Bool.false 854518 2000) hd4909 rfl) rfl

noncomputable def hp759426 := @hp759386 hp740893 56080419413 33554432 61 8388608 (@hp759390 hp759384 hp759385 21559537294235045119 hp740893 (hp759392 rfl rfl rfl rfl rfl) (hp759395 (hp759425 rfl) (Enclosure.Real.IsNear.const Bool.true hp759388 hp759389) rfl rfl)) rfl

noncomputable def hp759427 := nat_lit 7593232126518252699385856

noncomputable def hp759428 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 56080419413) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp759427) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp759429 := BSN.sin_reduce_arg_pos_rat_q3 56080419413 33554432 226375608064910080 72057594037927936 265 hp759427 hp619237 rfl rfl rfl rfl

noncomputable def hp759430 := nat_lit 14360111735735542729349952204086465636848444628715052292285438201010508374280579868157203478946098126153055810301840232634938592083324720031681

noncomputable def hp759431 := nat_lit 10207572188621341551168038605957159765805433703056511001717557748310994001977952438237370450122523429826759280209060636120027897759442881

noncomputable def hp759432 := nat_lit 71711462942921243759412992542838314678567349845408485116448881754266477932842806742242162702191786005158219233233115586523205498587561255675841

noncomputable def hp759433 := BSN.sin_dyadic_bound_f 215812637137 137438953472 4 3 67108864 21801270 hp759430 hp737934 hp759431 hp759432 hp737937

noncomputable def hp759434 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215812637137) (BSN.sinEvenQ 137438953472) 0 3 hp759430 hp737934 hp759431 rfl rfl rfl

noncomputable def hp759435 := hp759433 hp759431 67108853 rfl rfl rfl rfl rfl rfl rfl rfl (hp759434 rfl)

noncomputable def hp759436 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215812637137) (BSN.sinOddQ 137438953472) 0 3 hp759432 hp737937 hp759431 rfl rfl rfl

noncomputable def hp759437 := @BSN.sin_arg_round Bool.false 67108853 67108864 hp759427 hp619237 215812637137 137438953472 21801270 21780000 (hp759435 (hp759436 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759438 := hp759428 67108853 67108864 265 1000000000000000 21780000 10890000 hp759429 BSN.pi_near_15 hp759437 rfl rfl

noncomputable def hp759439 := @hp759383 61 8388608 Bool.false 67108853 67108864 1 10890000 hp759426 (Enclosure.sfrac_false_div 56080419413 33554432) (hp759438 rfl rfl) rfl

noncomputable def hp759440 := @hp759380 67108853 67108864 42042413 5709496320000 536870824 536870912 3954 536870912 (@hp759381 Bool.false 67108853 67108864 42042413 5709496320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000)) (@hp759382 672678608 91351941120000 67108853 67108864 42042413 5709496320000 (hp759439 rfl) rfl))

noncomputable def hp759441 := @hp759386 hp740893 897286710614 536870912 3894 536870912 (@hp759390 hp759384 hp759385 21559537294235045119 hp740893 (hp759392 rfl rfl rfl rfl rfl) (hp759395 (hp759425 rfl) (Enclosure.Real.IsNear.const Bool.true hp759388 hp759389) rfl rfl)) rfl

noncomputable def hp759442 := hp759379 (BSN.cos_quad_nat2 466 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 457222542 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl rfl (hp759440 rfl) hp759441

noncomputable def hp759443 := nat_lit 51246582115277495034279589333961290286511269925258383305913742669134589537208217921755583775558556015622677467136

noncomputable def hp759444 := nat_lit 51083440398601167712084907398324835785094674677489807259626210525547302244351471707508366885936424419987456

noncomputable def hp759445 := nat_lit 310346121378959892678690369598394253241234720885741091139083321028564032187756233820682713623182603668008604405760

noncomputable def hp759446 := BSN.cos_dyadic_bound_f 780470834 536870912 4 3 536870912 268435456 hp759443 hp716712 hp759444 hp759445 hp716714

noncomputable def hp759447 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 780470834) (BSN.cosEvenQ 536870912) 0 3 hp759443 hp716712 hp759444 rfl rfl rfl

noncomputable def hp759448 := hp759446 hp759444 62700604 rfl rfl rfl rfl rfl rfl rfl rfl (hp759447 rfl)

noncomputable def hp759449 := @BSN.binarySplit_of_base3 (BSN.cosOddP 780470834) (BSN.cosOddQ 536870912) 0 3 hp759445 hp716714 hp759444 rfl rfl rfl

noncomputable def hp759450 := nat_lit 1074118805291616166196126066025361316428688638307707781175282002936528896

noncomputable def hp759451 := nat_lit 59221471166896637001102903088725690992859412251700496032399129378816

noncomputable def hp759452 := nat_lit 3222237972932514705314375992269906497904080196098619942533781210550829056

noncomputable def hp759453 := BSN.cos_dyadic_bound_f 296182844 536870912 3 2 536870912 268435456 hp759450 hp708868 hp759451 hp759452 hp708870

noncomputable def hp759454 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 296182844) (BSN.cosEvenQ 536870912) 0 2 hp759450 hp708868 hp759451 rfl rfl rfl

noncomputable def hp759455 := hp759453 hp759451 457222542 rfl rfl rfl rfl rfl rfl rfl rfl (hp759454 rfl)

noncomputable def hp759456 := @BSN.binarySplit_of_base2 (BSN.cosOddP 296182844) (BSN.cosOddQ 536870912) 0 2 hp759452 hp708870 hp759451 rfl rfl rfl

noncomputable def hp759457 := hp759442 hd4911 hd4913 hd4915 hd4917 hd4918 (hp759448 (hp759449 rfl) rfl rfl rfl rfl) (hp759455 (hp759456 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759458 := hp759374 (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 402420684 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl rfl (hp759457 rfl rfl rfl rfl rfl) hp759441

noncomputable def hp759459 := nat_lit 95235051669013366923116283053937915027058121038981843223410832987613161011587821773212176317690005642069470693521

noncomputable def hp759460 := nat_lit 18743001534606982394015482071375021274248361461498133581683407679396368613899674274290110846026328318232721

noncomputable def hp759461 := nat_lit 475864267825658254081609832597886913147607403315019418541479337482524586324652224081875480639865935761121338280081

noncomputable def hp759462 := BSN.sin_dyadic_bound_f 717909877 536870912 4 3 536870912 268435456 hp759459 hp642702 hp759460 hp759461 hp642705

noncomputable def hp759463 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 717909877) (BSN.sinEvenQ 536870912) 0 3 hp759459 hp642702 hp759460 rfl rfl rfl

noncomputable def hp759464 := hp759462 hp759460 522291025 rfl rfl rfl rfl rfl rfl rfl rfl (hp759463 rfl)

noncomputable def hp759465 := @BSN.binarySplit_of_base3 (BSN.sinOddP 717909877) (BSN.sinOddQ 536870912) 0 3 hp759461 hp642705 hp759460 rfl rfl rfl

noncomputable def hp759466 := nat_lit 3175601690882376024054111426713258820506412961423790891288132826032800000

noncomputable def hp759467 := nat_lit 517526897432444232911451751152455616245734158754326726031632100000000

noncomputable def hp759468 := nat_lit 9525770018852263183696511376637471550286747415953864020412335213898400000

noncomputable def hp759469 := BSN.cos_dyadic_bound_f 388366370 536870912 3 2 536870912 268435456 hp759466 hp708868 hp759467 hp759468 hp708870

noncomputable def hp759470 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 388366370) (BSN.cosEvenQ 536870912) 0 2 hp759466 hp708868 hp759467 rfl rfl rfl

noncomputable def hp759471 := hp759469 hp759467 402420684 rfl rfl rfl rfl rfl rfl rfl rfl (hp759470 rfl)

noncomputable def hp759472 := @BSN.binarySplit_of_base2 (BSN.cosOddP 388366370) (BSN.cosOddQ 536870912) 0 2 hp759468 hp708870 hp759467 rfl rfl rfl

noncomputable def hp759473 := hp759458 hd4920 hd4922 hd4924 hd4926 hd4918 (hp759464 (hp759465 rfl) rfl rfl rfl rfl) (hp759471 (hp759472 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759474 := hp759369 (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 328117336 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl rfl (hp759473 rfl rfl rfl rfl rfl) hp759441

noncomputable def hp759475 := nat_lit 748410034131102489663075028193225661470356279013217453325365148900000000

noncomputable def hp759476 := nat_lit 8874549900954192929569003159223742774494368200678862539062500000000

noncomputable def hp759477 := nat_lit 1960107149643524023281405771643809417791202977962292231027083574500000000

noncomputable def hp759478 := BSN.sin_dyadic_bound_f 233624450 536870912 3 2 536870912 268435456 hp759475 hp708845 hp759476 hp759477 hp708848

noncomputable def hp759479 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 233624450) (BSN.sinEvenQ 536870912) 0 2 hp759475 hp708845 hp759476 rfl rfl rfl

noncomputable def hp759480 := hp759478 hp759476 226320614 rfl rfl rfl rfl rfl rfl rfl rfl (hp759479 rfl)

noncomputable def hp759481 := @BSN.binarySplit_of_base2 (BSN.sinOddP 233624450) (BSN.sinOddQ 536870912) 0 2 hp759477 hp708848 hp759476 rfl rfl rfl

noncomputable def hp759482 := nat_lit 3901558603601326101806660347793861226173891060691540682037994845309470465

noncomputable def hp759483 := nat_lit 241157077446369158477079909879233758108529197317879590443657436563201

noncomputable def hp759484 := nat_lit 10217977326544750430856099924367927309132777064063139505048315816151320321

noncomputable def hp759485 := BSN.sin_dyadic_bound_f 353010401 536870912 3 2 536870912 268435456 hp759482 hp708845 hp759483 hp759484 hp708848

noncomputable def hp759486 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 353010401) (BSN.sinEvenQ 536870912) 0 2 hp759482 hp708845 hp759483 rfl rfl rfl

noncomputable def hp759487 := hp759485 hp759483 328117336 rfl rfl rfl rfl rfl rfl rfl rfl (hp759486 rfl)

noncomputable def hp759488 := @BSN.binarySplit_of_base2 (BSN.sinOddP 353010401) (BSN.sinOddQ 536870912) 0 2 hp759484 hp708848 hp759483 rfl rfl rfl

noncomputable def hp759489 := hp759474 hd4928 hd4930 hd4932 hd4934 hd4918 (hp759480 (hp759481 rfl) rfl rfl rfl rfl) (hp759487 (hp759488 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759490 := hp759364 (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 241642168 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl rfl (hp759489 rfl rfl rfl rfl rfl) hp759441

noncomputable def hp759491 := nat_lit 1248565617651065450993432439210000

noncomputable def hp759492 := BSN.sin_dyadic_bound_f 187976190 536870912 2 1 536870912 268435456 hp759491 hp708890 hp759491 hp759491 hp708891

noncomputable def hp759493 := @BSN.binarySplit_of_base (BSN.sinEvenP 187976190) (BSN.sinEvenQ 536870912) 0 1 hp759491 hp708890 hp759491 rfl rfl rfl

noncomputable def hp759494 := hp759492 hp759491 184158900 rfl rfl rfl rfl rfl rfl rfl rfl (hp759493 rfl)

noncomputable def hp759495 := @BSN.binarySplit_of_base (BSN.sinOddP 187976190) (BSN.sinOddQ 536870912) 0 1 hp759491 hp708891 hp759491 rfl rfl rfl

noncomputable def hp759496 := nat_lit 991589917418744821973625367472536516198118167988245150112745136451203425

noncomputable def hp759497 := nat_lit 15578584359326578965802311061479768830752938023400703519790167994721

noncomputable def hp759498 := nat_lit 2596995989817273719279264663448258003750297792355270839632443316147827041

noncomputable def hp759499 := BSN.sin_dyadic_bound_f 250649013 536870912 3 2 536870912 268435456 hp759496 hp708845 hp759497 hp759498 hp708848

noncomputable def hp759500 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 250649013) (BSN.sinEvenQ 536870912) 0 2 hp759496 hp708845 hp759497 rfl rfl rfl

noncomputable def hp759501 := hp759499 hp759497 241642168 rfl rfl rfl rfl rfl rfl rfl rfl (hp759500 rfl)

noncomputable def hp759502 := @BSN.binarySplit_of_base2 (BSN.sinOddP 250649013) (BSN.sinOddQ 536870912) 0 2 hp759498 hp708848 hp759497 rfl rfl rfl

noncomputable def hp759503 := hp759490 hd4936 hd4938 hd4940 hd4942 hd4918 (hp759494 (hp759495 rfl) rfl rfl rfl rfl) (hp759501 (hp759502 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759504 := hp759359 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 401201756 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl rfl (hp759503 rfl rfl rfl rfl rfl) hp759441

noncomputable def hp759505 := nat_lit 9885881839925664710729134922809168770442302451703546808690425288161760928695605541886160712273023060352455811521

noncomputable def hp759506 := nat_lit 369081779885044070169175124925094407450596820530362892109270160419913495217768348669332934957958316040641

noncomputable def hp759507 := nat_lit 59953809403990190414926921834992419790649134859611869225727415831568459828668488498270226779316204445613639213505

noncomputable def hp759508 := BSN.cos_dyadic_bound_f 517519697 536870912 4 3 536870912 268435456 hp759505 hp716712 hp759506 hp759507 hp716714

noncomputable def hp759509 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 517519697) (BSN.cosEvenQ 536870912) 0 3 hp759505 hp716712 hp759506 rfl rfl rfl

noncomputable def hp759510 := hp759508 hp759506 306164140 rfl rfl rfl rfl rfl rfl rfl rfl (hp759509 rfl)

noncomputable def hp759511 := @BSN.binarySplit_of_base3 (BSN.cosOddP 517519697) (BSN.cosOddQ 536870912) 0 3 hp759507 hp716714 hp759506 rfl rfl rfl

noncomputable def hp759512 := nat_lit 3236153243898264977086538140023382077601045006900096937995164665732202496

noncomputable def hp759513 := nat_lit 537447858059518772697500755440906353481017545304879430030817367228416

noncomputable def hp759514 := nat_lit 9707384835978675893714219418559264420096172985609681055125432362462150656

noncomputable def hp759515 := BSN.cos_dyadic_bound_f 390204292 536870912 3 2 536870912 268435456 hp759512 hp708868 hp759513 hp759514 hp708870

noncomputable def hp759516 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 390204292) (BSN.cosEvenQ 536870912) 0 2 hp759512 hp708868 hp759513 rfl rfl rfl

noncomputable def hp759517 := hp759515 hp759513 401201756 rfl rfl rfl rfl rfl rfl rfl rfl (hp759516 rfl)

noncomputable def hp759518 := @BSN.binarySplit_of_base2 (BSN.cosOddP 390204292) (BSN.cosOddQ 536870912) 0 2 hp759514 hp708870 hp759513 rfl rfl rfl

noncomputable def hp759519 := hp759504 hd4944 hd4946 hd4961 hd4963 hd4918 (hp759510 (hp759511 rfl) rfl rfl rfl rfl) (hp759517 (hp759518 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759520 := @hp759354 51839 67108864 (hp759519 rfl rfl rfl rfl rfl) (hp759519 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp759521 := @hp759352 Bool.false 36801239 33554432 51839 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 854518 1000)) (Enclosure.sfrac Bool.false 854518 1000) 11) hp759520

noncomputable def hp759522 := @Enclosure.Real.IsNear.mulLit_tf hp759343 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1))) 2456431 8388608 1

noncomputable def hp759523 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp759342 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759524 := @hp759523 1 1 0 1 2456431 8388608 1 33554432 2456431 8388608 1

noncomputable def hp759525 := @Enclosure.Real.IsNear.of_eq (hp759342 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759526 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 854518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759527 := @hp759525 (@Inv.inv Real Real.instInv (Real.sqrt hp759344)) Bool.false 2456431 8388608 1 33554432 (hp759526 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 854518 1000) 854518 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000))))

noncomputable def hp759528 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp759344)) Bool.false 19651448 67108864 2 67108864 2456431 8388608

noncomputable def hp759529 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp759344) Bool.false 229173934 67108864 6 67108864 114586967 33554432 3 33554432

noncomputable def hp759530 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 854518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759531 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 854518 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759532 := @hp759531 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 854518 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4563428192113

noncomputable def hp759533 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 854518 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 854518 1000 0

noncomputable def hp759534 := @hp759533 1 10680707 67108864 1 67108864 4563428192113 33554432000 427259 33554432000 (Enclosure.Real.IsNear.const Bool.false 854518 1000) hd4949

noncomputable def hp759535 := @hp759532 33554432000 427259 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 854518 1000) 854518 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000))) (hp759534 rfl)

noncomputable def hp759536 := @hp759530 4563428192113 33554432000 427259 33554432000 391309630 391309667 33554432 hp759535 rfl rfl rfl

noncomputable def hp759537 := @Enclosure.Real.IsNear.recentre' hp759344 Bool.false 782619297 67108864 37 67108864 782619297 67108864 37 67108864 (hp759536 rfl rfl rfl)

noncomputable def hp759538 := @Enclosure.Real.IsNear.sqrt_image hp759344 782619297 67108864 37 67108864 114586964 114586970 33554432 (hp759537 rfl) rfl rfl

noncomputable def hp759539 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp759344) 114586967 33554432 3 33554432 9825723 9825725 33554432 (hp759529 (hp759538 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp759540 := @hp759524 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp759527 (@hp759528 1 33554432 (hp759539 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp759541 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759542 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp759543 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1))) (hp759541 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759542 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp759544 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 854518 1000) 854518 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl

noncomputable def hp759545 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759546 := @hp759545 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759542 (Enclosure.sfrac Bool.false 1 16)))) 127701095

noncomputable def hp759547 := @hp759546 67108864 867 67108864 947763 4194304 186546527 22837985280000 121030372900485 281474976710656 14148285644515487 766315624094760960000

noncomputable def hp759548 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759549 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759550 := @hp759548 (@Neg.neg Real Real.instNeg hp759549) Bool.true 127701095 67108864 867 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759551 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759552 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp759553 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp759554 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 279110357) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp759555 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1))) Bool.false 39281290631674086474115

noncomputable def hp759556 := nat_lit 199696958103241995634123047

noncomputable def hp759557 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp759558 := @Enclosure.Real.IsNear.subLit_ff_p hp759344 (Enclosure.sfrac Bool.false 11 1) 782619297 67108864 37 67108864 11 1 0

noncomputable def hp759559 := @hp759557 500000000000000 44421793 67108864 37 67108864 39281290631674086474115 9444732965739290427392 hp759556 hp645312 hd4948 (@hp759558 1 44421793 44421793 67108864 37 67108864 (hp759537 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759560 := @hp759554 279110357 67108864 233 67108864 Bool.true 35266727 67108864 1 10890000 (@hp759555 9444732965739290427392 hp759556 hp645312 279110357 67108864 233 67108864 (hp759559 rfl) rfl) (Enclosure.sfrac_false_div 279110357 67108864)

noncomputable def hp759561 := nat_lit 9840421803883568052568064

noncomputable def hp759562 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 279110357) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp759561) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp759563 := BSN.sin_reduce_arg_pos_rat_q2 279110357 67108864 226375608064910080 72057594037927936 0 hp759561 hp617687 rfl rfl rfl rfl

noncomputable def hp759564 := nat_lit 229383020032353697342988062958118826903288975834256373802866731327690884327840362209188406401

noncomputable def hp759565 := nat_lit 146241728821808310638925102718808940718673919169003765959201290340507516804216968807867521

noncomputable def hp759566 := nat_lit 687856576639417475407686338668918862828429579664431113876681791402391637949912652689949484161

noncomputable def hp759567 := BSN.cos_dyadic_bound_f 139840804591 137438953472 3 2 67108864 21801270 hp759564 hp746621 hp759565 hp759566 hp746624

noncomputable def hp759568 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 139840804591) (BSN.cosEvenQ 137438953472) 0 2 hp759564 hp746621 hp759565 rfl rfl rfl

noncomputable def hp759569 := hp759567 hp759565 35266727 rfl rfl rfl rfl rfl rfl rfl rfl (hp759568 rfl)

noncomputable def hp759570 := @BSN.binarySplit_of_base2 (BSN.cosOddP 139840804591) (BSN.cosOddQ 137438953472) 0 2 hp759566 hp746624 hp759565 rfl rfl rfl

noncomputable def hp759571 := @BSN.cos_arg_round Bool.false 35266727 67108864 hp759561 hp617687 139840804591 137438953472 21801270 21780000 (hp759569 (hp759570 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759572 := hp759562 35266727 67108864 0 1000000000000000 21780000 10890000 hp759563 BSN.pi_near_15 hp759571 rfl rfl

noncomputable def hp759573 := @hp759552 35266727 67108864 162779929 45675970560000 (@hp759553 35266727 67108864 2604478864 730815528960000 35266727 67108864 162779929 45675970560000 (hp759560 (hp759572 rfl rfl) rfl rfl) rfl)

noncomputable def hp759574 := @hp759551 35266727 67108864 162779929 45675970560000 63850114 63850981 33554432 hp759573 rfl rfl rfl

noncomputable def hp759575 := @Enclosure.Real.IsNear.recentre' hp759549 Bool.false 127701095 67108864 867 67108864 127701095 67108864 867 67108864 (hp759574 rfl rfl rfl)

noncomputable def hp759576 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759542 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp759577 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759542 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 120710669)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp759578 := nat_lit 1140080042844655924226257049245

noncomputable def hp759579 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759542 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp759578

noncomputable def hp759580 := nat_lit 155716186264243354621416520588714101

noncomputable def hp759581 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759542 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp759582 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp759583 := @hp759582 (Enclosure.sfrac Bool.false 1 16) 1007800371738303 4503599627370496 5770242019 4503599627370496 1 16 0

noncomputable def hp759584 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)) 1973295693334849

noncomputable def hp759585 := @hp759584 4503599627370496 3287214051 4503599627370496 44421793 67108864 37 67108864 67632338086135219617792 1007800371738303 4503599627370496 5770242019

noncomputable def hp759586 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)) 44421793 67108864 37

noncomputable def hp759587 := @hp759586 67108864 44421793 67108864 37 67108864 1973295693334849 4503599627370496 3287214051 4503599627370496 (@hp759558 1 44421793 44421793 67108864 37 67108864 (hp759537 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759588 := hp759587 (@hp759558 1 44421793 44421793 67108864 37 67108864 (hp759537 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759589 := @hp759585 4503599627370496 (hp759588 rfl) (@hp759558 1 44421793 44421793 67108864 37 67108864 (hp759537 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759590 := @hp759581 500000000000000 1289275348448959 4503599627370496 5770242019 4503599627370496 hp759578 hp627574 hp759580 hp738055 hd4948 (@hp759583 1 20628405575183344 1289275348448959 4503599627370496 5770242019 4503599627370496 (hp759589 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp759591 := @hp759577 120710669 67108864 271 33554432 Bool.true 7582104 33554432 1 10890000 (@hp759579 hp627574 hp759580 hp738055 120710669 67108864 271 33554432 (hp759590 rfl) rfl) (Enclosure.sfrac_true_div 120710669 67108864)

noncomputable def hp759592 := nat_lit 1754072282886891850425014988237998845327092042871745921906923999364672141364147238274046252562560965041

noncomputable def hp759593 := nat_lit 9570792099124491794458516391041391076895685999831080054162112816796062011899300595005856536189361

noncomputable def hp759594 := nat_lit 10597393467192543734670879961566297997500199655496821169078200741030002488199837769246605755024638073265

noncomputable def hp759595 := BSN.cos_dyadic_bound_t 120710669 67108864 4 3 33554432 10890000 hp759592 hp745658 hp759593 hp759594 hp745661

noncomputable def hp759596 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 120710669) (BSN.cosEvenQ 67108864) 0 3 hp759592 hp745658 hp759593 rfl rfl rfl

noncomputable def hp759597 := hp759595 hp759593 7582104 rfl rfl rfl rfl rfl rfl rfl rfl (hp759596 rfl)

noncomputable def hp759598 := @BSN.binarySplit_of_base3 (BSN.cosOddP 120710669) (BSN.cosOddQ 67108864) 0 3 hp759594 hp745661 hp759593 rfl rfl rfl

noncomputable def hp759599 := hp759591 (BSN.cos_neg_of_bound 120710669 67108864 Bool.true 7582104 33554432 1 10890000 (hp759597 (hp759598 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp759600 := hp759547 (hp759550 (@Enclosure.Real.IsNear.neg hp759549 Bool.false 127701095 67108864 867 67108864 (hp759575 rfl))) (@hp759576 7582104 33554432 2984744432 365407764480000 947763 4194304 186546527 22837985280000 (hp759599 rfl) rfl)

noncomputable def hp759601 := @hp759522 33554432 121030372900485 281474976710656 14148285644515487 766315624094760960000 297302759934311269035 2361183241434822606848 5573866766187140156623 hp759340 (hp759540 rfl) (@hp759543 Bool.false 121030372900485 281474976710656 14148285644515487 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759344 (Enclosure.sfrac Bool.false 11 1)) (hp759544 rfl (hp759347 rfl rfl))) (hp759600 rfl))

noncomputable def hp759602 := @hp759341 800074579515153408265423 hp759340 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 854518 1000))) (@hp759346 800074579515153408265423 hp759340 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 854518 1000) 11 (hp759347 rfl rfl)) (@hp759350 800074579515153408265423 hp759340 hp759521 (hp759601 rfl) rfl rfl))

theorem hd5047 : hp759339 hp759340 := hp759602

noncomputable def hp759603 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 855797 1000)) Bool.true 85716660984155317815201 75557863725914323419136 101239264006647441378349

noncomputable def hp759604 := nat_lit 129865078278915243376640000

noncomputable def hp759605 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 855797 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 855797 1000)) Bool.true 85716660984155317815201 75557863725914323419136

noncomputable def hp759606 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 855797 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759607 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp759606 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759608 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 855797 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759609 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp759607 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp759610 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 855797 1000)) hp759609 Bool.true 85716660984155317815201 75557863725914323419136

noncomputable def hp759611 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 855797 1000) 855797 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl

noncomputable def hp759612 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp759607 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp759613 := nat_lit 359521734032486586133568815104

noncomputable def hp759614 := @hp759612 5292789 4194304 207657 268435456 9629749288447322798175 75557863725914323419136 777898127451875298349 hp759604 hp759613 85716660984155317815201 75557863725914323419136

noncomputable def hp759615 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) 11)

noncomputable def hp759616 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) 11) hp759615

noncomputable def hp759617 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) 11)

noncomputable def hp759618 := @hp759617 338738496 536870912 207657 536870912 338738496 536870912 207657 536870912 363717690554056704 5292789 4194304

noncomputable def hp759619 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp759620 := hp759619 BSN.quadSignPos 9 10 11 855797 1000 188 240 536870912 268435456 9007199254740992

noncomputable def hp759621 := hp759620 Bool.false 898973626136 3899 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp759622 := hp759621 Bool.true 589701699 178267 Bool.true 411692407 Bool.true 349822491 28296951008113761 1 Bool.false 386605599

noncomputable def hp759623 := hp759622 Bool.false Bool.false 426875410 Bool.false Bool.true 338738496 207657 BSN.abs_quadSignPos (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 386605599 536870912) BSN.abs_quadSignPos

noncomputable def hp759624 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp759625 := hp759624 BSN.quadSignPos 7 8 9 855797 1000 66 131 536870912 268435456 9007199254740992

noncomputable def hp759626 := hp759625 Bool.false 898973626136 3899 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp759627 := hp759626 Bool.true 588731497 145590 Bool.true 772240478 Bool.true 72475078 28296951008113761 1 Bool.false 70866950

noncomputable def hp759628 := hp759627 Bool.true Bool.false 72255150 Bool.false Bool.true 589701699 178267 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 70866950 536870912) BSN.abs_quadSignPos

noncomputable def hp759629 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp759630 := hp759629 BSN.quadSignNeg 5 6 7 855797 1000 89 5 536870912 268435456 9007199254740992

noncomputable def hp759631 := hp759630 Bool.false 898973626136 3899 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp759632 := hp759631 Bool.true 182306420 108190 Bool.false 690214193 Bool.false 703751373 28296951008113761 1 Bool.false 515188425

noncomputable def hp759633 := hp759632 Bool.true Bool.false 518832569 Bool.true Bool.true 588731497 145590 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 89 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 515188425 536870912) BSN.abs_quadSignNeg

noncomputable def hp759634 := hp759624 BSN.quadSignNeg 3 4 5 855797 1000 310 189 536870912 268435456 9007199254740992

noncomputable def hp759635 := hp759634 Bool.false 898973626136 3899 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp759636 := hp759635 Bool.true 12909751 63945 Bool.false 609600590 Bool.false 126833805 28296951008113761 1 Bool.false 226402057

noncomputable def hp759637 := hp759636 Bool.true Bool.false 125657277 Bool.true Bool.true 182306420 108190 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 310 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 226402057 536870912) BSN.abs_quadSignNeg

noncomputable def hp759638 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp759639 := hp759638 BSN.quadSignPos 1 2 3 855797 1000 688 467 536870912 268435456 9007199254740992

noncomputable def hp759640 := hp759639 Bool.false 898973626136 3899 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp759641 := hp759640 Bool.true 536870904 3954 Bool.false 304801677 Bool.false 385412713 28296951008113761 1 Bool.false 452646500

noncomputable def hp759642 := hp759641 Bool.false Bool.false 353150854 Bool.false Bool.true 12909751 63945 BSN.abs_quadSignPos (BSN.cos_quad_nat0 688 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 452646500 536870912) BSN.abs_quadSignPos

noncomputable def hp759643 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) 1) Bool.true

noncomputable def hp759644 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)))

noncomputable def hp759645 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000))) Bool.true 67108863 67108864

noncomputable def hp759646 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 112371703267) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 112371703267 67108864

noncomputable def hp759647 := nat_lit 106650858289015147794506953206861348945419325815503171522739

noncomputable def hp759648 := nat_lit 63692350799296909568109259120339642871007483342618624000

noncomputable def hp759649 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) Bool.false hp759647 hp759648 11777293286269831321

noncomputable def hp759650 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 855797 4000) (Real.log (Enclosure.sfrac Bool.false 2929555020836 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1711594))))))

noncomputable def hp759651 := nat_lit 220341048435866250669827215403360000

noncomputable def hp759652 := nat_lit 1131403429598110747067161325680111667520

noncomputable def hp759653 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp759650 (Enclosure.sfrac Bool.false 855797 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 855797 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp759651 hp759652)) Bool.false

noncomputable def hp759654 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 855797 1000) 855797 1000 2929555020836 16000000 1711594

noncomputable def hp759655 := hp759654 4000 2000 hp759651 hp759652 (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl rfl rfl rfl

noncomputable def hp759656 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp759650 (Enclosure.sfrac Bool.false 855797 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 855797 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp759651 hp759652) 30164552916300696959699 18014398509481984000

noncomputable def hp759657 := nat_lit 34128274652484847294242225026195631662534184260961014887276480

noncomputable def hp759658 := @hp759656 11777293286269831321 hp743892 hp759651 hp759652 0 1 hp759657 hp759647 hp759648 11777293286269831321 hp743892

noncomputable def hp759659 := @Enclosure.Real.IsNear.subLit_ff_p (hp759650 (Enclosure.sfrac Bool.false 855797 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 855797 2000) (Real.log Real.pi)) 38988513305398161226451 18014398509481984000 981588940355851 396000000000000000000

noncomputable def hp759660 := nat_lit 2024308879280826855373653671936000

noncomputable def hp759661 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 855797 4000) (Real.log (Enclosure.sfrac Bool.false 2929555020836 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1711594))))))

noncomputable def hp759662 := @hp759661 (Enclosure.sfrac Bool.false 855797 2000) 1867873896240309518283 720575940379279360 981588940355851 396000000000000000000 855797 2000 0

noncomputable def hp759663 := nat_lit 3119081064431852898116080

noncomputable def hp759664 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 855797 4000) (Real.log (Enclosure.sfrac Bool.false 2929555020836 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1711594))))) 1868156760502217067403

noncomputable def hp759665 := nat_lit 4206078091541467227982659097863389184

noncomputable def hp759666 := @hp759664 720575940379279360 10697478343369861 4356000000000000000000 883950818461091 2251799813685248 200000001089 8712000000000000000 hp759665 1867873896240309518283 720575940379279360 981588940355851

noncomputable def hp759667 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 855797 4000) (Real.log (Enclosure.sfrac Bool.false 2929555020836 16000000)) 855797 4000 0 1 54573595154639975 4503599627370496

noncomputable def hp759668 := nat_lit 117195903207161377639628800

noncomputable def hp759669 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2929555020836) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp759668 hp617687

noncomputable def hp759670 := BSN.log_rat_reduce_isNear 2929555020836 16000000 17 5859110041672 4194304000000 89730002 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp759671 := nat_lit 107068132303056526253689203205190332749682559936984962078771050362020416874860279748318804334270252603842172545424537751554249195520

noncomputable def hp759672 := nat_lit 995101086458858845190680177154301124402878879942954834645369625477014530712135241474880760368885577215713482967296960583412219904

noncomputable def hp759673 := nat_lit 150927467462264270476812291996833899175446860173021360074881467962717849800791155519942365379263859730285466247987404472320

noncomputable def hp759674 := BSN.log_dyadic_bound 832403020836 5026707020836 6 5 hp759671 268435456 87120000 hp759672 hp759673 89730002 5859110041672

noncomputable def hp759675 := hp759674 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp759676 := @BSN.binarySplit_of_base5 (BSN.artanhP 832403020836) (BSN.artanhQ 5026707020836) 0 5 hp759672 hp759671 hp759673 rfl rfl rfl

noncomputable def hp759677 := hp759670 rfl rfl rfl rfl (hp759675 (hp759676 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp759678 := @hp759667 12500018513 1089000000000000000 1868156760502217067403 720575940379279360 10697478343369861 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 855797 4000) (BSN.isNear_log_sfrac 2929555020836 16000000 54573595154639975 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp759669 1000001481040000 87120000000000000000000 54573595154639975 4503599627370496 12500018513 1089000000000000000 (hp759677 rfl rfl rfl) rfl)) rfl

noncomputable def hp759679 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1711594)))) 1 4

noncomputable def hp759680 := @hp759679 0 1 883950818461091 562949953421312 200000001089 2178000000000000000 883950818461091 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp759681 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1711594))) 884279719003555 562949953421312 1

noncomputable def hp759682 := @hp759681 2000000000000000 19604 33554432 1 10890000 29660467629397022605312 883950818461091 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp759683 := BSN.arctan_dyadic_bound_f 1000 1711594 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp759684 := hp759683 1 19604 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1711594) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1711594) 0 0 rfl)

noncomputable def hp759685 := hp759680 (hp759682 (hp759684 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp759686 := @hp759659 32871814031517 67108864000 2567391 536870912000 hp759660 30164552916300696959699 18014398509481984000 11777293286269831321 hp743892 (@hp759662 1 hp759663 38988513305398161226451 18014398509481984000 981588940355851 396000000000000000000 (@hp759666 396000000000000000000 hp759678 hp759685 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 855797 2000) rfl rfl)

noncomputable def hp759687 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 855797 2000) (Real.log Real.pi) 855797 2000 0 1 38410761 33554432

noncomputable def hp759688 := hp759686 (@hp759687 3 268435456 32871814031517 67108864000 2567391 536870912000 (Enclosure.Real.IsNear.const Bool.false 855797 2000) hd4909 rfl) rfl

noncomputable def hp759689 := @hp759649 hp743892 112371703267 67108864 61 8388608 (@hp759653 hp759647 hp759648 11777293286269831321 hp743892 (hp759655 rfl rfl rfl rfl rfl) (hp759658 (hp759688 rfl) (Enclosure.Real.IsNear.const Bool.true hp759651 hp759652) rfl rfl)) rfl

noncomputable def hp759690 := nat_lit 15191613037171011982721024

noncomputable def hp759691 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 112371703267) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp759690) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp759692 := BSN.sin_reduce_arg_pos_rat_q1 112371703267 67108864 226375608064910080 72057594037927936 266 hp759690 hp617687 rfl rfl rfl rfl

noncomputable def hp759693 := nat_lit 14379635293563719807898927537750340614555131217772128577002105429944188167301519002913150043563848680442326206183999971659248344836236902400000

noncomputable def hp759694 := nat_lit 10249178738882596480631967829849643504090593961883063801892735925986999166238436599596306571213626785802349759994815657803776000000000000

noncomputable def hp759695 := nat_lit 71808838735045848777525442598315190435160815808105504871124288851015484040016481651293362357548496459447143752735480716819733592263360512000000

noncomputable def hp759696 := BSN.sin_dyadic_bound_f 215885805760 137438953472 4 3 67108864 21801270 hp759693 hp737934 hp759694 hp759695 hp737937

noncomputable def hp759697 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215885805760) (BSN.sinEvenQ 137438953472) 0 3 hp759693 hp737934 hp759694 rfl rfl rfl

noncomputable def hp759698 := hp759696 hp759694 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (hp759697 rfl)

noncomputable def hp759699 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215885805760) (BSN.sinOddQ 137438953472) 0 3 hp759695 hp737937 hp759694 rfl rfl rfl

noncomputable def hp759700 := @BSN.sin_arg_round Bool.false 67108863 67108864 hp759690 hp617687 215885805760 137438953472 21801270 21780000 (hp759698 (hp759699 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759701 := hp759691 67108863 67108864 266 1000000000000000 21780000 10890000 hp759692 BSN.pi_near_15 hp759700 rfl rfl

noncomputable def hp759702 := @hp759646 61 8388608 Bool.true 67108863 67108864 1 10890000 hp759689 (Enclosure.sfrac_false_div 112371703267 67108864) (hp759701 rfl rfl) rfl

noncomputable def hp759703 := @hp759643 67108863 67108864 42042413 5709496320000 536870904 536870912 3954 536870912 (@hp759644 Bool.true 67108863 67108864 42042413 5709496320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000)) (@hp759645 672678608 91351941120000 67108863 67108864 42042413 5709496320000 (hp759702 rfl) rfl))

noncomputable def hp759704 := @hp759649 hp743892 898973626136 536870912 3899 536870912 (@hp759653 hp759647 hp759648 11777293286269831321 hp743892 (hp759655 rfl rfl rfl rfl rfl) (hp759658 (hp759688 rfl) (Enclosure.Real.IsNear.const Bool.true hp759651 hp759652) rfl rfl)) rfl

noncomputable def hp759705 := hp759642 (BSN.cos_quad_nat3 467 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 353150854 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl rfl (hp759703 rfl) hp759704

noncomputable def hp759706 := nat_lit 1204717014200590053648199201449433707713139088915008309317006961875401761

noncomputable def hp759707 := nat_lit 74497005670392318117305731727856167643415672721710613188006393986081

noncomputable def hp759708 := nat_lit 3614002048590429376308362992884845410804130435399581506724644872838233121

noncomputable def hp759709 := BSN.cos_dyadic_bound_f 304801677 536870912 3 2 536870912 268435456 hp759706 hp708868 hp759707 hp759708 hp708870

noncomputable def hp759710 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 304801677) (BSN.cosEvenQ 536870912) 0 2 hp759706 hp708868 hp759707 rfl rfl rfl

noncomputable def hp759711 := hp759709 hp759707 452646500 rfl rfl rfl rfl rfl rfl rfl rfl (hp759710 rfl)

noncomputable def hp759712 := @BSN.binarySplit_of_base2 (BSN.cosOddP 304801677) (BSN.cosOddQ 536870912) 0 2 hp759708 hp708870 hp759707 rfl rfl rfl

noncomputable def hp759713 := nat_lit 5543749142807027417551189051303831267945557647150706001779465030247785025

noncomputable def hp759714 := nat_lit 486864700283972182173333955746802791110391594734821182779611924537921

noncomputable def hp759715 := nat_lit 14518554735932231091005785927010253735338472251384183151316955707533042241

noncomputable def hp759716 := BSN.sin_dyadic_bound_f 385412713 536870912 3 2 536870912 268435456 hp759713 hp708845 hp759714 hp759715 hp708848

noncomputable def hp759717 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 385412713) (BSN.sinEvenQ 536870912) 0 2 hp759713 hp708845 hp759714 rfl rfl rfl

noncomputable def hp759718 := hp759716 hp759714 353150854 rfl rfl rfl rfl rfl rfl rfl rfl (hp759717 rfl)

noncomputable def hp759719 := @BSN.binarySplit_of_base2 (BSN.sinOddP 385412713) (BSN.sinOddQ 536870912) 0 2 hp759715 hp708848 hp759714 rfl rfl rfl

noncomputable def hp759720 := hp759705 hd4911 hd4913 hd4915 hd4917 hd4918 (hp759711 (hp759712 rfl) rfl rfl rfl rfl) (hp759718 (hp759719 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759721 := hp759637 (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 125657277 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl rfl (hp759720 rfl rfl rfl rfl rfl) hp759704

noncomputable def hp759722 := nat_lit 19041264694761601188779325439753520315982145421662601937502999244771313461639491180560173985272214535779904000000

noncomputable def hp759723 := nat_lit 2633568044967730805818245228012327324948222184931073684058225553768718667910046208767044396881000000000000

noncomputable def hp759724 := nat_lit 115440869130429733433069583936762975739224757472339103885552730157095845428857633983356872666047858654662617600000

noncomputable def hp759725 := BSN.cos_dyadic_bound_f 609600590 536870912 4 3 536870912 268435456 hp759722 hp716712 hp759723 hp759724 hp716714

noncomputable def hp759726 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 609600590) (BSN.cosEvenQ 536870912) 0 3 hp759722 hp716712 hp759723 rfl rfl rfl

noncomputable def hp759727 := hp759725 hp759723 226402057 rfl rfl rfl rfl rfl rfl rfl rfl (hp759726 rfl)

noncomputable def hp759728 := @BSN.binarySplit_of_base3 (BSN.cosOddP 609600590) (BSN.cosOddQ 536870912) 0 3 hp759724 hp716714 hp759723 rfl rfl rfl

noncomputable def hp759729 := nat_lit 258785587591254415165349822900625

noncomputable def hp759730 := BSN.sin_dyadic_bound_f 126833805 536870912 2 1 536870912 268435456 hp759729 hp708890 hp759729 hp759729 hp708891

noncomputable def hp759731 := @BSN.binarySplit_of_base (BSN.sinEvenP 126833805) (BSN.sinEvenQ 536870912) 0 1 hp759729 hp708890 hp759729 rfl rfl rfl

noncomputable def hp759732 := hp759730 hp759729 125657277 rfl rfl rfl rfl rfl rfl rfl rfl (hp759731 rfl)

noncomputable def hp759733 := @BSN.binarySplit_of_base (BSN.sinOddP 126833805) (BSN.sinOddQ 536870912) 0 1 hp759729 hp708891 hp759729 rfl rfl rfl

noncomputable def hp759734 := hp759721 hd4920 hd4922 hd4924 hd4926 hd4918 (hp759727 (hp759728 rfl) rfl rfl rfl rfl) (hp759732 (hp759733 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759735 := hp759633 (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 518832569 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl rfl (hp759734 rfl rfl rfl rfl rfl) hp759704

noncomputable def hp759736 := nat_lit 81355295738994318448686571860244028776131240135197503126143385392235007525715769171779035394043534917917507342401

noncomputable def hp759737 := nat_lit 11689787762953796500938195657897346933948625286502946063147434836960539741871710899246859934361950492840001

noncomputable def hp759738 := nat_lit 406549469441033485036542963136063522231468539970219026591311621618026640534390390263454251025703137862605016682561

noncomputable def hp759739 := BSN.sin_dyadic_bound_f 690214193 536870912 4 3 536870912 268435456 hp759736 hp642702 hp759737 hp759738 hp642705

noncomputable def hp759740 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 690214193) (BSN.sinEvenQ 536870912) 0 3 hp759736 hp642702 hp759737 rfl rfl rfl

noncomputable def hp759741 := hp759739 hp759737 515188425 rfl rfl rfl rfl rfl rfl rfl rfl (hp759740 rfl)

noncomputable def hp759742 := @BSN.binarySplit_of_base3 (BSN.sinOddP 690214193) (BSN.sinOddQ 536870912) 0 3 hp759738 hp642705 hp759737 rfl rfl rfl

noncomputable def hp759743 := nat_lit 87934436402475700498970874012289020195854749611470705447391676656859123239678875376847264280413474348209662713521

noncomputable def hp759744 := nat_lit 14758120834677452424285729654092317742411173739988518549095078128591894051273026267552627009008571063852721

noncomputable def hp759745 := nat_lit 439407006299197024741034634212206633890754183281518812375869825231077685261420950108933654762638096735786688700081

noncomputable def hp759746 := BSN.sin_dyadic_bound_f 703751373 536870912 4 3 536870912 268435456 hp759743 hp642702 hp759744 hp759745 hp642705

noncomputable def hp759747 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 703751373) (BSN.sinEvenQ 536870912) 0 3 hp759743 hp642702 hp759744 rfl rfl rfl

noncomputable def hp759748 := hp759746 hp759744 518832569 rfl rfl rfl rfl rfl rfl rfl rfl (hp759747 rfl)

noncomputable def hp759749 := @BSN.binarySplit_of_base3 (BSN.sinOddP 703751373) (BSN.sinOddQ 536870912) 0 3 hp759745 hp642705 hp759744 rfl rfl rfl

noncomputable def hp759750 := hp759735 hd4928 hd4930 hd4932 hd4934 hd4918 (hp759741 (hp759742 rfl) rfl rfl rfl rfl) (hp759748 (hp759749 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759751 := hp759628 (BSN.cos_quad_nat3 131 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 72255150 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl rfl (hp759750 rfl rfl rfl rfl rfl) hp759704

noncomputable def hp759752 := nat_lit 49113467042484290691175167907295176750487727689036717184049997173232226732600226775743854353098443065963937796096

noncomputable def hp759753 := nat_lit 44981169625199437411340470294529396590260593874871953414724912800306119518348951488574551632796488002441216

noncomputable def hp759754 := nat_lit 297449940435548169462883110840976684268215869363007080996253564505984558445015397092290206300890155144318788833280

noncomputable def hp759755 := BSN.cos_dyadic_bound_f 772240478 536870912 4 3 536870912 268435456 hp759752 hp716712 hp759753 hp759754 hp716714

noncomputable def hp759756 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 772240478) (BSN.cosEvenQ 536870912) 0 3 hp759752 hp716712 hp759753 rfl rfl rfl

noncomputable def hp759757 := hp759755 hp759753 70866950 rfl rfl rfl rfl rfl rfl rfl rfl (hp759756 rfl)

noncomputable def hp759758 := @BSN.binarySplit_of_base3 (BSN.cosOddP 772240478) (BSN.cosOddQ 536870912) 0 3 hp759754 hp716714 hp759753 rfl rfl rfl

noncomputable def hp759759 := nat_lit 27590194730019540233387661815056

noncomputable def hp759760 := BSN.sin_dyadic_bound_f 72475078 536870912 2 1 536870912 268435456 hp759759 hp708890 hp759759 hp759759 hp708891

noncomputable def hp759761 := @BSN.binarySplit_of_base (BSN.sinEvenP 72475078) (BSN.sinEvenQ 536870912) 0 1 hp759759 hp708890 hp759759 rfl rfl rfl

noncomputable def hp759762 := hp759760 hp759759 72255150 rfl rfl rfl rfl rfl rfl rfl rfl (hp759761 rfl)

noncomputable def hp759763 := @BSN.binarySplit_of_base (BSN.sinOddP 72475078) (BSN.sinOddQ 536870912) 0 1 hp759759 hp708891 hp759759 rfl rfl rfl

noncomputable def hp759764 := hp759751 hd4936 hd4938 hd4940 hd4942 hd4918 (hp759757 (hp759758 rfl) rfl rfl rfl rfl) (hp759762 (hp759763 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759765 := hp759623 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 426875410 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl rfl (hp759764 rfl rfl rfl rfl rfl) hp759704

noncomputable def hp759766 := nat_lit 4010232829535481669156275866703883840776092978259261900509975135033346881

noncomputable def hp759767 := nat_lit 825244916386327045287303800294283512295149278576144098343858661870401

noncomputable def hp759768 := nat_lit 12029047998773672353378252992511062955303688636220633413333237687776299841

noncomputable def hp759769 := BSN.cos_dyadic_bound_f 411692407 536870912 3 2 536870912 268435456 hp759766 hp708868 hp759767 hp759768 hp708870

noncomputable def hp759770 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 411692407) (BSN.cosEvenQ 536870912) 0 2 hp759766 hp708868 hp759767 rfl rfl rfl

noncomputable def hp759771 := hp759769 hp759767 386605599 rfl rfl rfl rfl rfl rfl rfl rfl (hp759770 rfl)

noncomputable def hp759772 := @BSN.binarySplit_of_base2 (BSN.cosOddP 411692407) (BSN.cosOddQ 536870912) 0 2 hp759768 hp708870 hp759767 rfl rfl rfl

noncomputable def hp759773 := nat_lit 2090385037568455185038477893471604359278501654428280391555976668257356001

noncomputable def hp759774 := nat_lit 224275494914967961307726316421545206181477950651059366992942834026721

noncomputable def hp759775 := nat_lit 6270706561715535619192818227781969987423142007383539055933944119104014561

noncomputable def hp759776 := BSN.cos_dyadic_bound_f 349822491 536870912 3 2 536870912 268435456 hp759773 hp708868 hp759774 hp759775 hp708870

noncomputable def hp759777 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 349822491) (BSN.cosEvenQ 536870912) 0 2 hp759773 hp708868 hp759774 rfl rfl rfl

noncomputable def hp759778 := hp759776 hp759774 426875410 rfl rfl rfl rfl rfl rfl rfl rfl (hp759777 rfl)

noncomputable def hp759779 := @BSN.binarySplit_of_base2 (BSN.cosOddP 349822491) (BSN.cosOddQ 536870912) 0 2 hp759775 hp708870 hp759774 rfl rfl rfl

noncomputable def hp759780 := hp759765 hd4944 hd4946 hd4961 hd4963 hd4918 (hp759771 (hp759772 rfl) rfl rfl rfl rfl) (hp759778 (hp759779 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759781 := @hp759618 207657 268435456 (hp759780 rfl rfl rfl rfl rfl) (hp759780 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp759782 := @hp759616 Bool.true 5292789 4194304 207657 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 855797 1000)) (Enclosure.sfrac Bool.false 855797 1000) 11) hp759781

noncomputable def hp759783 := @Enclosure.Real.IsNear.mulLit_tf hp759607 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1))) 19644101 67108864 1

noncomputable def hp759784 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp759606 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759785 := @hp759784 1 1 0 1 19644101 67108864 1 67108864 19644101 67108864 1

noncomputable def hp759786 := @Enclosure.Real.IsNear.of_eq (hp759606 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759787 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 855797 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759788 := @hp759786 (@Inv.inv Real Real.instInv (Real.sqrt hp759608)) Bool.false 19644101 67108864 1 67108864 (hp759787 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 855797 1000) 855797 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000))))

noncomputable def hp759789 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp759608)) Bool.false 19644101 67108864 1 67108864 19644101 67108864

noncomputable def hp759790 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp759608) Bool.false 229259640 67108864 6 67108864 28657455 8388608 3 33554432

noncomputable def hp759791 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 855797 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759792 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 855797 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759793 := @hp759792 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 855797 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9140517008479

noncomputable def hp759794 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 855797 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 855797 1000 0

noncomputable def hp759795 := @hp759794 1 10680707 67108864 1 67108864 9140517008479 67108864000 855797 67108864000 (Enclosure.Real.IsNear.const Bool.false 855797 1000) hd4949

noncomputable def hp759796 := @hp759793 67108864000 855797 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 855797 1000) 855797 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000))) (hp759795 rfl)

noncomputable def hp759797 := @hp759791 9140517008479 67108864000 855797 67108864000 391602367 391602404 33554432 hp759796 rfl rfl rfl

noncomputable def hp759798 := @Enclosure.Real.IsNear.recentre' hp759608 Bool.false 783204771 67108864 37 67108864 783204771 67108864 37 67108864 (hp759797 rfl rfl rfl)

noncomputable def hp759799 := @Enclosure.Real.IsNear.sqrt_image hp759608 783204771 67108864 37 67108864 114629817 114629823 33554432 (hp759798 rfl) rfl rfl

noncomputable def hp759800 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp759608) 28657455 8388608 3 33554432 9822050 9822051 33554432 (hp759790 (hp759799 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp759801 := @hp759785 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp759788 (@hp759789 1 67108864 (hp759800 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp759802 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759803 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp759804 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1))) (hp759802 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759803 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp759805 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 855797 1000) 855797 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl

noncomputable def hp759806 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759807 := @hp759806 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759803 (Enclosure.sfrac Bool.false 1 16)))) 70181025

noncomputable def hp759808 := @hp759807 33554432 263 16777216 6984947 33554432 375134929 45675970560000 490210740030675 1125899906842624 2848081403642489 139330113471774720000

noncomputable def hp759809 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759810 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759811 := @hp759809 (@Neg.neg Real Real.instNeg hp759810) Bool.true 70181025 33554432 263 16777216 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759812 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp759813 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp759814 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp759815 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 141394499) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp759816 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1))) Bool.false 39799013415877973834185

noncomputable def hp759817 := nat_lit 998484790521239161535931843

noncomputable def hp759818 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp759819 := @Enclosure.Real.IsNear.subLit_ff_p hp759608 (Enclosure.sfrac Bool.false 11 1) 783204771 67108864 37 67108864 11 1 0

noncomputable def hp759820 := @hp759818 500000000000000 45007267 67108864 37 67108864 39799013415877973834185 9444732965739290427392 hp759817 hp738031 hd4948 (@hp759819 1 45007267 45007267 67108864 37 67108864 (hp759798 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759821 := @hp759815 141394499 33554432 117 33554432 Bool.true 32085593 67108864 1 10890000 (@hp759816 9444732965739290427392 hp759817 hp738031 141394499 33554432 117 33554432 (hp759820 rfl) rfl) (Enclosure.sfrac_false_div 141394499 33554432)

noncomputable def hp759822 := nat_lit 5185284921731061286699008

noncomputable def hp759823 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 141394499) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp759822) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp759824 := BSN.sin_reduce_arg_pos_rat_q2 141394499 33554432 226375608064910080 72057594037927936 0 hp759822 hp619237 rfl rfl rfl rfl

noncomputable def hp759825 := nat_lit 282996816965346635478801209159621768031989624810004690778569048443461526754530533117941916801

noncomputable def hp759826 := nat_lit 222526922298427877027781144278749151963513080295992436302800575003135081077874001200161921

noncomputable def hp759827 := nat_lit 848545397051443050682348065190307805792041848269422087463101544180378310101435851351425426561

noncomputable def hp759828 := BSN.cos_dyadic_bound_f 147374661359 137438953472 3 2 67108864 21801270 hp759825 hp746621 hp759826 hp759827 hp746624

noncomputable def hp759829 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 147374661359) (BSN.cosEvenQ 137438953472) 0 2 hp759825 hp746621 hp759826 rfl rfl rfl

noncomputable def hp759830 := hp759828 hp759826 32085593 rfl rfl rfl rfl rfl rfl rfl rfl (hp759829 rfl)

noncomputable def hp759831 := @BSN.binarySplit_of_base2 (BSN.cosOddP 147374661359) (BSN.cosOddQ 137438953472) 0 2 hp759827 hp746624 hp759826 rfl rfl rfl

noncomputable def hp759832 := @BSN.cos_arg_round Bool.false 32085593 67108864 hp759822 hp619237 147374661359 137438953472 21801270 21780000 (hp759830 (hp759831 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759833 := hp759823 32085593 67108864 0 1000000000000000 21780000 10890000 hp759824 BSN.pi_near_15 hp759832 rfl rfl

noncomputable def hp759834 := @hp759813 32085593 67108864 81730277 22837985280000 (@hp759814 32085593 67108864 1307684432 365407764480000 32085593 67108864 81730277 22837985280000 (hp759821 (hp759833 rfl rfl) rfl rfl) rfl)

noncomputable def hp759835 := @hp759812 32085593 67108864 81730277 22837985280000 70180499 70181551 33554432 hp759834 rfl rfl rfl

noncomputable def hp759836 := @Enclosure.Real.IsNear.recentre' hp759810 Bool.false 140362050 67108864 1052 67108864 70181025 33554432 263 16777216 (hp759835 rfl rfl rfl)

noncomputable def hp759837 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759803 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp759838 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759803 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 119487165)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp759839 := nat_lit 1128524368827559454387572075525

noncomputable def hp759840 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759803 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp759839

noncomputable def hp759841 := nat_lit 6275414401286786664787014575368617

noncomputable def hp759842 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp759803 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp759843 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp759844 := @hp759843 (Enclosure.sfrac Bool.false 1 16) 994732477305399 4503599627370496 5813567095 4503599627370496 1 16 0

noncomputable def hp759845 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)) 2025654082809289

noncomputable def hp759846 := @hp759845 4503599627370496 3330539127 4503599627370496 45007267 67108864 37 67108864 66755366535871107956736 994732477305399 4503599627370496 5813567095

noncomputable def hp759847 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)) 45007267 67108864 37

noncomputable def hp759848 := @hp759847 67108864 45007267 67108864 37 67108864 2025654082809289 4503599627370496 3330539127 4503599627370496 (@hp759819 1 45007267 45007267 67108864 37 67108864 (hp759798 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759849 := hp759848 (@hp759819 1 45007267 45007267 67108864 37 67108864 (hp759798 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759850 := @hp759846 4503599627370496 (hp759849 rfl) (@hp759819 1 45007267 45007267 67108864 37 67108864 (hp759798 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp759851 := @hp759842 500000000000000 1276207454016055 4503599627370496 5813567095 4503599627370496 hp759839 hp627574 hp759841 hp747268 hd4948 (@hp759844 1 20419319264256880 1276207454016055 4503599627370496 5813567095 4503599627370496 (hp759850 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp759852 := @hp759838 119487165 67108864 545 67108864 Bool.true 6984947 33554432 1 10890000 (@hp759840 hp627574 hp759841 hp747268 119487165 67108864 545 67108864 (hp759851 rfl) rfl) (Enclosure.sfrac_true_div 119487165 67108864)

noncomputable def hp759853 := nat_lit 1683613119920202852161098212912150487806317706850542436424664663243540302794492492411362771643930640625

noncomputable def hp759854 := nat_lit 8469447574325130474100827472444298647754464208116482755719288108563153510639794599056289306640625

noncomputable def hp759855 := nat_lit 10173385083993995349786895558187180580766029708580436298983154105722135800987415152447230206035892240625

noncomputable def hp759856 := BSN.cos_dyadic_bound_t 119487165 67108864 4 3 33554432 10890000 hp759853 hp745658 hp759854 hp759855 hp745661

noncomputable def hp759857 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 119487165) (BSN.cosEvenQ 67108864) 0 3 hp759853 hp745658 hp759854 rfl rfl rfl

noncomputable def hp759858 := hp759856 hp759854 6984947 rfl rfl rfl rfl rfl rfl rfl rfl (hp759857 rfl)

noncomputable def hp759859 := @BSN.binarySplit_of_base3 (BSN.cosOddP 119487165) (BSN.cosOddQ 67108864) 0 3 hp759855 hp745661 hp759854 rfl rfl rfl

noncomputable def hp759860 := hp759852 (BSN.cos_neg_of_bound 119487165 67108864 Bool.true 6984947 33554432 1 10890000 (hp759858 (hp759859 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp759861 := hp759808 (hp759811 (@Enclosure.Real.IsNear.neg hp759810 Bool.false 70181025 33554432 263 16777216 (hp759836 rfl))) (@hp759837 6984947 33554432 6002158864 730815528960000 6984947 33554432 375134929 45675970560000 (hp759860 rfl) rfl)

noncomputable def hp759862 := @hp759783 67108864 490210740030675 1125899906842624 2848081403642489 139330113471774720000 9629749288447322798175 75557863725914323419136 777898127451875298349 hp759604 (hp759801 rfl) (@hp759804 Bool.false 490210740030675 1125899906842624 2848081403642489 139330113471774720000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759608 (Enclosure.sfrac Bool.false 11 1)) (hp759805 rfl (hp759611 rfl rfl))) (hp759861 rfl))

noncomputable def hp759863 := @hp759605 101239264006647441378349 hp759604 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 855797 1000))) (@hp759610 101239264006647441378349 hp759604 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 855797 1000) 11 (hp759611 rfl rfl)) (@hp759614 101239264006647441378349 hp759604 hp759782 (hp759862 rfl) rfl rfl))

theorem hd5048 : hp759603 hp759604 := hp759863

noncomputable def hp759864 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 857075 1000)) Bool.false 21465898029574878310945 37778931862957161709568 89328564439609642892211

noncomputable def hp759865 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 857075 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 857075 1000)) Bool.false 21465898029574878310945 37778931862957161709568

noncomputable def hp759866 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 857075 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759867 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp759866 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp759868 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 857075 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp759869 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp759867 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp759870 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 857075 1000)) hp759869 Bool.false 21465898029574878310945 37778931862957161709568

noncomputable def hp759871 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 857075 1000) 857075 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl

noncomputable def hp759872 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp759867 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp759873 := nat_lit 2881104063009216972771515432960

noncomputable def hp759874 := @hp759872 58938059 134217728 103985 134217728 4876309245178609054241 37778931862957161709568 789308693505511308211 hp752921 hp759873 21465898029574878310945 37778931862957161709568

noncomputable def hp759875 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) 11)

noncomputable def hp759876 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) 11) hp759875

noncomputable def hp759877 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) 11)

noncomputable def hp759878 := @hp759877 117876118 536870912 207970 536870912 117876118 536870912 207970 536870912 126568517947359232 58938059 134217728

noncomputable def hp759879 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp759880 := hp759879 BSN.quadSignPos 9 10 11 857075 1000 188 240 536870912 268435456 9007199254740992

noncomputable def hp759881 := hp759880 Bool.false 900659735031 3905 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp759882 := hp759881 Bool.true 160955171 178536 Bool.true 305435554 Bool.true 308959957 28296951008113761 1 Bool.false 452305333

noncomputable def hp759883 := hp759882 Bool.false Bool.false 450396931 Bool.false Bool.false 117876118 207970 BSN.abs_quadSignPos (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 452305333 536870912) BSN.abs_quadSignPos

noncomputable def hp759884 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp759885 := hp759884 BSN.quadSignNeg 7 8 9 857075 1000 66 130 536870912 268435456 9007199254740992

noncomputable def hp759886 := hp759885 Bool.false 900659735031 3905 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp759887 := hp759886 Bool.true 16238701 145810 Bool.true 512880145 Bool.true 737243001 28296951008113761 1 Bool.false 309963838

noncomputable def hp759888 := hp759887 Bool.true Bool.false 105383105 Bool.true Bool.true 160955171 178536 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 309963838 536870912) BSN.abs_quadSignNeg

noncomputable def hp759889 := hp759884 BSN.quadSignNeg 5 6 7 857075 1000 90 6 536870912 268435456 9007199254740992

noncomputable def hp759890 := hp759889 Bool.false 900659735031 3905 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp759891 := hp759890 Bool.false 356194001 108354 Bool.false 303644397 Bool.false 211415564 28296951008113761 1 Bool.false 453267748

noncomputable def hp759892 := hp759891 Bool.true Bool.false 495779173 Bool.true Bool.true 16238701 145810 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 453267748 536870912) BSN.abs_quadSignNeg

noncomputable def hp759893 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp759894 := hp759893 BSN.quadSignNeg 3 4 5 857075 1000 311 189 536870912 268435456 9007199254740992

noncomputable def hp759895 := hp759894 Bool.false 900659735031 3905 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp759896 := hp759895 Bool.false 373017634 64043 Bool.false 501228938 Bool.false 708673529 28296951008113761 1 Bool.false 431522813

noncomputable def hp759897 := hp759896 Bool.false Bool.false 520075933 Bool.true Bool.false 356194001 108354 BSN.abs_quadSignPos (BSN.cos_quad_nat3 311 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 431522813 536870912) BSN.abs_quadSignNeg

noncomputable def hp759898 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp759899 := hp759898 BSN.quadSignPos 1 2 3 857075 1000 689 468 536870912 268435456 9007199254740992

noncomputable def hp759900 := hp759899 Bool.false 900659735031 3905 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp759901 := hp759900 Bool.false 536870648 3962 Bool.false 672012881 Bool.false 474425768 28296951008113761 1 Bool.false 509772916

noncomputable def hp759902 := hp759901 Bool.true Bool.false 340540020 Bool.false Bool.false 373017634 64043 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 689 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 509772916 536870912) BSN.abs_quadSignPos

noncomputable def hp759903 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) 1) Bool.false

noncomputable def hp759904 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)))

noncomputable def hp759905 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000))) Bool.false 67108831 67108864

noncomputable def hp759906 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 56291233439) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 56291233439 33554432

noncomputable def hp759907 := nat_lit 17663895855085747378069164382241344529346192231341

noncomputable def hp759908 := nat_lit 10529205990161717945394928945661039853761986560

noncomputable def hp759909 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) Bool.false hp759907 hp759908 5189723105260898189

noncomputable def hp759910 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 857075 4000) (Real.log (Enclosure.sfrac Bool.false 2938311222500 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1714150))))))

noncomputable def hp759911 := nat_lit 221991194780812628092826562500000000

noncomputable def hp759912 := nat_lit 1141578800908072142244990587578125000000

noncomputable def hp759913 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp759910 (Enclosure.sfrac Bool.false 857075 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 857075 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp759911 hp759912)) Bool.false

noncomputable def hp759914 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 857075 1000) 857075 1000 2938311222500 16000000 1714150

noncomputable def hp759915 := hp759914 4000 2000 hp759911 hp759912 (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl rfl rfl rfl

noncomputable def hp759916 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp759910 (Enclosure.sfrac Bool.false 857075 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 857075 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp759911 hp759912) 1208845173493384182221 720575940379279360

noncomputable def hp759917 := nat_lit 1379991863678574013911653467362605041355171268073515625000000

noncomputable def hp759918 := @hp759916 5189723105260898189 713687040000000000000000 hp759911 hp759912 0 1 hp759917 hp759907 hp759908 5189723105260898189 713687040000000000000000

noncomputable def hp759919 := @Enclosure.Real.IsNear.subLit_ff_p (hp759910 (Enclosure.sfrac Bool.false 857075 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 857075 2000) (Real.log Real.pi)) 1562330677671861516749 720575940379279360 432538134702959 174240000000000000000

noncomputable def hp759920 := nat_lit 3244969053800956959376812277760

noncomputable def hp759921 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 857075 4000) (Real.log (Enclosure.sfrac Bool.false 2938311222500 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1714150))))))

noncomputable def hp759922 := @hp759921 (Enclosure.sfrac Bool.false 857075 2000) 374224897944429389097 144115188075855872 432538134702959 174240000000000000000 857075 2000 0

noncomputable def hp759923 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 857075 4000) (Real.log (Enclosure.sfrac Bool.false 2938311222500 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1714150))))) 374281470829023153641

noncomputable def hp759924 := nat_lit 842679555467647045626953188880941056

noncomputable def hp759925 := @hp759923 144115188075855872 428538134681179 174240000000000000000 883951321777571 2251799813685248 200000001089 8712000000000000000 hp759924 374224897944429389097 144115188075855872 432538134702959

noncomputable def hp759926 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 857075 4000) (Real.log (Enclosure.sfrac Bool.false 2938311222500 16000000)) 857075 4000 0 1 54587035969580135 4503599627370496

noncomputable def hp759927 := nat_lit 117224767137461165338132480

noncomputable def hp759928 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2938311222500) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp759927 hp617687

noncomputable def hp759929 := BSN.log_rat_reduce_isNear 2938311222500 16000000 17 5876622445000 4194304000000 90531137 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp759930 := nat_lit 108947878361883289056987104159411606416325076595387514199927114582964569920665840605812204040454816818237304687500000000000000000000

noncomputable def hp759931 := nat_lit 1030699083930234691688058348246286144958083971300812383116962465171970470148747610943593862944879531860351562500000000000000000000

noncomputable def hp759932 := nat_lit 167576809491512296499329351288220084294586834014089897703765780117909216090716673094586801528930664062500000000000000000000

noncomputable def hp759933 := BSN.log_dyadic_bound 841159222500 5035463222500 6 5 hp759930 268435456 87120000 hp759931 hp759932 90531137 5876622445000

noncomputable def hp759934 := hp759933 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp759935 := @BSN.binarySplit_of_base5 (BSN.artanhP 841159222500) (BSN.artanhQ 5035463222500) 0 5 hp759931 hp759930 hp759932 rfl rfl rfl

noncomputable def hp759936 := hp759929 rfl rfl rfl rfl (hp759934 (hp759935 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp759937 := @hp759926 12500018513 1089000000000000000 374281470829023153641 144115188075855872 428538134681179 174240000000000000000 (Enclosure.Real.IsNear.const Bool.false 857075 4000) (BSN.isNear_log_sfrac 2938311222500 16000000 54587035969580135 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp759928 1000001481040000 87120000000000000000000 54587035969580135 4503599627370496 12500018513 1089000000000000000 (hp759936 rfl rfl rfl) rfl)) rfl

noncomputable def hp759938 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1714150)))) 1 4

noncomputable def hp759939 := @hp759938 0 1 883951321777571 562949953421312 200000001089 2178000000000000000 883951321777571 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp759940 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1714150))) 884279719003555 562949953421312 1

noncomputable def hp759941 := @hp759940 2000000000000000 19574 33554432 1 10890000 29660484517895625244672 883951321777571 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp759942 := BSN.arctan_dyadic_bound_f 1000 1714150 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp759943 := hp759942 1 19574 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1714150) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1714150) 0 0 rfl)

noncomputable def hp759944 := hp759939 (hp759941 (hp759943 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp759945 := @hp759919 1316836119363 2684354560 102849 21474836480 hp759920 1208845173493384182221 720575940379279360 5189723105260898189 713687040000000000000000 (@hp759922 1 624932271068744606699600 1562330677671861516749 720575940379279360 432538134702959 174240000000000000000 (@hp759925 174240000000000000000 hp759937 hp759944 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 857075 2000) rfl rfl)

noncomputable def hp759946 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 857075 2000) (Real.log Real.pi) 857075 2000 0 1 38410761 33554432

noncomputable def hp759947 := hp759945 (@hp759946 3 268435456 1316836119363 2684354560 102849 21474836480 (Enclosure.Real.IsNear.const Bool.false 857075 2000) hd4909 rfl) rfl

noncomputable def hp759948 := @hp759909 713687040000000000000000 56291233439 33554432 489 67108864 (@hp759913 hp759907 hp759908 5189723105260898189 713687040000000000000000 (hp759915 rfl rfl rfl rfl rfl) (hp759918 (hp759947 rfl) (Enclosure.Real.IsNear.const Bool.true hp759911 hp759912) rfl rfl)) rfl

noncomputable def hp759949 := nat_lit 7591115343445915009548288

noncomputable def hp759950 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 56291233439) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp759949) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp759951 := BSN.sin_reduce_arg_pos_rat_q3 56291233439 33554432 226375608064910080 72057594037927936 266 hp759949 hp619237 rfl rfl rfl rfl

noncomputable def hp759952 := nat_lit 14344073521494458182508312544328791060592458515831724047103758892878473422718400006855973204878287644545846753398761714932833297432479463899136

noncomputable def hp759953 := nat_lit 10173477430983503495159555096486992830949386193184012033250460715098302649749224707059011205228789310269975352744174038934690373079924736

noncomputable def hp759954 := nat_lit 71631470422772315457593700753270750982371003380128363423131919449746690664984641308975857207285189122448870195127064408108062350347136082640896

noncomputable def hp759955 := BSN.sin_dyadic_bound_f 215752474544 137438953472 4 3 67108864 21801270 hp759952 hp737934 hp759953 hp759954 hp737937

noncomputable def hp759956 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215752474544) (BSN.sinEvenQ 137438953472) 0 3 hp759952 hp737934 hp759953 rfl rfl rfl

noncomputable def hp759957 := hp759955 hp759953 67108831 rfl rfl rfl rfl rfl rfl rfl rfl (hp759956 rfl)

noncomputable def hp759958 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215752474544) (BSN.sinOddQ 137438953472) 0 3 hp759954 hp737937 hp759953 rfl rfl rfl

noncomputable def hp759959 := @BSN.sin_arg_round Bool.false 67108831 67108864 hp759949 hp619237 215752474544 137438953472 21801270 21780000 (hp759957 (hp759958 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759960 := hp759950 67108831 67108864 266 1000000000000000 21780000 10890000 hp759951 BSN.pi_near_15 hp759959 rfl rfl

noncomputable def hp759961 := @hp759906 489 67108864 Bool.false 67108831 67108864 1 10890000 hp759948 (Enclosure.sfrac_false_div 56291233439 33554432) (hp759960 rfl rfl) rfl

noncomputable def hp759962 := @hp759903 67108831 67108864 337019929 45675970560000 536870648 536870912 3962 536870912 (@hp759904 Bool.false 67108831 67108864 337019929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000)) (@hp759905 5392318864 730815528960000 67108831 67108864 337019929 45675970560000 (hp759961 rfl) rfl))

noncomputable def hp759963 := @hp759909 713687040000000000000000 900659735031 536870912 3905 536870912 (@hp759913 hp759907 hp759908 5189723105260898189 713687040000000000000000 (hp759915 rfl rfl rfl rfl rfl) (hp759918 (hp759947 rfl) (Enclosure.Real.IsNear.const Bool.true hp759911 hp759912) rfl rfl)) rfl

noncomputable def hp759964 := hp759902 (BSN.cos_quad_nat0 468 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 340540020 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl rfl (hp759962 rfl) hp759963

noncomputable def hp759965 := nat_lit 73100596776824531118713772285167157656583346341434142216419219374919001348847566239004070000068756276845285338561

noncomputable def hp759966 := nat_lit 8482642638259830141946037869761786910975660553777497673398620674959320172637702956886920043960913589824961

noncomputable def hp759967 := nat_lit 365319674715108488120164303023692118189973544051698688206801689683036246020085089991263987389806234469250028137921

noncomputable def hp759968 := BSN.sin_dyadic_bound_f 672012881 536870912 4 3 536870912 268435456 hp759965 hp642702 hp759966 hp759967 hp642705

noncomputable def hp759969 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 672012881) (BSN.sinEvenQ 536870912) 0 3 hp759965 hp642702 hp759966 rfl rfl rfl

noncomputable def hp759970 := hp759968 hp759966 509772916 rfl rfl rfl rfl rfl rfl rfl rfl (hp759969 rfl)

noncomputable def hp759971 := @BSN.binarySplit_of_base3 (BSN.sinOddP 672012881) (BSN.sinOddQ 536870912) 0 3 hp759967 hp642705 hp759966 rfl rfl rfl

noncomputable def hp759972 := nat_lit 7073257490334119492018939190785104623178448696684076793644631610733101056

noncomputable def hp759973 := nat_lit 2566528873365271765313642093503230332888767139063865457913588220952576

noncomputable def hp759974 := nat_lit 21214639413255627932526190288168307408869568555774102650018067655757398016

noncomputable def hp759975 := BSN.cos_dyadic_bound_f 474425768 536870912 3 2 536870912 268435456 hp759972 hp708868 hp759973 hp759974 hp708870

noncomputable def hp759976 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 474425768) (BSN.cosEvenQ 536870912) 0 2 hp759972 hp708868 hp759973 rfl rfl rfl

noncomputable def hp759977 := hp759975 hp759973 340540020 rfl rfl rfl rfl rfl rfl rfl rfl (hp759976 rfl)

noncomputable def hp759978 := @BSN.binarySplit_of_base2 (BSN.cosOddP 474425768) (BSN.cosOddQ 536870912) 0 2 hp759974 hp708870 hp759973 rfl rfl rfl

noncomputable def hp759979 := hp759964 hd4911 hd4913 hd4915 hd4917 hd4918 (hp759970 (hp759971 rfl) rfl rfl rfl rfl) (hp759977 (hp759978 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759980 := hp759897 (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 520075933 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl rfl (hp759979 rfl rfl rfl rfl rfl) hp759963

noncomputable def hp759981 := nat_lit 15860428903408261387523012976918631252670530882178300764179096357009875200

noncomputable def hp759982 := nat_lit 3983722634354186192915138099386192173434941994750272210087723100528896

noncomputable def hp759983 := nat_lit 41532768719899349237295552335006932779189638594856430132128919859529769216

noncomputable def hp759984 := BSN.sin_dyadic_bound_f 501228938 536870912 3 2 536870912 268435456 hp759981 hp708845 hp759982 hp759983 hp708848

noncomputable def hp759985 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 501228938) (BSN.sinEvenQ 536870912) 0 2 hp759981 hp708845 hp759982 rfl rfl rfl

noncomputable def hp759986 := hp759984 hp759982 431522813 rfl rfl rfl rfl rfl rfl rfl rfl (hp759985 rfl)

noncomputable def hp759987 := @BSN.binarySplit_of_base2 (BSN.sinOddP 501228938) (BSN.sinOddQ 536870912) 0 2 hp759983 hp708848 hp759982 rfl rfl rfl

noncomputable def hp759988 := nat_lit 90422974211490822795400276552417190346633244678726391759969167898953421140101587702026475423001716921282795358241

noncomputable def hp759989 := nat_lit 16045547146949468351456140321582429120037609613583600753538064911499175249861172789393993773011124347947041

noncomputable def hp759990 := nat_lit 451834487769074929920599406876721610766617203294702306191575749707524625796151219209276355754648087303967634311201

noncomputable def hp759991 := BSN.sin_dyadic_bound_f 708673529 536870912 4 3 536870912 268435456 hp759988 hp642702 hp759989 hp759990 hp642705

noncomputable def hp759992 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 708673529) (BSN.sinEvenQ 536870912) 0 3 hp759988 hp642702 hp759989 rfl rfl rfl

noncomputable def hp759993 := hp759991 hp759989 520075933 rfl rfl rfl rfl rfl rfl rfl rfl (hp759992 rfl)

noncomputable def hp759994 := @BSN.binarySplit_of_base3 (BSN.sinOddP 708673529) (BSN.sinOddQ 536870912) 0 3 hp759990 hp642705 hp759989 rfl rfl rfl

noncomputable def hp759995 := hp759980 hd4920 hd4922 hd4924 hd4926 hd4918 (hp759986 (hp759987 rfl) rfl rfl rfl rfl) (hp759993 (hp759994 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp759996 := hp759892 (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 495779173 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl rfl (hp759995 rfl rfl rfl rfl rfl) hp759963

noncomputable def hp759997 := nat_lit 1186523424868289080682335783944909283864652026514409522330864281206027041

noncomputable def hp759998 := nat_lit 72264029362588208995771181999399654005778818510570800271233525904161

noncomputable def hp759999 := nat_lit 3559425746546142065629015809470729052285944521906207425392050376566272801

noncomputable def hp760000 := BSN.cos_dyadic_bound_f 303644397 536870912 3 2 536870912 268435456 hp759997 hp708868 hp759998 hp759999 hp708870

noncomputable def hp760001 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 303644397) (BSN.cosEvenQ 536870912) 0 2 hp759997 hp708868 hp759998 rfl rfl rfl

noncomputable def hp760002 := hp760000 hp759998 453267748 rfl rfl rfl rfl rfl rfl rfl rfl (hp760001 rfl)

noncomputable def hp760003 := @BSN.binarySplit_of_base2 (BSN.cosOddP 303644397) (BSN.cosOddQ 536870912) 0 2 hp759999 hp708870 hp759998 rfl rfl rfl

noncomputable def hp760004 := nat_lit 278832131967899931058375384334073646925652332641516488700488026475790336

noncomputable def hp760005 := nat_lit 3991127927768814417875668593968864230501541756159123476859710406656

noncomputable def hp760006 := nat_lit 836488413647844255546290401665033003048495994841037147854510360006557696

noncomputable def hp760007 := BSN.cos_dyadic_bound_f 211415564 536870912 3 2 536870912 268435456 hp760004 hp708868 hp760005 hp760006 hp708870

noncomputable def hp760008 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 211415564) (BSN.cosEvenQ 536870912) 0 2 hp760004 hp708868 hp760005 rfl rfl rfl

noncomputable def hp760009 := hp760007 hp760005 495779173 rfl rfl rfl rfl rfl rfl rfl rfl (hp760008 rfl)

noncomputable def hp760010 := @BSN.binarySplit_of_base2 (BSN.cosOddP 211415564) (BSN.cosOddQ 536870912) 0 2 hp760006 hp708870 hp760005 rfl rfl rfl

noncomputable def hp760011 := hp759996 hd4928 hd4930 hd4932 hd4934 hd4918 (hp760002 (hp760003 rfl) rfl rfl rfl rfl) (hp760009 (hp760010 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760012 := hp759888 (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 105383105 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl rfl (hp760011 rfl rfl rfl rfl rfl) hp759963

noncomputable def hp760013 := nat_lit 9535940492113998187068846064135151615277130584068287579787710464396023754963353058587419754546925664143511890625

noncomputable def hp760014 := nat_lit 331276508226267224715474849386665816448284883871626967666743488062363447400198099183877199100840087890625

noncomputable def hp760015 := nat_lit 57832259706687690930539195032940288931461366945282201739424937899035432222169875275710696855280639708537393490625

noncomputable def hp760016 := BSN.cos_dyadic_bound_f 512880145 536870912 4 3 536870912 268435456 hp760013 hp716712 hp760014 hp760015 hp716714

noncomputable def hp760017 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 512880145) (BSN.cosEvenQ 536870912) 0 3 hp760013 hp716712 hp760014 rfl rfl rfl

noncomputable def hp760018 := hp760016 hp760014 309963838 rfl rfl rfl rfl rfl rfl rfl rfl (hp760017 rfl)

noncomputable def hp760019 := @BSN.binarySplit_of_base3 (BSN.cosOddP 512880145) (BSN.cosOddQ 536870912) 0 3 hp760015 hp716714 hp760014 rfl rfl rfl

noncomputable def hp760020 := nat_lit 40779877060641447073743484642231647864418385815806523725467657512535849483254060598491845558153091511153416770081

noncomputable def hp760021 := nat_lit 25782670555442496280448101705957392956622476105179125193554381440893047778589438926199297818632458080916001

noncomputable def hp760022 := nat_lit 247049420740143520895381617210745645955785239393297113647821722632978212932860194619238028632237440428625340437025

noncomputable def hp760023 := BSN.cos_dyadic_bound_f 737243001 536870912 4 3 536870912 268435456 hp760020 hp716712 hp760021 hp760022 hp716714

noncomputable def hp760024 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 737243001) (BSN.cosEvenQ 536870912) 0 3 hp760020 hp716712 hp760021 rfl rfl rfl

noncomputable def hp760025 := hp760023 hp760021 105383105 rfl rfl rfl rfl rfl rfl rfl rfl (hp760024 rfl)

noncomputable def hp760026 := @BSN.binarySplit_of_base3 (BSN.cosOddP 737243001) (BSN.cosOddQ 536870912) 0 3 hp760022 hp716714 hp760021 rfl rfl rfl

noncomputable def hp760027 := hp760012 hd4936 hd4938 hd4940 hd4942 hd4918 (hp760018 (hp760019 rfl) rfl rfl rfl rfl) (hp760025 (hp760026 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760028 := hp759883 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 450396931 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl rfl (hp760027 rfl rfl rfl rfl rfl) hp759963

noncomputable def hp760029 := nat_lit 1214770444779478726892572315983607925328359636287799451530589830363382016

noncomputable def hp760030 := nat_lit 75745478790700057114141992181138561540162885182579857327543657595136

noncomputable def hp760031 := nat_lit 3644159843380854780563488663966461498861998583093033194877114403774955776

noncomputable def hp760032 := BSN.cos_dyadic_bound_f 305435554 536870912 3 2 536870912 268435456 hp760029 hp708868 hp760030 hp760031 hp708870

noncomputable def hp760033 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 305435554) (BSN.cosEvenQ 536870912) 0 2 hp760029 hp708868 hp760030 rfl rfl rfl

noncomputable def hp760034 := hp760032 hp760030 452305333 rfl rfl rfl rfl rfl rfl rfl rfl (hp760033 rfl)

noncomputable def hp760035 := @BSN.binarySplit_of_base2 (BSN.cosOddP 305435554) (BSN.cosOddQ 536870912) 0 2 hp760031 hp708870 hp760030 rfl rfl rfl

noncomputable def hp760036 := nat_lit 1271820775862883313944572295891577745602581950067174046037528232489322081

noncomputable def hp760037 := nat_lit 83026660090942776486154914424603367064533717051358978499742450517601

noncomputable def hp760038 := nat_lit 3815296274268468056280744577845884030073616782767419420155585212566931041

noncomputable def hp760039 := BSN.cos_dyadic_bound_f 308959957 536870912 3 2 536870912 268435456 hp760036 hp708868 hp760037 hp760038 hp708870

noncomputable def hp760040 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 308959957) (BSN.cosEvenQ 536870912) 0 2 hp760036 hp708868 hp760037 rfl rfl rfl

noncomputable def hp760041 := hp760039 hp760037 450396931 rfl rfl rfl rfl rfl rfl rfl rfl (hp760040 rfl)

noncomputable def hp760042 := @BSN.binarySplit_of_base2 (BSN.cosOddP 308959957) (BSN.cosOddQ 536870912) 0 2 hp760038 hp708870 hp760037 rfl rfl rfl

noncomputable def hp760043 := hp760028 hd4944 hd4946 hd4961 hd4963 hd4918 (hp760034 (hp760035 rfl) rfl rfl rfl rfl) (hp760041 (hp760042 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760044 := @hp759878 103985 134217728 (hp760043 rfl rfl rfl rfl rfl) (hp760043 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp760045 := @hp759876 Bool.false 58938059 134217728 103985 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 857075 1000)) (Enclosure.sfrac Bool.false 857075 1000) 11) hp760044

noncomputable def hp760046 := @Enclosure.Real.IsNear.mulLit_tf hp759867 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1))) 9818387 33554432 1

noncomputable def hp760047 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp759866 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760048 := @hp760047 1 1 0 1 9818387 33554432 1 33554432 9818387 33554432 1

noncomputable def hp760049 := @Enclosure.Real.IsNear.of_eq (hp759866 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760050 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 857075 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760051 := @hp760049 (@Inv.inv Real Real.instInv (Real.sqrt hp759868)) Bool.false 9818387 33554432 1 33554432 (hp760050 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 857075 1000) 857075 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000))))

noncomputable def hp760052 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp759868)) Bool.false 19636774 67108864 2 67108864 9818387 33554432

noncomputable def hp760053 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp759868) Bool.false 229345183 67108864 7 67108864 229345183 67108864 7 67108864

noncomputable def hp760054 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 857075 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760055 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 857075 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760056 := @hp760055 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 857075 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 366166678081

noncomputable def hp760057 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 857075 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 857075 1000 0

noncomputable def hp760058 := @hp760057 1 10680707 67108864 1 67108864 366166678081 2684354560 34283 2684354560 (Enclosure.Real.IsNear.const Bool.false 857075 1000) hd4949

noncomputable def hp760059 := @hp760056 2684354560 34283 2684354560 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 857075 1000) 857075 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000))) (hp760058 rfl)

noncomputable def hp760060 := @hp760054 366166678081 2684354560 34283 2684354560 391894656 391894694 33554432 hp760059 rfl rfl rfl

noncomputable def hp760061 := @Enclosure.Real.IsNear.recentre' hp759868 Bool.false 783789350 67108864 38 67108864 391894675 33554432 19 33554432 (hp760060 rfl rfl rfl)

noncomputable def hp760062 := @Enclosure.Real.IsNear.sqrt_image hp759868 391894675 33554432 19 33554432 114672588 114672595 33554432 (hp760061 rfl) rfl rfl

noncomputable def hp760063 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp759868) 229345183 67108864 7 67108864 9818386 9818388 33554432 (hp760053 (hp760062 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp760064 := @hp760048 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp760051 (@hp760052 1 33554432 (hp760063 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp760065 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760066 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp760067 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1))) (hp760065 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760066 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp760068 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 857075 1000) 857075 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl

noncomputable def hp760069 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760070 := @hp760069 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760066 (Enclosure.sfrac Bool.false 1 16)))) 78151807

noncomputable def hp760071 := @hp760070 33554432 167 8388608 6354949 33554432 97016701 11418992640000 496650747742843 1125899906842624 120356772159583 5108770827298406400

noncomputable def hp760072 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760073 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760074 := @hp760072 (@Neg.neg Real Real.instNeg hp760073) Bool.true 78151807 33554432 167 8388608 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760075 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760076 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp760077 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp760078 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 4475969) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false

noncomputable def hp760079 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1))) Bool.false 20157972384866676506265

noncomputable def hp760080 := nat_lit 512735432967652351182478789

noncomputable def hp760081 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp760082 := @Enclosure.Real.IsNear.subLit_ff_p hp759868 (Enclosure.sfrac Bool.false 11 1) 391894675 33554432 19 33554432 11 1 0

noncomputable def hp760083 := @hp760081 500000000000000 22795923 33554432 19 33554432 20157972384866676506265 4722366482869645213696 hp760080 hp682805 hd4948 (@hp760082 1 22795923 22795923 33554432 19 33554432 (hp760061 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760084 := @hp760078 4475969 1048576 15 4194304 Bool.true 28813151 67108864 1 10890000 (@hp760079 4722366482869645213696 hp760080 hp682805 4475969 1048576 15 4194304 (hp760083 rfl) rfl) (Enclosure.sfrac_false_div 4475969 1048576)

noncomputable def hp760085 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 4475969) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 170311055052158227447808) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp760086 := BSN.sin_reduce_arg_pos_rat_q2 4475969 1048576 226375608064910080 72057594037927936 0 170311055052158227447808 151115727451828646838272 rfl rfl rfl rfl

noncomputable def hp760087 := nat_lit 345412110111724515151820083928646028214818019818802650347028017156195078594253062425060549761

noncomputable def hp760088 := nat_lit 331393588837618120156793305477359161932077210764824569690539870361017301723558210972132481

noncomputable def hp760089 := nat_lit 1035573543157498309215146665174983366320589905034878301901702971727863201179312070853237384321

noncomputable def hp760090 := BSN.cos_dyadic_bound_f 154897002223 137438953472 3 2 67108864 21801270 hp760087 hp746621 hp760088 hp760089 hp746624

noncomputable def hp760091 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 154897002223) (BSN.cosEvenQ 137438953472) 0 2 hp760087 hp746621 hp760088 rfl rfl rfl

noncomputable def hp760092 := hp760090 hp760088 28813151 rfl rfl rfl rfl rfl rfl rfl rfl (hp760091 rfl)

noncomputable def hp760093 := @BSN.binarySplit_of_base2 (BSN.cosOddP 154897002223) (BSN.cosOddQ 137438953472) 0 2 hp760089 hp746624 hp760088 rfl rfl rfl

noncomputable def hp760094 := @BSN.cos_arg_round Bool.false 28813151 67108864 170311055052158227447808 151115727451828646838272 154897002223 137438953472 21801270 21780000 (hp760092 (hp760093 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760095 := hp760085 28813151 67108864 0 1000000000000000 21780000 10890000 hp760086 BSN.pi_near_15 hp760094 rfl rfl

noncomputable def hp760096 := @hp760076 28813151 67108864 10471519 2854748160000 (@hp760077 28813151 67108864 167544304 45675970560000 28813151 67108864 10471519 2854748160000 (hp760084 (hp760095 rfl rfl) rfl rfl) rfl)

noncomputable def hp760097 := @hp760075 28813151 67108864 10471519 2854748160000 78151139 78152475 33554432 hp760096 rfl rfl rfl

noncomputable def hp760098 := @Enclosure.Real.IsNear.recentre' hp760073 Bool.false 156303614 67108864 1336 67108864 78151807 33554432 167 8388608 (hp760097 rfl rfl rfl)

noncomputable def hp760099 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760066 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp760100 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760066 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 118201491)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp760101 := nat_lit 279095380652397371874708154405

noncomputable def hp760102 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760066 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp760101

noncomputable def hp760103 := nat_lit 40581110847294479240633890849243613

noncomputable def hp760104 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760066 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp760105 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp760106 := @hp760105 (Enclosure.sfrac Bool.false 1 16) 245250142758807 1125899906842624 1503779643 1125899906842624 1 16 0

noncomputable def hp760107 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)) 519654105421929

noncomputable def hp760108 := @hp760107 1125899906842624 866245435 1125899906842624 22795923 33554432 19 33554432 8229229238190681882624 245250142758807 1125899906842624 1503779643

noncomputable def hp760109 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)) 22795923 33554432 19

noncomputable def hp760110 := @hp760109 33554432 22795923 33554432 19 33554432 519654105421929 1125899906842624 866245435 1125899906842624 (@hp760082 1 22795923 22795923 33554432 19 33554432 (hp760061 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760111 := hp760110 (@hp760082 1 22795923 22795923 33554432 19 33554432 (hp760061 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760112 := @hp760108 1125899906842624 (hp760111 rfl) (@hp760082 1 22795923 22795923 33554432 19 33554432 (hp760061 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760113 := @hp760104 500000000000000 315618886936471 1125899906842624 1503779643 1125899906842624 hp760101 hp682141 hp760103 hp682143 hd4948 (@hp760106 1 5049902190983536 315618886936471 1125899906842624 1503779643 1125899906842624 (hp760112 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp760114 := @hp760100 118201491 67108864 141 16777216 Bool.true 6354949 33554432 1 10890000 (@hp760102 hp682141 hp760103 hp682143 118201491 67108864 141 16777216 (hp760113 rfl) rfl) (Enclosure.sfrac_true_div 118201491 67108864)

noncomputable def hp760115 := nat_lit 1611905312653640747828190903586098384648788843792668757706429840895852707233449240855843732979428416561

noncomputable def hp760116 := nat_lit 7438330268721495034791950465871726984072238773725346105610873060452378589873048313472896099474481

noncomputable def hp760117 := nat_lit 9741719963760633973322727048041619064534955497614802779754311946898067117716762142232036894689013062705

noncomputable def hp760118 := BSN.cos_dyadic_bound_t 118201491 67108864 4 3 33554432 10890000 hp760115 hp745658 hp760116 hp760117 hp745661

noncomputable def hp760119 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 118201491) (BSN.cosEvenQ 67108864) 0 3 hp760115 hp745658 hp760116 rfl rfl rfl

noncomputable def hp760120 := hp760118 hp760116 6354949 rfl rfl rfl rfl rfl rfl rfl rfl (hp760119 rfl)

noncomputable def hp760121 := @BSN.binarySplit_of_base3 (BSN.cosOddP 118201491) (BSN.cosOddQ 67108864) 0 3 hp760117 hp745661 hp760116 rfl rfl rfl

noncomputable def hp760122 := hp760114 (BSN.cos_neg_of_bound 118201491 67108864 Bool.true 6354949 33554432 1 10890000 (hp760120 (hp760121 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp760123 := hp760071 (hp760074 (@Enclosure.Real.IsNear.neg hp760073 Bool.false 78151807 33554432 167 8388608 (hp760098 rfl))) (@hp760099 6354949 33554432 1552267216 182703882240000 6354949 33554432 97016701 11418992640000 (hp760122 rfl) rfl)

noncomputable def hp760124 := @hp760046 33554432 496650747742843 1125899906842624 120356772159583 5108770827298406400 4876309245178609054241 37778931862957161709568 789308693505511308211 hp752921 (hp760064 rfl) (@hp760067 Bool.false 496650747742843 1125899906842624 120356772159583 5108770827298406400 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp759868 (Enclosure.sfrac Bool.false 11 1)) (hp760068 rfl (hp759871 rfl rfl))) (hp760123 rfl))

noncomputable def hp760125 := @hp759865 89328564439609642892211 hp752921 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 857075 1000))) (@hp759870 89328564439609642892211 hp752921 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 857075 1000) 11 (hp759871 rfl rfl)) (@hp759874 89328564439609642892211 hp752921 hp760045 (hp760124 rfl) rfl rfl))

theorem hd5049 : hp759864 hp752921 := hp760125

noncomputable def hp760126 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 858353 1000)) Bool.true 194420638923990726256605 75557863725914323419136 537395385163191866287469

noncomputable def hp760127 := nat_lit 685687613312672485028659200

noncomputable def hp760128 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 858353 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 858353 1000)) Bool.true 194420638923990726256605 75557863725914323419136

noncomputable def hp760129 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 858353 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760130 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp760129 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760131 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 858353 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760132 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp760130 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp760133 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 858353 1000)) hp760132 Bool.true 194420638923990726256605 75557863725914323419136

noncomputable def hp760134 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 858353 1000) 858353 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl

noncomputable def hp760135 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp760130 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp760136 := nat_lit 6523674108171599992807867023360

noncomputable def hp760137 := @hp760135 90728811 33554432 208269 268435456 9882480781693353023523 75557863725914323419136 5396089447885965026669 hp760127 hp760136 194420638923990726256605 75557863725914323419136

noncomputable def hp760138 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) 11)

noncomputable def hp760139 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) 11) hp760138

noncomputable def hp760140 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) 11)

noncomputable def hp760141 := @hp760140 725830488 536870912 208269 536870912 725830488 536870912 208269 536870912 779354552099930112 90728811 33554432

noncomputable def hp760142 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp760143 := hp760142 BSN.quadSignPos 9 10 11 858353 1000 188 240 536870912 268435456 9007199254740992

noncomputable def hp760144 := hp760143 Bool.false 902346355344 3910 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp760145 := hp760144 Bool.true 1026291335 178792 Bool.true 198667283 Bool.true 267586005 28296951008113761 1 Bool.false 500530374

noncomputable def hp760146 := hp760145 Bool.false Bool.false 471555208 Bool.false Bool.true 725830488 208269 BSN.abs_quadSignPos (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 500530374 536870912) BSN.abs_quadSignPos

noncomputable def hp760147 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp760148 := hp760147 BSN.quadSignNeg 7 8 9 858353 1000 66 130 536870912 268435456 9007199254740992

noncomputable def hp760149 := hp760148 Bool.false 902346355344 3910 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp760150 := hp760149 Bool.true 766531415 146018 Bool.true 253008394 Bool.true 558184650 28296951008113761 1 Bool.false 478349157

noncomputable def hp760151 := hp760150 Bool.true Bool.false 271913850 Bool.true Bool.true 1026291335 178792 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 478349157 536870912) BSN.abs_quadSignNeg

noncomputable def hp760152 := hp760147 BSN.quadSignNeg 5 6 7 858353 1000 90 6 536870912 268435456 9007199254740992

noncomputable def hp760153 := hp760152 Bool.false 902346355344 3910 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp760154 := hp760153 Bool.true 631786910 108507 Bool.false 760900874 Bool.false 562906029 28296951008113761 1 Bool.false 82090686

noncomputable def hp760155 := hp760154 Bool.true Bool.false 267832368 Bool.true Bool.true 766531415 146018 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 90 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 82090686 536870912) BSN.abs_quadSignNeg

noncomputable def hp760156 := hp760142 BSN.quadSignNeg 3 4 5 858353 1000 312 190 536870912 268435456 9007199254740992

noncomputable def hp760157 := hp760156 Bool.false 902346355344 3910 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp760158 := hp760157 Bool.true 669994557 64131 Bool.false 393368704 Bool.false 447709815 28296951008113761 1 Bool.false 399092076

noncomputable def hp760159 := hp760158 Bool.false Bool.false 360763588 Bool.true Bool.true 631786910 108507 BSN.abs_quadSignPos (BSN.cos_quad_nat0 312 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 399092076 536870912) BSN.abs_quadSignNeg

noncomputable def hp760160 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp760161 := hp760160 BSN.quadSignNeg 1 2 3 858353 1000 691 469 536870912 268435456 9007199254740992

noncomputable def hp760162 := hp760161 Bool.false 902346355344 3910 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp760163 := hp760162 Bool.true 536870632 3962 Bool.false 196420645 Bool.false 563950241 28296951008113761 1 Bool.false 192067898

noncomputable def hp760164 := hp760163 Bool.false Bool.false 465811572 Bool.true Bool.true 669994557 64131 BSN.abs_quadSignPos (BSN.cos_quad_nat3 691 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 192067898 536870912) BSN.abs_quadSignNeg

noncomputable def hp760165 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) 1) Bool.true

noncomputable def hp760166 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)))

noncomputable def hp760167 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000))) Bool.true 67108829 67108864

noncomputable def hp760168 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 56396647209) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 56396647209 33554432

noncomputable def hp760169 := nat_lit 108983735065463807772780631455830048936670996088191242401439

noncomputable def hp760170 := nat_lit 64842282446467256886473231537201876559516776030797824000

noncomputable def hp760171 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) Bool.false hp760169 hp760170 129935929114076764919

noncomputable def hp760172 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 858353 4000) (Real.log (Enclosure.sfrac Bool.false 2947080490436 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1716706))))))

noncomputable def hp760173 := nat_lit 223651212781870970637375107356640000

noncomputable def hp760174 := nat_lit 1151830319061049168398249370021380083520

noncomputable def hp760175 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp760172 (Enclosure.sfrac Bool.false 858353 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 858353 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp760173 hp760174)) Bool.false

noncomputable def hp760176 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 858353 1000) 858353 1000 2947080490436 16000000 1716706

noncomputable def hp760177 := hp760176 4000 2000 hp760173 hp760174 (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl rfl rfl rfl

noncomputable def hp760178 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp760172 (Enclosure.sfrac Bool.false 858353 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 858353 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp760173 hp760174) 30277722918701936742199 18014398509481984000

noncomputable def hp760179 := nat_lit 34874795220948418487289802065865615659734718748221197568460480

noncomputable def hp760180 := @hp760178 129935929114076764919 hp738659 hp760173 hp760174 0 1 hp760179 hp760169 hp760170 129935929114076764919 hp738659

noncomputable def hp760181 := @Enclosure.Real.IsNear.subLit_ff_p (hp760172 (Enclosure.sfrac Bool.false 858353 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 858353 2000) (Real.log Real.pi)) 39128037738528339201847 18014398509481984000 10829428391233589 4356000000000000000000

noncomputable def hp760182 := nat_lit 2031903589580851329368835751936000

noncomputable def hp760183 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 858353 4000) (Real.log (Enclosure.sfrac Bool.false 2947080490436 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1716706))))))

noncomputable def hp760184 := @hp760183 (Enclosure.sfrac Bool.false 858353 2000) 46859394240433033908023 18014398509481984000 10829428391233589 4356000000000000000000 858353 2000 0

noncomputable def hp760185 := nat_lit 78256075477056678403694000

noncomputable def hp760186 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 858353 4000) (Real.log (Enclosure.sfrac Bool.false 2947080490436 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1716706))))) 46866465854899568588023

noncomputable def hp760187 := nat_lit 105517975220010688977577106219103944704

noncomputable def hp760188 := @hp760186 18014398509481984000 10729428390689089 4356000000000000000000 883951808316835 2251799813685248 200000001089 8712000000000000000 hp760187 46859394240433033908023 18014398509481984000 10829428391233589

noncomputable def hp760189 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 858353 4000) (Real.log (Enclosure.sfrac Bool.false 2947080490436 16000000)) 858353 4000 0 1 54600456752524391 4503599627370496

noncomputable def hp760190 := nat_lit 117253588049377312393658368

noncomputable def hp760191 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2947080490436) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp760190 hp617687

noncomputable def hp760192 := BSN.log_rat_reduce_isNear 2947080490436 16000000 17 5894160980872 4194304000000 91331078 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp760193 := nat_lit 110860145724774065639361542955877514886447325756793055674564634462435294074119567440900141064588919579487753787424343547842023915520

noncomputable def hp760194 := nat_lit 1067370553719955438159754209882472677866406193438304334940950020972629388740732595420816169687054616936323609590957722202515963904

noncomputable def hp760195 := nat_lit 185889852629879845150877491550772081286835059388341715486665634300457377933469637539166923539065358012427516930675383992320

noncomputable def hp760196 := BSN.log_dyadic_bound 849928490436 5044232490436 6 5 hp760193 268435456 87120000 hp760194 hp760195 91331078 5894160980872

noncomputable def hp760197 := hp760196 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp760198 := @BSN.binarySplit_of_base5 (BSN.artanhP 849928490436) (BSN.artanhQ 5044232490436) 0 5 hp760194 hp760193 hp760195 rfl rfl rfl

noncomputable def hp760199 := hp760192 rfl rfl rfl rfl (hp760197 (hp760198 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp760200 := @hp760189 12500018513 1089000000000000000 46866465854899568588023 18014398509481984000 10729428390689089 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 858353 4000) (BSN.isNear_log_sfrac 2947080490436 16000000 54600456752524391 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp760191 1000001481040000 87120000000000000000000 54600456752524391 4503599627370496 12500018513 1089000000000000000 (hp760199 rfl rfl rfl) rfl)) rfl

noncomputable def hp760201 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1716706)))) 1 4

noncomputable def hp760202 := @hp760201 0 1 883951808316835 562949953421312 200000001089 2178000000000000000 883951808316835 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp760203 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1716706))) 884279719003555 562949953421312 1

noncomputable def hp760204 := @hp760203 2000000000000000 19545 33554432 1 10890000 29660500843444274462720 883951808316835 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp760205 := BSN.arctan_dyadic_bound_f 1000 1716706 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp760206 := hp760205 1 19545 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1716706) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1716706) 0 0 rfl)

noncomputable def hp760207 := hp760202 (hp760204 (hp760206 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp760208 := @hp760181 32969991936633 67108864000 2575059 536870912000 hp760182 30277722918701936742199 18014398509481984000 129935929114076764919 hp738659 (@hp760184 1 hp760185 39128037738528339201847 18014398509481984000 10829428391233589 4356000000000000000000 (@hp760188 4356000000000000000000 hp760200 hp760207 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 858353 2000) rfl rfl)

noncomputable def hp760209 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 858353 2000) (Real.log Real.pi) 858353 2000 0 1 38410761 33554432

noncomputable def hp760210 := hp760208 (@hp760209 3 268435456 32969991936633 67108864000 2575059 536870912000 (Enclosure.Real.IsNear.const Bool.false 858353 2000) hd4909 rfl) rfl

noncomputable def hp760211 := @hp760171 hp738659 56396647209 33554432 489 67108864 (@hp760175 hp760169 hp760170 129935929114076764919 hp738659 (hp760177 rfl rfl rfl rfl rfl) (hp760180 (hp760210 rfl) (Enclosure.Real.IsNear.const Bool.true hp760173 hp760174) rfl rfl)) rfl

noncomputable def hp760212 := nat_lit 7591030738235574722756608

noncomputable def hp760213 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 56396647209) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp760212) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp760214 := BSN.sin_reduce_arg_pos_rat_q1 56396647209 33554432 226375608064910080 72057594037927936 267 hp760212 hp619237 rfl rfl rfl rfl

noncomputable def hp760215 := nat_lit 14343432774020728304285019234389512674580210372755695353921041289128624208210312893248101777102796977364214194365529569943157547372342367557761

noncomputable def hp760216 := nat_lit 10172116877486815222974334020994194132848074817538555794748340428726449315637353388281692577950618541871717017923044186699558771289823361

noncomputable def hp760217 := nat_lit 71628274613191335812992776751391906856025953750055752928758510494945628258492849711635919258256573617757412466318813878685905189284058201659521

noncomputable def hp760218 := BSN.sin_dyadic_bound_f 215750069919 137438953472 4 3 67108864 21801270 hp760215 hp737934 hp760216 hp760217 hp737937

noncomputable def hp760219 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215750069919) (BSN.sinEvenQ 137438953472) 0 3 hp760215 hp737934 hp760216 rfl rfl rfl

noncomputable def hp760220 := hp760218 hp760216 67108829 rfl rfl rfl rfl rfl rfl rfl rfl (hp760219 rfl)

noncomputable def hp760221 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215750069919) (BSN.sinOddQ 137438953472) 0 3 hp760217 hp737937 hp760216 rfl rfl rfl

noncomputable def hp760222 := @BSN.sin_arg_round Bool.false 67108829 67108864 hp760212 hp619237 215750069919 137438953472 21801270 21780000 (hp760220 (hp760221 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760223 := hp760213 67108829 67108864 267 1000000000000000 21780000 10890000 hp760214 BSN.pi_near_15 hp760222 rfl rfl

noncomputable def hp760224 := @hp760168 489 67108864 Bool.true 67108829 67108864 1 10890000 hp760211 (Enclosure.sfrac_false_div 56396647209 33554432) (hp760223 rfl rfl) rfl

noncomputable def hp760225 := @hp760165 67108829 67108864 337019929 45675970560000 536870632 536870912 3962 536870912 (@hp760166 Bool.true 67108829 67108864 337019929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000)) (@hp760167 5392318864 730815528960000 67108829 67108864 337019929 45675970560000 (hp760224 rfl) rfl))

noncomputable def hp760226 := @hp760171 hp738659 902346355344 536870912 3910 536870912 (@hp760175 hp760169 hp760170 129935929114076764919 hp738659 (hp760177 rfl rfl rfl rfl rfl) (hp760180 (hp760210 rfl) (Enclosure.Real.IsNear.const Bool.true hp760173 hp760174) rfl rfl)) rfl

noncomputable def hp760227 := hp760164 (BSN.cos_quad_nat1 469 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 465811572 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl rfl (hp760225 rfl) hp760226

noncomputable def hp760228 := nat_lit 1488498945540222478723359766800625

noncomputable def hp760229 := BSN.sin_dyadic_bound_f 196420645 536870912 2 1 536870912 268435456 hp760228 hp708890 hp760228 hp760228 hp708891

noncomputable def hp760230 := @BSN.binarySplit_of_base (BSN.sinEvenP 196420645) (BSN.sinEvenQ 536870912) 0 1 hp760228 hp708890 hp760228 rfl rfl rfl

noncomputable def hp760231 := hp760229 hp760228 192067898 rfl rfl rfl rfl rfl rfl rfl rfl (hp760230 rfl)

noncomputable def hp760232 := @BSN.binarySplit_of_base (BSN.sinOddP 196420645) (BSN.sinOddQ 536870912) 0 1 hp760228 hp708891 hp760228 rfl rfl rfl

noncomputable def hp760233 := nat_lit 25421387652196369498275006500519405494619534172411562073563543383478535425

noncomputable def hp760234 := nat_lit 10231193364225285899259509531575042776375013761451088591730267920958721

noncomputable def hp760235 := nat_lit 66563260014115079175454787343071130988079887095940313192089336046762231041

noncomputable def hp760236 := BSN.sin_dyadic_bound_f 563950241 536870912 3 2 536870912 268435456 hp760233 hp708845 hp760234 hp760235 hp708848

noncomputable def hp760237 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 563950241) (BSN.sinEvenQ 536870912) 0 2 hp760233 hp708845 hp760234 rfl rfl rfl

noncomputable def hp760238 := hp760236 hp760234 465811572 rfl rfl rfl rfl rfl rfl rfl rfl (hp760237 rfl)

noncomputable def hp760239 := @BSN.binarySplit_of_base2 (BSN.sinOddP 563950241) (BSN.sinOddQ 536870912) 0 2 hp760235 hp708848 hp760234 rfl rfl rfl

noncomputable def hp760240 := hp760227 hd4911 hd4913 hd4915 hd4917 hd4918 (hp760231 (hp760232 rfl) rfl rfl rfl rfl) (hp760238 (hp760239 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760241 := hp760159 (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 360763588 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl rfl (hp760240 rfl rfl rfl rfl rfl) hp760226

noncomputable def hp760242 := nat_lit 3342431370511749043880152522233806317063500461654335874122790358080290816

noncomputable def hp760243 := nat_lit 573321778688162369354789663250281703632449945593575332051189221031936

noncomputable def hp760244 := nat_lit 10026147467977870806901747987374918387783236485071820471704268695798808576

noncomputable def hp760245 := BSN.cos_dyadic_bound_f 393368704 536870912 3 2 536870912 268435456 hp760242 hp708868 hp760243 hp760244 hp708870

noncomputable def hp760246 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 393368704) (BSN.cosEvenQ 536870912) 0 2 hp760242 hp708868 hp760243 rfl rfl rfl

noncomputable def hp760247 := hp760245 hp760243 399092076 rfl rfl rfl rfl rfl rfl rfl rfl (hp760246 rfl)

noncomputable def hp760248 := @BSN.binarySplit_of_base2 (BSN.cosOddP 393368704) (BSN.cosOddQ 536870912) 0 2 hp760244 hp708870 hp760243 rfl rfl rfl

noncomputable def hp760249 := nat_lit 5609191187182188805400814084865100087205471690220073213646704284598690625

noncomputable def hp760250 := nat_lit 1614257909773587364404041451203473648142169571433745393696392937890625

noncomputable def hp760251 := nat_lit 16824345045727019241473634171692893314320130731517352150152720067920290625

noncomputable def hp760252 := BSN.cos_dyadic_bound_f 447709815 536870912 3 2 536870912 268435456 hp760249 hp708868 hp760250 hp760251 hp708870

noncomputable def hp760253 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 447709815) (BSN.cosEvenQ 536870912) 0 2 hp760249 hp708868 hp760250 rfl rfl rfl

noncomputable def hp760254 := hp760252 hp760250 360763588 rfl rfl rfl rfl rfl rfl rfl rfl (hp760253 rfl)

noncomputable def hp760255 := @BSN.binarySplit_of_base2 (BSN.cosOddP 447709815) (BSN.cosOddQ 536870912) 0 2 hp760251 hp708870 hp760250 rfl rfl rfl

noncomputable def hp760256 := hp760241 hd4920 hd4922 hd4924 hd4926 hd4918 (hp760247 (hp760248 rfl) rfl rfl rfl rfl) (hp760254 (hp760255 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760257 := hp760155 (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 267832368 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl rfl (hp760256 rfl rfl rfl rfl rfl) hp760226

noncomputable def hp760258 := nat_lit 46284886983782614507653277109566582451907614650728306708052060203290249893769463726881943090817816742275506835456

noncomputable def hp760259 := nat_lit 37664915320808559894975813843337298986202043900894338367402308086545363888950939239238465476356692613861376

noncomputable def hp760260 := nat_lit 280346272613971528136905016811196729564196004734130268261441867680504520942093753141033673112069324645970292838400

noncomputable def hp760261 := BSN.cos_dyadic_bound_f 760900874 536870912 4 3 536870912 268435456 hp760258 hp716712 hp760259 hp760260 hp716714

noncomputable def hp760262 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 760900874) (BSN.cosEvenQ 536870912) 0 3 hp760258 hp716712 hp760259 rfl rfl rfl

noncomputable def hp760263 := hp760261 hp760259 82090686 rfl rfl rfl rfl rfl rfl rfl rfl (hp760262 rfl)

noncomputable def hp760264 := @BSN.binarySplit_of_base3 (BSN.cosOddP 760900874) (BSN.cosOddQ 536870912) 0 3 hp760260 hp716714 hp760259 rfl rfl rfl

noncomputable def hp760265 := nat_lit 13840145532065194453910724914163422708248544063623111771658076291292648545768629225221376444591421785548822575921

noncomputable def hp760266 := nat_lit 1012117192895951077139754939803510264009603639842037013740368886108799160721756738673941652804042130357041

noncomputable def hp760267 := nat_lit 83923305911771373965798283089598667959545886334469462352836819367779979966349194576917533717381075189292986432305

noncomputable def hp760268 := BSN.cos_dyadic_bound_f 562906029 536870912 4 3 536870912 268435456 hp760265 hp716712 hp760266 hp760267 hp716714

noncomputable def hp760269 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 562906029) (BSN.cosEvenQ 536870912) 0 3 hp760265 hp716712 hp760266 rfl rfl rfl

noncomputable def hp760270 := hp760268 hp760266 267832368 rfl rfl rfl rfl rfl rfl rfl rfl (hp760269 rfl)

noncomputable def hp760271 := @BSN.binarySplit_of_base3 (BSN.cosOddP 562906029) (BSN.cosOddQ 536870912) 0 3 hp760267 hp716714 hp760266 rfl rfl rfl

noncomputable def hp760272 := hp760257 hd4928 hd4930 hd4932 hd4934 hd4918 (hp760263 (hp760264 rfl) rfl rfl rfl rfl) (hp760270 (hp760271 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760273 := hp760151 (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 271913850 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl rfl (hp760272 rfl rfl rfl rfl rfl) hp760226

noncomputable def hp760274 := nat_lit 571927855120570511046759282093414491636026295526770266514818774287114496

noncomputable def hp760275 := nat_lit 16791111255384038215336121411630019530581071303245218688114228060416

noncomputable def hp760276 := nat_lit 1715749983139200765063847174037420214869017724437704309107080094405222656

noncomputable def hp760277 := BSN.cos_dyadic_bound_f 253008394 536870912 3 2 536870912 268435456 hp760274 hp708868 hp760275 hp760276 hp708870

noncomputable def hp760278 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 253008394) (BSN.cosEvenQ 536870912) 0 2 hp760274 hp708868 hp760275 rfl rfl rfl

noncomputable def hp760279 := hp760277 hp760275 478349157 rfl rfl rfl rfl rfl rfl rfl rfl (hp760278 rfl)

noncomputable def hp760280 := @BSN.binarySplit_of_base2 (BSN.cosOddP 253008394) (BSN.cosOddQ 536870912) 0 2 hp760276 hp708870 hp760275 rfl rfl rfl

noncomputable def hp760281 := nat_lit 13381298781709543971929621491640252952771184827217609906509734385496926014703300356595889766605903448040000000000

noncomputable def hp760282 := nat_lit 914817937087771027292406061816162010131064052347777239541272358666864398658527538574462890625000000000000

noncomputable def hp760283 := nat_lit 81142258180328678995855085672367632403520747380897131634280723427275954402497553306797338621820955084776000000000

noncomputable def hp760284 := BSN.cos_dyadic_bound_f 558184650 536870912 4 3 536870912 268435456 hp760281 hp716712 hp760282 hp760283 hp716714

noncomputable def hp760285 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 558184650) (BSN.cosEvenQ 536870912) 0 3 hp760281 hp716712 hp760282 rfl rfl rfl

noncomputable def hp760286 := hp760284 hp760282 271913850 rfl rfl rfl rfl rfl rfl rfl rfl (hp760285 rfl)

noncomputable def hp760287 := @BSN.binarySplit_of_base3 (BSN.cosOddP 558184650) (BSN.cosOddQ 536870912) 0 3 hp760283 hp716714 hp760282 rfl rfl rfl

noncomputable def hp760288 := hp760273 hd4936 hd4938 hd4940 hd4942 hd4918 (hp760279 (hp760280 rfl) rfl rfl rfl rfl) (hp760286 (hp760287 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760289 := hp760146 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 471555208 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl rfl (hp760288 rfl rfl rfl rfl rfl) hp760226

noncomputable def hp760290 := nat_lit 217419771729550826675206251517530188657346168029179030323347127096556321

noncomputable def hp760291 := nat_lit 2426670545691729391843598620396215230743624402414746247296716094241

noncomputable def hp760292 := nat_lit 652254461847561096566835067355349773541577016838732261477546787857480481

noncomputable def hp760293 := BSN.cos_dyadic_bound_f 198667283 536870912 3 2 536870912 268435456 hp760290 hp708868 hp760291 hp760292 hp708870

noncomputable def hp760294 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 198667283) (BSN.cosEvenQ 536870912) 0 2 hp760290 hp708868 hp760291 rfl rfl rfl

noncomputable def hp760295 := hp760293 hp760291 500530374 rfl rfl rfl rfl rfl rfl rfl rfl (hp760294 rfl)

noncomputable def hp760296 := @BSN.binarySplit_of_base2 (BSN.cosOddP 198667283) (BSN.cosOddQ 536870912) 0 2 hp760292 hp708870 hp760291 rfl rfl rfl

noncomputable def hp760297 := nat_lit 715580198721297875413759775874434005638957557947399284609940961503190625

noncomputable def hp760298 := nat_lit 26284950617821222368973550316137320349904565366518251952991250390625

noncomputable def hp760299 := nat_lit 2146688026262657983796541380522669742276172864711464817325916902008790625

noncomputable def hp760300 := BSN.cos_dyadic_bound_f 267586005 536870912 3 2 536870912 268435456 hp760297 hp708868 hp760298 hp760299 hp708870

noncomputable def hp760301 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 267586005) (BSN.cosEvenQ 536870912) 0 2 hp760297 hp708868 hp760298 rfl rfl rfl

noncomputable def hp760302 := hp760300 hp760298 471555208 rfl rfl rfl rfl rfl rfl rfl rfl (hp760301 rfl)

noncomputable def hp760303 := @BSN.binarySplit_of_base2 (BSN.cosOddP 267586005) (BSN.cosOddQ 536870912) 0 2 hp760299 hp708870 hp760298 rfl rfl rfl

noncomputable def hp760304 := hp760289 hd4944 hd4946 hd4961 hd4963 hd4918 (hp760295 (hp760296 rfl) rfl rfl rfl rfl) (hp760302 (hp760303 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760305 := @hp760141 208269 268435456 (hp760304 rfl rfl rfl rfl rfl) (hp760304 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp760306 := @hp760139 Bool.true 90728811 33554432 208269 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 858353 1000)) (Enclosure.sfrac Bool.false 858353 1000) 11) hp760305

noncomputable def hp760307 := @Enclosure.Real.IsNear.mulLit_tf hp760130 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1))) 19629461 67108864 1

noncomputable def hp760308 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp760129 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760309 := @hp760308 1 1 0 1 19629461 67108864 1 67108864 19629461 67108864 1

noncomputable def hp760310 := @Enclosure.Real.IsNear.of_eq (hp760129 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760311 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 858353 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760312 := @hp760310 (@Inv.inv Real Real.instInv (Real.sqrt hp760131)) Bool.false 19629461 67108864 1 67108864 (hp760311 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 858353 1000) 858353 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000))))

noncomputable def hp760313 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp760131)) Bool.false 19629461 67108864 1 67108864 19629461 67108864

noncomputable def hp760314 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp760131) Bool.false 229430630 67108864 6 67108864 114715315 33554432 3 33554432

noncomputable def hp760315 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 858353 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760316 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 858353 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760317 := @hp760316 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 858353 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9167816895571

noncomputable def hp760318 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 858353 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 858353 1000 0

noncomputable def hp760319 := @hp760318 1 10680707 67108864 1 67108864 9167816895571 67108864000 858353 67108864000 (Enclosure.Real.IsNear.const Bool.false 858353 1000) hd4949

noncomputable def hp760320 := @hp760317 67108864000 858353 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 858353 1000) 858353 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000))) (hp760319 rfl)

noncomputable def hp760321 := @hp760315 9167816895571 67108864000 858353 67108864000 392186728 392186766 33554432 hp760320 rfl rfl rfl

noncomputable def hp760322 := @Enclosure.Real.IsNear.recentre' hp760131 Bool.false 784373494 67108864 38 67108864 392186747 33554432 19 33554432 (hp760321 rfl rfl rfl)

noncomputable def hp760323 := @Enclosure.Real.IsNear.sqrt_image hp760131 392186747 33554432 19 33554432 114715312 114715318 33554432 (hp760322 rfl) rfl rfl

noncomputable def hp760324 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp760131) 114715315 33554432 3 33554432 9814730 9814731 33554432 (hp760314 (hp760323 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp760325 := @hp760309 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp760312 (@hp760313 1 67108864 (hp760324 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp760326 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760327 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp760328 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1))) (hp760326 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760327 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp760329 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 858353 1000) 858353 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl

noncomputable def hp760330 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760331 := @hp760330 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760327 (Enclosure.sfrac Bool.false 1 16)))) 88455219

noncomputable def hp760332 := @hp760331 33554432 107 4194304 5691597 33554432 48848663 5709496320000 503451459094743 1125899906842624 205998537780659 7663156240947609600

noncomputable def hp760333 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760334 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760335 := @hp760333 (@Neg.neg Real Real.instNeg hp760334) Bool.true 88455219 33554432 107 4194304 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760336 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760337 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp760338 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp760339 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 290132301) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp760340 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1))) Bool.false 20416245730955482822225

noncomputable def hp760341 := nat_lit 512735432970161230558633413

noncomputable def hp760342 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp760343 := @Enclosure.Real.IsNear.subLit_ff_p hp760131 (Enclosure.sfrac Bool.false 11 1) 392186747 33554432 19 33554432 11 1 0

noncomputable def hp760344 := @hp760342 500000000000000 23087995 33554432 19 33554432 20416245730955482822225 4722366482869645213696 hp760341 hp682805 hd4948 (@hp760343 1 23087995 23087995 33554432 19 33554432 (hp760322 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760345 := @hp760339 290132301 67108864 15 4194304 Bool.true 25456947 67108864 1 10890000 (@hp760340 4722366482869645213696 hp760341 hp682805 290132301 67108864 15 4194304 (hp760344 rfl) rfl) (Enclosure.sfrac_false_div 290132301 67108864)

noncomputable def hp760346 := nat_lit 11428851336405119225823232

noncomputable def hp760347 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 290132301) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp760346) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp760348 := BSN.sin_reduce_arg_pos_rat_q2 290132301 67108864 226375608064910080 72057594037927936 0 hp760346 hp617687 rfl rfl rfl rfl

noncomputable def hp760349 := nat_lit 1770106810383956384985427400766515293256926901611440337213403036709568662529385666106748320579378762086700498800487127015401808843256458915521

noncomputable def hp760350 := nat_lit 336878578758474630163725056768327162526685379717299828316200633370044478739021475752926085866848168638338743115089713489826128183439041

noncomputable def hp760351 := nat_lit 10730345915983709549217063764726674617352227631002691637451994058776012683765044849075214169256922828524848801800208213777703376962298737864385

noncomputable def hp760352 := BSN.cos_dyadic_bound_f 162413745903 137438953472 4 3 67108864 21801270 hp760349 hp740177 hp760350 hp760351 hp740180

noncomputable def hp760353 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 162413745903) (BSN.cosEvenQ 137438953472) 0 3 hp760349 hp740177 hp760350 rfl rfl rfl

noncomputable def hp760354 := hp760352 hp760350 25456947 rfl rfl rfl rfl rfl rfl rfl rfl (hp760353 rfl)

noncomputable def hp760355 := @BSN.binarySplit_of_base3 (BSN.cosOddP 162413745903) (BSN.cosOddQ 137438953472) 0 3 hp760351 hp740180 hp760350 rfl rfl rfl

noncomputable def hp760356 := @BSN.cos_arg_round Bool.false 25456947 67108864 hp760346 hp617687 162413745903 137438953472 21801270 21780000 (hp760354 (hp760355 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760357 := hp760347 25456947 67108864 0 1000000000000000 21780000 10890000 hp760348 BSN.pi_near_15 hp760356 rfl rfl

noncomputable def hp760358 := @hp760337 25456947 67108864 10471519 2854748160000 (@hp760338 25456947 67108864 167544304 45675970560000 25456947 67108864 10471519 2854748160000 (hp760345 (hp760357 rfl rfl) rfl rfl) rfl)

noncomputable def hp760359 := @hp760336 25456947 67108864 10471519 2854748160000 88454363 88456075 33554432 hp760358 rfl rfl rfl

noncomputable def hp760360 := @Enclosure.Real.IsNear.recentre' hp760334 Bool.false 176910438 67108864 1712 67108864 88455219 33554432 107 4194304 (hp760359 rfl rfl rfl)

noncomputable def hp760361 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760327 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp760362 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760327 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 116852855)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp760363 := nat_lit 275911003047622279645367757845

noncomputable def hp760364 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760327 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp760363

noncomputable def hp760365 := nat_lit 40880622173904617920368823878926061

noncomputable def hp760366 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760327 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp760367 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp760368 := @hp760367 (Enclosure.sfrac Bool.false 1 16) 241649045123815 1125899906842624 1514878379 1125899906842624 1 16 0

noncomputable def hp760369 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)) 533055513120025

noncomputable def hp760370 := @hp760369 1125899906842624 877344171 1125899906842624 23087995 33554432 19 33554432 8108396452471981998080 241649045123815 1125899906842624 1514878379

noncomputable def hp760371 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)) 23087995 33554432 19

noncomputable def hp760372 := @hp760371 33554432 23087995 33554432 19 33554432 533055513120025 1125899906842624 877344171 1125899906842624 (@hp760343 1 23087995 23087995 33554432 19 33554432 (hp760322 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760373 := hp760372 (@hp760343 1 23087995 23087995 33554432 19 33554432 (hp760322 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760374 := @hp760370 1125899906842624 (hp760373 rfl) (@hp760343 1 23087995 23087995 33554432 19 33554432 (hp760322 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760375 := @hp760366 500000000000000 312017789301479 1125899906842624 1514878379 1125899906842624 hp760363 hp682141 hp760365 hp682143 hd4948 (@hp760368 1 4992284628823664 312017789301479 1125899906842624 1514878379 1125899906842624 (hp760374 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp760376 := @hp760362 116852855 67108864 71 8388608 Bool.true 5691597 33554432 1 10890000 (@hp760364 hp682141 hp760365 hp682143 116852855 67108864 71 8388608 (hp760375 rfl) rfl) (Enclosure.sfrac_true_div 116852855 67108864)

noncomputable def hp760377 := nat_lit 1539195714083242743277147540057800488495950946502664984802347493428511373206717804710707005398164390625

noncomputable def hp760378 := nat_lit 6481446383485705601497085739199067240200993496508070242463631214723647431102679794555722900390625

noncomputable def hp760379 := nat_lit 9303877138506924463879978865950716720835866451991654880208884618362634157391987063145433459078701990625

noncomputable def hp760380 := BSN.cos_dyadic_bound_t 116852855 67108864 4 3 33554432 10890000 hp760377 hp745658 hp760378 hp760379 hp745661

noncomputable def hp760381 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 116852855) (BSN.cosEvenQ 67108864) 0 3 hp760377 hp745658 hp760378 rfl rfl rfl

noncomputable def hp760382 := hp760380 hp760378 5691597 rfl rfl rfl rfl rfl rfl rfl rfl (hp760381 rfl)

noncomputable def hp760383 := @BSN.binarySplit_of_base3 (BSN.cosOddP 116852855) (BSN.cosOddQ 67108864) 0 3 hp760379 hp745661 hp760378 rfl rfl rfl

noncomputable def hp760384 := hp760376 (BSN.cos_neg_of_bound 116852855 67108864 Bool.true 5691597 33554432 1 10890000 (hp760382 (hp760383 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp760385 := hp760332 (hp760335 (@Enclosure.Real.IsNear.neg hp760334 Bool.false 88455219 33554432 107 4194304 (hp760360 rfl))) (@hp760361 5691597 33554432 781578608 91351941120000 5691597 33554432 48848663 5709496320000 (hp760384 rfl) rfl)

noncomputable def hp760386 := @hp760307 67108864 503451459094743 1125899906842624 205998537780659 7663156240947609600 9882480781693353023523 75557863725914323419136 5396089447885965026669 hp760127 (hp760325 rfl) (@hp760328 Bool.false 503451459094743 1125899906842624 205998537780659 7663156240947609600 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760131 (Enclosure.sfrac Bool.false 11 1)) (hp760329 rfl (hp760134 rfl rfl))) (hp760385 rfl))

noncomputable def hp760387 := @hp760128 537395385163191866287469 hp760127 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 858353 1000))) (@hp760133 537395385163191866287469 hp760127 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 858353 1000) 11 (hp760134 rfl rfl)) (@hp760137 537395385163191866287469 hp760127 hp760306 (hp760386 rfl) rfl rfl))

theorem hd5050 : hp760126 hp760127 := hp760387

noncomputable def hp760388 := nat_lit 80862315281730460232473067

noncomputable def hp760389 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 859631 1000)) Bool.false 425875622419710952815017 151115727451828646838272 hp760388

noncomputable def hp760390 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 859631 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 859631 1000)) Bool.false 425875622419710952815017 151115727451828646838272

noncomputable def hp760391 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 859631 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760392 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp760391 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760393 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 859631 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760394 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp760392 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp760395 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 859631 1000)) hp760394 Bool.false 425875622419710952815017 151115727451828646838272

noncomputable def hp760396 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 859631 1000) 859631 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl

noncomputable def hp760397 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp760392 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp760398 := nat_lit 28580029225879733251773393010688

noncomputable def hp760399 := @hp760397 180227725 67108864 104291 134217728 20038864843794839714217 151115727451828646838272 942492529263744953113067 hp755229 hp760398 425875622419710952815017 151115727451828646838272

noncomputable def hp760400 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) 11)

noncomputable def hp760401 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) 11) hp760400

noncomputable def hp760402 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) 11)

noncomputable def hp760403 := @hp760402 720910900 536870912 208582 536870912 720910900 536870912 208582 536870912 774072184707481600 180227725 67108864

noncomputable def hp760404 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp760405 := hp760404 BSN.quadSignPos 9 10 11 859631 1000 188 240 536870912 268435456 9007199254740992

noncomputable def hp760406 := hp760405 Bool.false 904033486930 3916 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp760407 := hp760406 Bool.false 405813442 179061 Bool.true 91387739 Bool.true 225700780 28296951008113761 1 Bool.false 529111531

noncomputable def hp760408 := hp760407 Bool.false Bool.false 490123185 Bool.false Bool.false 720910900 208582 BSN.abs_quadSignPos (BSN.cos_quad_nat0 188 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 529111531 536870912) BSN.abs_quadSignPos

noncomputable def hp760409 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp760410 := hp760409 BSN.quadSignNeg 7 8 9 859631 1000 65 130 536870912 268435456 9007199254740992

noncomputable def hp760411 := hp760410 Bool.false 904033486930 3916 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp760412 := hp760411 Bool.false 731877617 146238 Bool.true 835940226 Bool.true 378615025 28296951008113761 1 Bool.false 536820262

noncomputable def hp760413 := hp760412 Bool.true Bool.false 408808645 Bool.true Bool.false 405813442 179061 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536820262 536870912) BSN.abs_quadSignNeg

noncomputable def hp760414 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp760415 := hp760414 BSN.quadSignPos 5 6 7 859631 1000 91 7 536870912 268435456 9007199254740992

noncomputable def hp760416 := hp760415 Bool.false 904033486930 3916 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp760417 := hp760416 Bool.false 563843099 108671 Bool.false 375353769 Bool.false 71592911 28296951008113761 1 Bool.false 345512944

noncomputable def hp760418 := hp760417 Bool.false Bool.false 71380912 Bool.false Bool.false 731877617 146238 BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 345512944 536870912) BSN.abs_quadSignPos

noncomputable def hp760419 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp760420 := hp760419 BSN.quadSignPos 3 4 5 859631 1000 313 191 536870912 268435456 9007199254740992

noncomputable def hp760421 := hp760420 Bool.false 904033486930 3916 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp760422 := hp760421 Bool.false 618127005 64229 Bool.false 286019742 Bool.false 187257373 28296951008113761 1 Bool.false 272680481

noncomputable def hp760423 := hp760422 Bool.true Bool.false 183483531 Bool.false Bool.false 563843099 108671 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 313 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 272680481 536870912) BSN.abs_quadSignPos

noncomputable def hp760424 := hp760404 BSN.quadSignNeg 1 2 3 859631 1000 692 470 536870912 268435456 9007199254740992

noncomputable def hp760425 := hp760424 Bool.false 904033486930 3916 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp760426 := hp760425 Bool.false 536870904 3970 Bool.false 564654540 Bool.false 653985987 28296951008113761 1 Bool.false 266315563

noncomputable def hp760427 := hp760426 Bool.false Bool.false 185428923 Bool.true Bool.false 618127005 64229 BSN.abs_quadSignPos (BSN.cos_quad_nat0 692 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 266315563 536870912) BSN.abs_quadSignNeg

noncomputable def hp760428 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) 1) Bool.false

noncomputable def hp760429 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)))

noncomputable def hp760430 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000))) Bool.false 67108863 67108864

noncomputable def hp760431 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 56502092933) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 56502092933 33554432

noncomputable def hp760432 := nat_lit 22033311123624646333781987067128940454258541720874747786637

noncomputable def hp760433 := nat_lit 13084740784868453167751778642296552100722937133478707200

noncomputable def hp760434 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) Bool.false hp760432 hp760433 130128780596631075113

noncomputable def hp760435 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 859631 4000) (Real.log (Enclosure.sfrac Bool.false 2955862824644 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1719262))))))

noncomputable def hp760436 := nat_lit 225321146664294214641220057832480000

noncomputable def hp760437 := nat_lit 1162158439249023903960969285469011689280

noncomputable def hp760438 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp760435 (Enclosure.sfrac Bool.false 859631 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 859631 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp760436 hp760437)) Bool.false

noncomputable def hp760439 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 859631 1000) 859631 1000 2955862824644 16000000 1719262

noncomputable def hp760440 := hp760439 4000 2000 hp760436 hp760437 (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl rfl rfl rfl

noncomputable def hp760441 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp760435 (Enclosure.sfrac Bool.false 859631 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 859631 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp760436 hp760437) 6066866731115375666453 3602879701896396800

noncomputable def hp760442 := nat_lit 7050659559559886826810235861481260945362733350679919291723840

noncomputable def hp760443 := @hp760441 130128780596631075113 hp738659 hp760436 hp760437 0 1 hp760442 hp760432 hp760433 130128780596631075113 hp738659

noncomputable def hp760444 := @Enclosure.Real.IsNear.subLit_ff_p (hp760435 (Enclosure.sfrac Bool.false 859631 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 859631 2000) (Real.log Real.pi)) 39197825690767749888361 18014398509481984000 10845403414893203 4356000000000000000000

noncomputable def hp760445 := nat_lit 2035702671822731569544518696960000

noncomputable def hp760446 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 859631 4000) (Real.log (Enclosure.sfrac Bool.false 2955862824644 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1719262))))))

noncomputable def hp760447 := @hp760446 (Enclosure.sfrac Bool.false 859631 2000) 46940693393320003582313 18014398509481984000 10845403414893203 4356000000000000000000 859631 2000 0

noncomputable def hp760448 := nat_lit 78395651381535499776722000

noncomputable def hp760449 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 859631 4000) (Real.log (Enclosure.sfrac Bool.false 2955862824644 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1719262))))) 46947765011678852374313

noncomputable def hp760450 := nat_lit 105701044637334335782197489322241818624

noncomputable def hp760451 := @hp760449 18014398509481984000 10745403414348703 4356000000000000000000 883952294856099 2251799813685248 200000001089 8712000000000000000 hp760450 46940693393320003582313 18014398509481984000 10845403414893203

noncomputable def hp760452 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 859631 4000) (Real.log (Enclosure.sfrac Bool.false 2955862824644 16000000)) 859631 4000 0 1 54613857587358823 4503599627370496

noncomputable def hp760453 := nat_lit 117282366123053803901026304

noncomputable def hp760454 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2955862824644) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp760453 hp617687

noncomputable def hp760455 := BSN.log_rat_reduce_isNear 2955862824644 16000000 17 5911725649288 4194304000000 92129830 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp760456 := nat_lit 112805485105371182962408036141152760810833457451400018175427675706977155952007307234962081880280601086447195096499031894688944619520

noncomputable def hp760457 := nat_lit 1105143535020568225046757685142376948090663223749751243700640915333978638667334754206185385873235358819994390220459259821848264704

noncomputable def hp760458 := nat_lit 206016110526158090600303524358031370203226174735074378738383478217240309102663206830729214552982990683679919777778704056320

noncomputable def hp760459 := BSN.log_dyadic_bound 858710824644 5053014824644 6 5 hp760456 268435456 87120000 hp760457 hp760458 92129830 5911725649288

noncomputable def hp760460 := hp760459 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp760461 := @BSN.binarySplit_of_base5 (BSN.artanhP 858710824644) (BSN.artanhQ 5053014824644) 0 5 hp760457 hp760456 hp760458 rfl rfl rfl

noncomputable def hp760462 := hp760455 rfl rfl rfl rfl (hp760460 (hp760461 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp760463 := @hp760452 12500018513 1089000000000000000 46947765011678852374313 18014398509481984000 10745403414348703 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 859631 4000) (BSN.isNear_log_sfrac 2955862824644 16000000 54613857587358823 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp760454 1000001481040000 87120000000000000000000 54613857587358823 4503599627370496 12500018513 1089000000000000000 (hp760462 rfl rfl rfl) rfl)) rfl

noncomputable def hp760464 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1719262)))) 1 4

noncomputable def hp760465 := @hp760464 0 1 883952294856099 562949953421312 200000001089 2178000000000000000 883952294856099 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp760466 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1719262))) 884279719003555 562949953421312 1

noncomputable def hp760467 := @hp760466 2000000000000000 19516 33554432 1 10890000 29660517168992923680768 883952294856099 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp760468 := BSN.arctan_dyadic_bound_f 1000 1719262 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp760469 := hp760468 1 19516 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1719262) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1719262) 0 0 rfl)

noncomputable def hp760470 := hp760465 (hp760467 (hp760469 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp760471 := @hp760444 33019080889191 67108864000 2578893 536870912000 hp760445 6066866731115375666453 3602879701896396800 130128780596631075113 hp738659 (@hp760447 1 hp760448 39197825690767749888361 18014398509481984000 10845403414893203 4356000000000000000000 (@hp760451 4356000000000000000000 hp760463 hp760470 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 859631 2000) rfl rfl)

noncomputable def hp760472 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 859631 2000) (Real.log Real.pi) 859631 2000 0 1 38410761 33554432

noncomputable def hp760473 := hp760471 (@hp760472 3 268435456 33019080889191 67108864000 2578893 536870912000 (Enclosure.Real.IsNear.const Bool.false 859631 2000) hd4909 rfl) rfl

noncomputable def hp760474 := @hp760434 hp738659 56502092933 33554432 245 33554432 (@hp760438 hp760432 hp760433 130128780596631075113 hp738659 (hp760440 rfl rfl rfl rfl rfl) (hp760443 (hp760473 rfl) (Enclosure.Real.IsNear.const Bool.true hp760436 hp760437) rfl rfl)) rfl

noncomputable def hp760475 := nat_lit 7595551189745010334498816

noncomputable def hp760476 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 56502092933) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp760475) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp760477 := BSN.sin_reduce_arg_pos_rat_q3 56502092933 33554432 226375608064910080 72057594037927936 267 hp760475 hp619237 rfl rfl rfl rfl

noncomputable def hp760478 := nat_lit 14377698050550169020699947632408648796052060378944606960329676293539020272858472215649278866542150491943127263474113509869904945115817231650816

noncomputable def hp760479 := nat_lit 10245045257414129805864453582004214965185320917976919452862286028830013427375244171916378017860898923605013568404663988348931708208418816

noncomputable def hp760480 := nat_lit 71799176546970326370430452994209256278485196394364360735123486706584638273991837465255943362746063759993371868950561510858604328690102601650176

noncomputable def hp760481 := BSN.sin_dyadic_bound_f 215878548878 137438953472 4 3 67108864 21801270 hp760478 hp737934 hp760479 hp760480 hp737937

noncomputable def hp760482 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215878548878) (BSN.sinEvenQ 137438953472) 0 3 hp760478 hp737934 hp760479 rfl rfl rfl

noncomputable def hp760483 := hp760481 hp760479 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (hp760482 rfl)

noncomputable def hp760484 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215878548878) (BSN.sinOddQ 137438953472) 0 3 hp760480 hp737937 hp760479 rfl rfl rfl

noncomputable def hp760485 := @BSN.sin_arg_round Bool.false 67108863 67108864 hp760475 hp619237 215878548878 137438953472 21801270 21780000 (hp760483 (hp760484 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760486 := hp760476 67108863 67108864 267 1000000000000000 21780000 10890000 hp760477 BSN.pi_near_15 hp760485 rfl rfl

noncomputable def hp760487 := @hp760431 245 33554432 Bool.false 67108863 67108864 1 10890000 hp760474 (Enclosure.sfrac_false_div 56502092933 33554432) (hp760486 rfl rfl) rfl

noncomputable def hp760488 := @hp760428 67108863 67108864 168850277 22837985280000 536870904 536870912 3970 536870912 (@hp760429 Bool.false 67108863 67108864 168850277 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000)) (@hp760430 2701604432 365407764480000 67108863 67108864 168850277 22837985280000 (hp760487 rfl) rfl))

noncomputable def hp760489 := @hp760434 hp738659 904033486930 536870912 3916 536870912 (@hp760438 hp760432 hp760433 130128780596631075113 hp738659 (hp760440 rfl rfl rfl rfl rfl) (hp760443 (hp760473 rfl) (Enclosure.Real.IsNear.const Bool.true hp760436 hp760437) rfl rfl)) rfl

noncomputable def hp760490 := hp760427 (BSN.cos_quad_nat2 470 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 185428923 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl rfl (hp760488 rfl) hp760489

noncomputable def hp760491 := nat_lit 14013036440520711713173417534105024513728554927785460212359793365609371753329096338410708453694887784873984000000

noncomputable def hp760492 := nat_lit 1050494764415372986845165778734986874257861390686288049247912308495566025336809051894924578816000000000000

noncomputable def hp760493 := nat_lit 84971166371746854302470759818574437663812646037373712966153645562280803119801424788113745934417664101161369600000

noncomputable def hp760494 := BSN.cos_dyadic_bound_f 564654540 536870912 4 3 536870912 268435456 hp760491 hp716712 hp760492 hp760493 hp716714

noncomputable def hp760495 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 564654540) (BSN.cosEvenQ 536870912) 0 3 hp760491 hp716712 hp760492 rfl rfl rfl

noncomputable def hp760496 := hp760494 hp760492 266315563 rfl rfl rfl rfl rfl rfl rfl rfl (hp760495 rfl)

noncomputable def hp760497 := @BSN.binarySplit_of_base3 (BSN.cosOddP 564654540) (BSN.cosOddQ 536870912) 0 3 hp760493 hp716714 hp760492 rfl rfl rfl

noncomputable def hp760498 := nat_lit 25230591140322166022163375363910211154568002144711304258378505666209755094971547292864554171451720023723180306161

noncomputable def hp760499 := nat_lit 6120984971697951140168483579666649556273627072338102434832228969306076852890588685661277656054432571338481

noncomputable def hp760500 := nat_lit 152931987259527058364681645438794875877640936986895066338435999150740733017459261004228689637485161059675477651185

noncomputable def hp760501 := BSN.cos_dyadic_bound_f 653985987 536870912 4 3 536870912 268435456 hp760498 hp716712 hp760499 hp760500 hp716714

noncomputable def hp760502 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 653985987) (BSN.cosEvenQ 536870912) 0 3 hp760498 hp716712 hp760499 rfl rfl rfl

noncomputable def hp760503 := hp760501 hp760499 185428923 rfl rfl rfl rfl rfl rfl rfl rfl (hp760502 rfl)

noncomputable def hp760504 := @BSN.binarySplit_of_base3 (BSN.cosOddP 653985987) (BSN.cosOddQ 536870912) 0 3 hp760500 hp716714 hp760499 rfl rfl rfl

noncomputable def hp760505 := hp760490 hd4911 hd4913 hd4915 hd4917 hd4918 (hp760496 (hp760497 rfl) rfl rfl rfl rfl) (hp760503 (hp760504 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760506 := hp760423 (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 183483531 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl rfl (hp760505 rfl rfl rfl rfl rfl) hp760489

noncomputable def hp760507 := nat_lit 1681345226597200161835282492116922691290827835168944725894687063579132160

noncomputable def hp760508 := nat_lit 44788661567793747719222892894279726855076330125839532458814622761216

noncomputable def hp760509 := nat_lit 4403450697540604948262765880384397262394402778050841970481151847603732736

noncomputable def hp760510 := BSN.sin_dyadic_bound_f 286019742 536870912 3 2 536870912 268435456 hp760507 hp708845 hp760508 hp760509 hp708848

noncomputable def hp760511 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 286019742) (BSN.sinEvenQ 536870912) 0 2 hp760507 hp708845 hp760508 rfl rfl rfl

noncomputable def hp760512 := hp760510 hp760508 272680481 rfl rfl rfl rfl rfl rfl rfl rfl (hp760511 rfl)

noncomputable def hp760513 := @BSN.binarySplit_of_base2 (BSN.sinOddP 286019742) (BSN.sinOddQ 536870912) 0 2 hp760509 hp708848 hp760508 rfl rfl rfl

noncomputable def hp760514 := nat_lit 1229576929191660416901990979154641

noncomputable def hp760515 := BSN.sin_dyadic_bound_f 187257373 536870912 2 1 536870912 268435456 hp760514 hp708890 hp760514 hp760514 hp708891

noncomputable def hp760516 := @BSN.binarySplit_of_base (BSN.sinEvenP 187257373) (BSN.sinEvenQ 536870912) 0 1 hp760514 hp708890 hp760514 rfl rfl rfl

noncomputable def hp760517 := hp760515 hp760514 183483531 rfl rfl rfl rfl rfl rfl rfl rfl (hp760516 rfl)

noncomputable def hp760518 := @BSN.binarySplit_of_base (BSN.sinOddP 187257373) (BSN.sinOddQ 536870912) 0 1 hp760514 hp708891 hp760514 rfl rfl rfl

noncomputable def hp760519 := hp760506 hd4920 hd4922 hd4924 hd4926 hd4918 (hp760512 (hp760513 rfl) rfl rfl rfl rfl) (hp760517 (hp760518 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760520 := hp760418 (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 71380912 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl rfl (hp760519 rfl rfl rfl rfl rfl) hp760489

noncomputable def hp760521 := nat_lit 4987222243153337228572318986765074437091890163599371844812463261997624385

noncomputable def hp760522 := nat_lit 394027241674764673690636375891598271033626005584413890720610461183041

noncomputable def hp760523 := nat_lit 13061134592724600265360574411204703795182800748275027685352427554961386561

noncomputable def hp760524 := BSN.sin_dyadic_bound_f 375353769 536870912 3 2 536870912 268435456 hp760521 hp708845 hp760522 hp760523 hp708848

noncomputable def hp760525 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 375353769) (BSN.sinEvenQ 536870912) 0 2 hp760521 hp708845 hp760522 rfl rfl rfl

noncomputable def hp760526 := hp760524 hp760522 345512944 rfl rfl rfl rfl rfl rfl rfl rfl (hp760525 rfl)

noncomputable def hp760527 := @BSN.binarySplit_of_base2 (BSN.sinOddP 375353769) (BSN.sinOddQ 536870912) 0 2 hp760523 hp708848 hp760522 rfl rfl rfl

noncomputable def hp760528 := nat_lit 26271210577824643962851054274241

noncomputable def hp760529 := BSN.sin_dyadic_bound_f 71592911 536870912 2 1 536870912 268435456 hp760528 hp708890 hp760528 hp760528 hp708891

noncomputable def hp760530 := @BSN.binarySplit_of_base (BSN.sinEvenP 71592911) (BSN.sinEvenQ 536870912) 0 1 hp760528 hp708890 hp760528 rfl rfl rfl

noncomputable def hp760531 := hp760529 hp760528 71380912 rfl rfl rfl rfl rfl rfl rfl rfl (hp760530 rfl)

noncomputable def hp760532 := @BSN.binarySplit_of_base (BSN.sinOddP 71592911) (BSN.sinOddQ 536870912) 0 1 hp760528 hp708891 hp760528 rfl rfl rfl

noncomputable def hp760533 := hp760520 hd4928 hd4930 hd4932 hd4934 hd4918 (hp760526 (hp760527 rfl) rfl rfl rfl rfl) (hp760531 (hp760532 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760534 := hp760413 (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 408808645 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl rfl (hp760533 rfl rfl rfl rfl rfl) hp760489

noncomputable def hp760535 := nat_lit 175227630816649830861356658498119448435184233621020999334850571735926948504541854665009090503787600210023158910976

noncomputable def hp760536 := nat_lit 116440132585707277375447325968967494479971998882703085989800513684098457002575968081548532400788574154264576

noncomputable def hp760537 := nat_lit 875086973626786599425300234390579102951921585642715817566534947119853253753417280986519863050034534614975030235136

noncomputable def hp760538 := BSN.sin_dyadic_bound_f 835940226 536870912 4 3 536870912 268435456 hp760535 hp642702 hp760536 hp760537 hp642705

noncomputable def hp760539 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 835940226) (BSN.sinEvenQ 536870912) 0 3 hp760535 hp642702 hp760536 rfl rfl rfl

noncomputable def hp760540 := hp760538 hp760536 536820262 rfl rfl rfl rfl rfl rfl rfl rfl (hp760539 rfl)

noncomputable def hp760541 := @BSN.binarySplit_of_base3 (BSN.sinOddP 835940226) (BSN.sinOddQ 536870912) 0 3 hp760537 hp642705 hp760536 rfl rfl rfl

noncomputable def hp760542 := nat_lit 2868428932526027128670497905640575479800700630271248232788164844962890625

noncomputable def hp760543 := nat_lit 422262735165142900597727617600949654016505421022887212646636962890625

noncomputable def hp760544 := nat_lit 8604442272107751100210298261686524540094068879971698923939201260962890625

noncomputable def hp760545 := BSN.cos_dyadic_bound_f 378615025 536870912 3 2 536870912 268435456 hp760542 hp708868 hp760543 hp760544 hp708870

noncomputable def hp760546 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 378615025) (BSN.cosEvenQ 536870912) 0 2 hp760542 hp708868 hp760543 rfl rfl rfl

noncomputable def hp760547 := hp760545 hp760543 408808645 rfl rfl rfl rfl rfl rfl rfl rfl (hp760546 rfl)

noncomputable def hp760548 := @BSN.binarySplit_of_base2 (BSN.cosOddP 378615025) (BSN.cosOddQ 536870912) 0 2 hp760544 hp708870 hp760543 rfl rfl rfl

noncomputable def hp760549 := hp760534 hd4936 hd4938 hd4940 hd4942 hd4918 (hp760540 (hp760541 rfl) rfl rfl rfl rfl) (hp760547 (hp760548 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760550 := hp760408 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 490123185 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl rfl (hp760549 rfl rfl rfl rfl rfl) hp760489

noncomputable def hp760551 := nat_lit 69751207574595757881938190758641

noncomputable def hp760552 := BSN.cos_dyadic_bound_f 91387739 536870912 2 1 536870912 268435456 hp760551 hp708767 hp760551 hp760551 hp708768

noncomputable def hp760553 := @BSN.binarySplit_of_base (BSN.cosEvenP 91387739) (BSN.cosEvenQ 536870912) 0 1 hp760551 hp708767 hp760551 rfl rfl rfl

noncomputable def hp760554 := hp760552 hp760551 529111531 rfl rfl rfl rfl rfl rfl rfl rfl (hp760553 rfl)

noncomputable def hp760555 := @BSN.binarySplit_of_base (BSN.cosOddP 91387739) (BSN.cosOddQ 536870912) 0 1 hp760551 hp708768 hp760551 rfl rfl rfl

noncomputable def hp760556 := nat_lit 362183860245637133175400114527897176850154814454815800212979134668800000

noncomputable def hp760557 := nat_lit 6733866151146872957554988405169464250281034353594608140313600000000

noncomputable def hp760558 := nat_lit 1086538113004609105780285233606881191621963881295740211422656776806400000

noncomputable def hp760559 := BSN.cos_dyadic_bound_f 225700780 536870912 3 2 536870912 268435456 hp760556 hp708868 hp760557 hp760558 hp708870

noncomputable def hp760560 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 225700780) (BSN.cosEvenQ 536870912) 0 2 hp760556 hp708868 hp760557 rfl rfl rfl

noncomputable def hp760561 := hp760559 hp760557 490123185 rfl rfl rfl rfl rfl rfl rfl rfl (hp760560 rfl)

noncomputable def hp760562 := @BSN.binarySplit_of_base2 (BSN.cosOddP 225700780) (BSN.cosOddQ 536870912) 0 2 hp760558 hp708870 hp760557 rfl rfl rfl

noncomputable def hp760563 := hp760550 hd4944 hd4946 hd4961 hd4963 hd4918 (hp760554 (hp760555 rfl) rfl rfl rfl rfl) (hp760561 (hp760562 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760564 := @hp760403 104291 134217728 (hp760563 rfl rfl rfl rfl rfl) (hp760563 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp760565 := @hp760401 Bool.false 180227725 67108864 104291 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 859631 1000)) (Enclosure.sfrac Bool.false 859631 1000) 11) hp760564

noncomputable def hp760566 := @Enclosure.Real.IsNear.mulLit_tf hp760392 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1))) 19622161 67108864 1

noncomputable def hp760567 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp760391 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760568 := @hp760567 1 1 0 1 19622161 67108864 1 67108864 19622161 67108864 1

noncomputable def hp760569 := @Enclosure.Real.IsNear.of_eq (hp760391 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760570 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 859631 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760571 := @hp760569 (@Inv.inv Real Real.instInv (Real.sqrt hp760393)) Bool.false 19622161 67108864 1 67108864 (hp760570 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 859631 1000) 859631 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000))))

noncomputable def hp760572 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp760393)) Bool.false 19622161 67108864 1 67108864 19622161 67108864

noncomputable def hp760573 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp760393) Bool.false 229515982 67108864 6 67108864 114757991 33554432 3 33554432

noncomputable def hp760574 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 859631 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760575 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 859631 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760576 := @hp760575 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 859631 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9181466839117

noncomputable def hp760577 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 859631 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 859631 1000 0

noncomputable def hp760578 := @hp760577 1 10680707 67108864 1 67108864 9181466839117 67108864000 859631 67108864000 (Enclosure.Real.IsNear.const Bool.false 859631 1000) hd4949

noncomputable def hp760579 := @hp760576 67108864000 859631 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 859631 1000) 859631 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000))) (hp760578 rfl)

noncomputable def hp760580 := @hp760574 9181466839117 67108864000 859631 67108864000 392478582 392478620 33554432 hp760579 rfl rfl rfl

noncomputable def hp760581 := @Enclosure.Real.IsNear.recentre' hp760393 Bool.false 784957202 67108864 38 67108864 392478601 33554432 19 33554432 (hp760580 rfl rfl rfl)

noncomputable def hp760582 := @Enclosure.Real.IsNear.sqrt_image hp760393 392478601 33554432 19 33554432 114757988 114757994 33554432 (hp760581 rfl) rfl rfl

noncomputable def hp760583 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp760393) 114757991 33554432 3 33554432 9811080 9811081 33554432 (hp760573 (hp760582 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp760584 := @hp760568 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp760571 (@hp760572 1 67108864 (hp760583 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp760585 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760586 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp760587 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1))) (hp760585 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760586 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp760588 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 859631 1000) 859631 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl

noncomputable def hp760589 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760590 := @hp760589 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760586 (Enclosure.sfrac Bool.false 1 16)))) 204456273

noncomputable def hp760591 := @hp760590 67108864 2285 67108864 4994889 33554432 98377951 11418992640000 1021236388988697 2251799813685248 47996619854962441 1532631248189521920000

noncomputable def hp760592 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760593 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760594 := @hp760592 (@Neg.neg Real Real.instNeg hp760593) Bool.true 204456273 67108864 2285 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760595 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760596 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp760597 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp760598 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 293799847) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp760599 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1))) Bool.false 20674326304065546363195

noncomputable def hp760600 := nat_lit 512735432972668237329046981

noncomputable def hp760601 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp760602 := @Enclosure.Real.IsNear.subLit_ff_p hp760393 (Enclosure.sfrac Bool.false 11 1) 392478601 33554432 19 33554432 11 1 0

noncomputable def hp760603 := @hp760601 500000000000000 23379849 33554432 19 33554432 20674326304065546363195 4722366482869645213696 hp760600 hp682805 hd4948 (@hp760602 1 23379849 23379849 33554432 19 33554432 (hp760581 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760604 := @hp760598 293799847 67108864 15 4194304 Bool.true 22027202 67108864 1 10890000 (@hp760599 4722366482869645213696 hp760600 hp682805 293799847 67108864 15 4194304 (hp760603 rfl) rfl) (Enclosure.sfrac_false_div 293799847 67108864)

noncomputable def hp760605 := nat_lit 11957400417971972125753344

noncomputable def hp760606 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 293799847) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp760605) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp760607 := BSN.sin_reduce_arg_pos_rat_q2 293799847 67108864 226375608064910080 72057594037927936 0 hp760605 hp617687 rfl rfl rfl rfl

noncomputable def hp760608 := nat_lit 2121465940200837218092113018008602498082517408232978989939772764697586261775701812765092044552728311688270716081406954793352422956292768952001

noncomputable def hp760609 := nat_lit 579540333250040120748532034346598281368746559258791897011805637281792375387604188351522446231437515591188588208196895223901479025929921

noncomputable def hp760610 := nat_lit 12858306671199086760922438359826630053388172791360514760923880697706570190499772413497566904987450269063169466275127393959244849655497223204545

noncomputable def hp760611 := BSN.cos_dyadic_bound_f 169924880111 137438953472 4 3 67108864 21801270 hp760608 hp740177 hp760609 hp760610 hp740180

noncomputable def hp760612 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 169924880111) (BSN.cosEvenQ 137438953472) 0 3 hp760608 hp740177 hp760609 rfl rfl rfl

noncomputable def hp760613 := hp760611 hp760609 22027202 rfl rfl rfl rfl rfl rfl rfl rfl (hp760612 rfl)

noncomputable def hp760614 := @BSN.binarySplit_of_base3 (BSN.cosOddP 169924880111) (BSN.cosOddQ 137438953472) 0 3 hp760610 hp740180 hp760609 rfl rfl rfl

noncomputable def hp760615 := @BSN.cos_arg_round Bool.false 22027202 67108864 hp760605 hp617687 169924880111 137438953472 21801270 21780000 (hp760613 (hp760614 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760616 := hp760606 22027202 67108864 0 1000000000000000 21780000 10890000 hp760607 BSN.pi_near_15 hp760615 rfl rfl

noncomputable def hp760617 := @hp760596 11013601 33554432 10471519 2854748160000 (@hp760597 22027202 67108864 167544304 45675970560000 11013601 33554432 10471519 2854748160000 (hp760604 (hp760616 rfl rfl) rfl rfl) rfl)

noncomputable def hp760618 := @hp760595 11013601 33554432 10471519 2854748160000 102226994 102229279 33554432 hp760617 rfl rfl rfl

noncomputable def hp760619 := @Enclosure.Real.IsNear.recentre' hp760593 Bool.false 204456273 67108864 2285 67108864 204456273 67108864 2285 67108864 (hp760618 rfl rfl rfl)

noncomputable def hp760620 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760586 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp760621 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760586 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 115441401)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp760622 := nat_lit 272578302277855907794643268205

noncomputable def hp760623 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760586 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp760622

noncomputable def hp760624 := nat_lit 41179909947864627261062053645355129

noncomputable def hp760625 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760586 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp760626 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp760627 := @hp760626 (Enclosure.sfrac Bool.false 1 16) 237880214177967 1125899906842624 1525968831 1125899906842624 1 16 0

noncomputable def hp760628 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)) 546617339262801

noncomputable def hp760629 := @hp760628 1125899906842624 888434623 1125899906842624 23379849 33554432 19 33554432 7981935470780029599744 237880214177967 1125899906842624 1525968831

noncomputable def hp760630 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)) 23379849 33554432 19

noncomputable def hp760631 := @hp760630 33554432 23379849 33554432 19 33554432 546617339262801 1125899906842624 888434623 1125899906842624 (@hp760602 1 23379849 23379849 33554432 19 33554432 (hp760581 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760632 := hp760631 (@hp760602 1 23379849 23379849 33554432 19 33554432 (hp760581 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760633 := @hp760629 1125899906842624 (hp760632 rfl) (@hp760602 1 23379849 23379849 33554432 19 33554432 (hp760581 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760634 := @hp760625 500000000000000 308248958355631 1125899906842624 1525968831 1125899906842624 hp760622 hp682141 hp760624 hp682143 hd4948 (@hp760627 1 4931983333690096 308248958355631 1125899906842624 1525968831 1125899906842624 (hp760633 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp760635 := @hp760621 115441401 67108864 143 16777216 Bool.true 4994889 33554432 1 10890000 (@hp760623 hp682141 hp760624 hp682143 115441401 67108864 143 16777216 (hp760634 rfl) rfl) (Enclosure.sfrac_true_div 115441401 67108864)

noncomputable def hp760636 := nat_lit 1465785994289294314750425717032702372234546420119792784684082751863187816585680137994635790115237813281

noncomputable def hp760637 := nat_lit 5601947891022604907787642274441585691355140175170102587593360775836553490113852396527972106656801

noncomputable def hp760638 := nat_lit 8861667801787726949931310825652083720334812998911198868770993992248057156721706444261396250029723507745

noncomputable def hp760639 := BSN.cos_dyadic_bound_t 115441401 67108864 4 3 33554432 10890000 hp760636 hp745658 hp760637 hp760638 hp745661

noncomputable def hp760640 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 115441401) (BSN.cosEvenQ 67108864) 0 3 hp760636 hp745658 hp760637 rfl rfl rfl

noncomputable def hp760641 := hp760639 hp760637 4994889 rfl rfl rfl rfl rfl rfl rfl rfl (hp760640 rfl)

noncomputable def hp760642 := @BSN.binarySplit_of_base3 (BSN.cosOddP 115441401) (BSN.cosOddQ 67108864) 0 3 hp760638 hp745661 hp760637 rfl rfl rfl

noncomputable def hp760643 := hp760635 (BSN.cos_neg_of_bound 115441401 67108864 Bool.true 4994889 33554432 1 10890000 (hp760641 (hp760642 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp760644 := hp760591 (hp760594 (@Enclosure.Real.IsNear.neg hp760593 Bool.false 204456273 67108864 2285 67108864 (hp760619 rfl))) (@hp760620 4994889 33554432 1574047216 182703882240000 4994889 33554432 98377951 11418992640000 (hp760643 rfl) rfl)

noncomputable def hp760645 := @hp760566 67108864 1021236388988697 2251799813685248 47996619854962441 1532631248189521920000 20038864843794839714217 151115727451828646838272 942492529263744953113067 hp755229 (hp760584 rfl) (@hp760587 Bool.false 1021236388988697 2251799813685248 47996619854962441 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760393 (Enclosure.sfrac Bool.false 11 1)) (hp760588 rfl (hp760396 rfl rfl))) (hp760644 rfl))

noncomputable def hp760646 := @hp760390 hp760388 hp755229 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 859631 1000))) (@hp760395 hp760388 hp755229 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 859631 1000) 11 (hp760396 rfl rfl)) (@hp760399 hp760388 hp755229 hp760565 (hp760645 rfl) rfl rfl))

theorem hd5051 : hp760389 hp755229 := hp760646

noncomputable def hp760647 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 860908 1000)) Bool.true 32991745972947692065011 37778931862957161709568 845217165000330524886353

noncomputable def hp760648 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 860908 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 860908 1000)) Bool.true 32991745972947692065011 37778931862957161709568

noncomputable def hp760649 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 860908 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760650 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp760649 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760651 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 860908 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760652 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp760650 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp760653 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 860908 1000)) hp760652 Bool.true 32991745972947692065011 37778931862957161709568

noncomputable def hp760654 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 860908 1000) 860908 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl

noncomputable def hp760655 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp760650 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp760656 := nat_lit 4428077187242188691809404715008

noncomputable def hp760657 := @hp760655 135264161 134217728 51 65536 5081730594313731534605 37778931862957161709568 11465765985230600406353 hp750331 hp760656 32991745972947692065011 37778931862957161709568

noncomputable def hp760658 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) 11)

noncomputable def hp760659 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) 11) hp760658

noncomputable def hp760660 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) 11)

noncomputable def hp760661 := @hp760660 270528322 536870912 208896 536870912 270528322 536870912 208896 536870912 290477573907939328 135264161 134217728

noncomputable def hp760662 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp760663 := hp760662 BSN.quadSignPos 9 10 11 860908 1000 187 240 536870912 268435456 9007199254740992

noncomputable def hp760664 := hp760663 Bool.false 905719807470 3922 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp760665 := hp760664 Bool.true 592748696 179331 Bool.true 826997906 Bool.true 183339241 28296951008113761 1 Bool.false 536622973

noncomputable def hp760666 := hp760665 Bool.false Bool.false 505869157 Bool.false Bool.true 270528322 208896 BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536622973 536870912) BSN.abs_quadSignPos

noncomputable def hp760667 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp760668 := hp760667 BSN.quadSignNeg 7 8 9 860908 1000 65 130 536870912 268435456 9007199254740992

noncomputable def hp760669 := hp760668 Bool.false 905719807470 3922 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp760670 := hp760669 Bool.true 259267126 146459 Bool.true 575251857 Bool.true 198676821 28296951008113761 1 Bool.false 471327001

noncomputable def hp760671 := hp760670 Bool.true Bool.false 500526925 Bool.true Bool.true 592748696 179331 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 471327001 536870912) BSN.abs_quadSignNeg

noncomputable def hp760672 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp760673 := hp760672 BSN.quadSignPos 5 6 7 860908 1000 91 7 536870912 268435456 9007199254740992

noncomputable def hp760674 := hp760673 Bool.false 905719807470 3922 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp760675 := hp760674 Bool.true 622469221 108836 Bool.false 833272417 Bool.false 423828307 28296951008113761 1 Bool.false 536776990

noncomputable def hp760676 := hp760675 Bool.false Bool.false 381156997 Bool.false Bool.true 259267126 146459 BSN.abs_quadSignPos (BSN.cos_quad_nat3 91 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536776990 536870912) BSN.abs_quadSignPos

noncomputable def hp760677 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp760678 := hp760677 BSN.quadSignPos 3 4 5 860908 1000 314 191 536870912 268435456 9007199254740992

noncomputable def hp760679 := hp760678 Bool.false 905719807470 3922 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp760680 := hp760679 Bool.true 606622833 64327 Bool.false 178603996 Bool.false 770172803 28296951008113761 1 Bool.false 507435279

noncomputable def hp760681 := hp760680 Bool.true Bool.false 531896261 Bool.false Bool.true 622469221 108836 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 314 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 507435279 536870912) BSN.abs_quadSignPos

noncomputable def hp760682 := hp760677 BSN.quadSignPos 1 2 3 860908 1000 694 471 536870912 268435456 9007199254740992

noncomputable def hp760683 := hp760682 Bool.false 905719807470 3922 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp760684 := hp760683 Bool.true 536870792 3978 Bool.false 89134662 Bool.false 743800500 28296951008113761 1 Bool.false 529488546

noncomputable def hp760685 := hp760684 Bool.true Bool.false 527674301 Bool.false Bool.true 606622833 64327 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 694 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 529488546 536870912) BSN.abs_quadSignPos

noncomputable def hp760686 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) 1) Bool.true

noncomputable def hp760687 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)))

noncomputable def hp760688 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000))) Bool.true 67108849 67108864

noncomputable def hp760689 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 113214975933) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 113214975933 67108864

noncomputable def hp760690 := nat_lit 849605354739355503526844106865839107558628186280155749

noncomputable def hp760691 := nat_lit 503608729627790096415982847652133651266574221312000

noncomputable def hp760692 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) Bool.false hp760690 hp760691 10860123431515151807

noncomputable def hp760693 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 860908 4000) (Real.log (Enclosure.sfrac Bool.false 2964651337856 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1721816))))))

noncomputable def hp760694 := nat_lit 226999722408742727753534111088640000

noncomputable def hp760695 := nat_lit 1172555446689459719732363819266049310720

noncomputable def hp760696 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp760693 (Enclosure.sfrac Bool.false 860908 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 860908 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp760694 hp760695)) Bool.false

noncomputable def hp760697 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 860908 1000) 860908 1000 2964651337856 16000000 1721816

noncomputable def hp760698 := hp760697 4000 2000 hp760694 hp760695 (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl rfl rfl rfl

noncomputable def hp760699 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp760693 (Enclosure.sfrac Bool.false 860908 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 860908 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp760694 hp760695) 7597729294576387399117 4503599627370496000

noncomputable def hp760700 := nat_lit 8908757844511744364661640862009541080473961090569005946634240

noncomputable def hp760701 := @hp760699 10860123431515151807 hp753999 hp760694 hp760695 0 1 hp760700 hp760690 hp760691 10860123431515151807 hp753999

noncomputable def hp760702 := @Enclosure.Real.IsNear.subLit_ff_p (hp760693 (Enclosure.sfrac Bool.false 860908 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 860908 2000) (Real.log Real.pi)) 9816894029512686476749 4503599627370496000 113139228526399 45375000000000000000

noncomputable def hp760703 := nat_lit 127468745484635679894664118272000

noncomputable def hp760704 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 860908 4000) (Real.log (Enclosure.sfrac Bool.false 2964651337856 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1721816))))))

noncomputable def hp760705 := @hp760704 (Enclosure.sfrac Bool.false 860908 2000) 11755486503512825961933 4503599627370496000 113139228526399 45375000000000000000 860908 2000 0

noncomputable def hp760706 := nat_lit 19633788059025372953498000

noncomputable def hp760707 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 860908 4000) (Real.log (Enclosure.sfrac Bool.false 2964651337856 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1721816))))) 11757254409075616687933

noncomputable def hp760708 := nat_lit 26471002318389628959741431483291664384

noncomputable def hp760709 := @hp760707 4503599627370496000 2690341484497451 1089000000000000000000 883952781395363 2251799813685248 200000001089 8712000000000000000 hp760708 11755486503512825961933 4503599627370496000 113139228526399

noncomputable def hp760710 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 860908 4000) (Real.log (Enclosure.sfrac Bool.false 2964651337856 16000000)) 860908 4000 0 1 54627228038655079 4503599627370496

noncomputable def hp760711 := nat_lit 117311078948578894064648192

noncomputable def hp760712 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2964651337856) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp760711 hp617687

noncomputable def hp760713 := BSN.log_rat_reduce_isNear 2964651337856 16000000 17 5929302675712 4194304000000 92926771 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp760714 := nat_lit 114782894506207987373658318620579326243171453529712711947715695880758272528063141348024682006013013857647098653460041463743664619520

noncomputable def hp760715 := nat_lit 1144015834802021753253183125602400204380756558739550468710882024321053309473790293185629491550062024209095036698892797034264264704

noncomputable def hp760716 := nat_lit 228098972139327114476520718509394087345627960171749194824789505714026271961388742280908395323192749586053961480260624056320

noncomputable def hp760717 := BSN.log_dyadic_bound 867499337856 5061803337856 6 5 hp760714 268435456 87120000 hp760715 hp760716 92926771 5929302675712

noncomputable def hp760718 := hp760717 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp760719 := @BSN.binarySplit_of_base5 (BSN.artanhP 867499337856) (BSN.artanhQ 5061803337856) 0 5 hp760715 hp760714 hp760716 rfl rfl rfl

noncomputable def hp760720 := hp760713 rfl rfl rfl rfl (hp760718 (hp760719 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp760721 := @hp760710 12500018513 1089000000000000000 11757254409075616687933 4503599627370496000 2690341484497451 1089000000000000000000 (Enclosure.Real.IsNear.const Bool.false 860908 4000) (BSN.isNear_log_sfrac 2964651337856 16000000 54627228038655079 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp760712 1000001481040000 87120000000000000000000 54627228038655079 4503599627370496 12500018513 1089000000000000000 (hp760720 rfl rfl rfl) rfl)) rfl

noncomputable def hp760722 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1721816)))) 1 4

noncomputable def hp760723 := @hp760722 0 1 883952781395363 562949953421312 200000001089 2178000000000000000 883952781395363 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp760724 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1721816))) 884279719003555 562949953421312 1

noncomputable def hp760725 := @hp760724 2000000000000000 19487 33554432 1 10890000 29660533494541572898816 883952781395363 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp760726 := BSN.arctan_dyadic_bound_f 1000 1721816 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp760727 := hp760726 1 19487 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1721816) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1721816) 0 0 rfl)

noncomputable def hp760728 := hp760723 (hp760725 (hp760727 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp760729 := @hp760702 8267032857747 16777216000 645681 134217728000 hp760703 7597729294576387399117 4503599627370496000 10860123431515151807 hp753999 (@hp760705 1 hp760706 9816894029512686476749 4503599627370496000 113139228526399 45375000000000000000 (@hp760709 45375000000000000000 hp760721 hp760728 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 860908 2000) rfl rfl)

noncomputable def hp760730 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 860908 2000) (Real.log Real.pi) 860908 2000 0 1 38410761 33554432

noncomputable def hp760731 := hp760729 (@hp760730 3 268435456 8267032857747 16777216000 645681 134217728000 (Enclosure.Real.IsNear.const Bool.false 860908 2000) hd4909 rfl) rfl

noncomputable def hp760732 := @hp760692 hp753999 113214975933 67108864 491 67108864 (@hp760696 hp760690 hp760691 10860123431515151807 hp753999 (hp760698 rfl rfl rfl rfl rfl) (hp760701 (hp760731 rfl) (Enclosure.Real.IsNear.const Bool.true hp760694 hp760695) rfl rfl)) rfl

noncomputable def hp760733 := nat_lit 15185532740626573548322816

noncomputable def hp760734 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 113214975933) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp760733) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp760735 := BSN.sin_reduce_arg_pos_rat_q1 113214975933 67108864 226375608064910080 72057594037927936 268 hp760733 hp617687 rfl rfl rfl rfl

noncomputable def hp760736 := nat_lit 14356581686757622498174731372527563864364414974411681317367093591724202340154848524016276540069783813749835787800311572573570064817631049263601

noncomputable def hp760737 := nat_lit 10200061336941825637481372738828616784006534912429542835267262484640622769979331859808429550592396411232041731938928838337373446701820401

noncomputable def hp760738 := nat_lit 71693856418532084528139223843331354179605877772768572717748644356381286761533480261377376668079909348447470160043871986946565634288428362738161

noncomputable def hp760739 := BSN.sin_dyadic_bound_f 215799399549 137438953472 4 3 67108864 21801270 hp760736 hp737934 hp760737 hp760738 hp737937

noncomputable def hp760740 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215799399549) (BSN.sinEvenQ 137438953472) 0 3 hp760736 hp737934 hp760737 rfl rfl rfl

noncomputable def hp760741 := hp760739 hp760737 67108849 rfl rfl rfl rfl rfl rfl rfl rfl (hp760740 rfl)

noncomputable def hp760742 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215799399549) (BSN.sinOddQ 137438953472) 0 3 hp760738 hp737937 hp760737 rfl rfl rfl

noncomputable def hp760743 := @BSN.sin_arg_round Bool.false 67108849 67108864 hp760733 hp617687 215799399549 137438953472 21801270 21780000 (hp760741 (hp760742 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760744 := hp760734 67108849 67108864 268 1000000000000000 21780000 10890000 hp760735 BSN.pi_near_15 hp760743 rfl rfl

noncomputable def hp760745 := @hp760689 491 67108864 Bool.true 67108849 67108864 1 10890000 hp760732 (Enclosure.sfrac_false_div 113214975933 67108864) (hp760744 rfl rfl) rfl

noncomputable def hp760746 := @hp760686 67108849 67108864 338381179 45675970560000 536870792 536870912 3978 536870912 (@hp760687 Bool.true 67108849 67108864 338381179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000)) (@hp760688 5414098864 730815528960000 67108849 67108864 338381179 45675970560000 (hp760745 rfl) rfl))

noncomputable def hp760747 := @hp760692 hp753999 905719807470 536870912 3922 536870912 (@hp760696 hp760690 hp760691 10860123431515151807 hp753999 (hp760698 rfl rfl rfl rfl rfl) (hp760701 (hp760731 rfl) (Enclosure.Real.IsNear.const Bool.true hp760694 hp760695) rfl rfl)) rfl

noncomputable def hp760748 := hp760685 (BSN.cos_quad_nat3 471 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 527674301 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl rfl (hp760746 rfl) hp760747

noncomputable def hp760749 := nat_lit 63122833841128661566910604811536

noncomputable def hp760750 := BSN.cos_dyadic_bound_f 89134662 536870912 2 1 536870912 268435456 hp760749 hp708767 hp760749 hp760749 hp708768

noncomputable def hp760751 := @BSN.binarySplit_of_base (BSN.cosEvenP 89134662) (BSN.cosEvenQ 536870912) 0 1 hp760749 hp708767 hp760749 rfl rfl rfl

noncomputable def hp760752 := hp760750 hp760749 529488546 rfl rfl rfl rfl rfl rfl rfl rfl (hp760751 rfl)

noncomputable def hp760753 := @BSN.binarySplit_of_base (BSN.cosOddP 89134662) (BSN.cosOddQ 536870912) 0 1 hp760749 hp708768 hp760749 rfl rfl rfl

noncomputable def hp760754 := nat_lit 109752098589172551394633927410213522960243604695671219495267290894280001524661029871946047434722775040000000000000

noncomputable def hp760755 := nat_lit 28673294253973018705339328283832808533143038705543414990171193610763186328369140625000000000000000000000000

noncomputable def hp760756 := nat_lit 548347582956218147655335856604664332414618367419462344646210923410586595056933162020757497173613875200000000000000

noncomputable def hp760757 := BSN.sin_dyadic_bound_f 743800500 536870912 4 3 536870912 268435456 hp760754 hp642702 hp760755 hp760756 hp642705

noncomputable def hp760758 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 743800500) (BSN.sinEvenQ 536870912) 0 3 hp760754 hp642702 hp760755 rfl rfl rfl

noncomputable def hp760759 := hp760757 hp760755 527674301 rfl rfl rfl rfl rfl rfl rfl rfl (hp760758 rfl)

noncomputable def hp760760 := @BSN.binarySplit_of_base3 (BSN.sinOddP 743800500) (BSN.sinOddQ 536870912) 0 3 hp760756 hp642705 hp760755 rfl rfl rfl

noncomputable def hp760761 := hp760748 hd4911 hd4913 hd4915 hd4917 hd4918 (hp760752 (hp760753 rfl) rfl rfl rfl rfl) (hp760759 (hp760760 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760762 := hp760681 (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 531896261 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl rfl (hp760761 rfl rfl rfl rfl rfl) hp760747

noncomputable def hp760763 := nat_lit 142022329076022379572543195088293822471282362834717110833013757187260416

noncomputable def hp760764 := nat_lit 1035450568430942481625442147454584589455078445338635407903424577536

noncomputable def hp760765 := nat_lit 426064916326930276832666334380586558244668178347260655228225464712626176

noncomputable def hp760766 := BSN.cos_dyadic_bound_f 178603996 536870912 3 2 536870912 268435456 hp760763 hp708868 hp760764 hp760765 hp708870

noncomputable def hp760767 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 178603996) (BSN.cosEvenQ 536870912) 0 2 hp760763 hp708868 hp760764 rfl rfl rfl

noncomputable def hp760768 := hp760766 hp760764 507435279 rfl rfl rfl rfl rfl rfl rfl rfl (hp760767 rfl)

noncomputable def hp760769 := @BSN.binarySplit_of_base2 (BSN.cosOddP 178603996) (BSN.cosOddQ 536870912) 0 2 hp760765 hp708870 hp760764 rfl rfl rfl

noncomputable def hp760770 := nat_lit 126188199391710765183041438071452516454302334652927534721215761895241235281812255640619904195045377873097792313841

noncomputable def hp760771 := nat_lit 43557018112154442811815872869970747680487633296088450667422153247643456429694653910969403410356960815110641

noncomputable def hp760772 := nat_lit 630395330663031651159688966573836182809949712641322347318879007429306262110668995769506840489453682604153993058801

noncomputable def hp760773 := BSN.sin_dyadic_bound_f 770172803 536870912 4 3 536870912 268435456 hp760770 hp642702 hp760771 hp760772 hp642705

noncomputable def hp760774 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 770172803) (BSN.sinEvenQ 536870912) 0 3 hp760770 hp642702 hp760771 rfl rfl rfl

noncomputable def hp760775 := hp760773 hp760771 531896261 rfl rfl rfl rfl rfl rfl rfl rfl (hp760774 rfl)

noncomputable def hp760776 := @BSN.binarySplit_of_base3 (BSN.sinOddP 770172803) (BSN.sinOddQ 536870912) 0 3 hp760772 hp642705 hp760771 rfl rfl rfl

noncomputable def hp760777 := hp760762 hd4920 hd4922 hd4924 hd4926 hd4918 (hp760768 (hp760769 rfl) rfl rfl rfl rfl) (hp760775 (hp760776 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760778 := hp760676 (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 381156997 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl rfl (hp760777 rfl rfl rfl rfl rfl) hp760747

noncomputable def hp760779 := nat_lit 172997172449113767865108568587557624183591072864754330899383204704874257596739311217255196898035456709743739077761

noncomputable def hp760780 := nat_lit 112058311050534388278252252170478832409451974972697438557642083367304157124321887103155466968191888811820161

noncomputable def hp760781 := nat_lit 863961227479982237065451547439939928737089727820926530652247825741015035233981065855963895650781298849638761301121

noncomputable def hp760782 := BSN.sin_dyadic_bound_f 833272417 536870912 4 3 536870912 268435456 hp760779 hp642702 hp760780 hp760781 hp642705

noncomputable def hp760783 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 833272417) (BSN.sinEvenQ 536870912) 0 3 hp760779 hp642702 hp760780 rfl rfl rfl

noncomputable def hp760784 := hp760782 hp760780 536776990 rfl rfl rfl rfl rfl rfl rfl rfl (hp760783 rfl)

noncomputable def hp760785 := @BSN.binarySplit_of_base3 (BSN.sinOddP 833272417) (BSN.sinOddQ 536870912) 0 3 hp760781 hp642705 hp760780 rfl rfl rfl

noncomputable def hp760786 := nat_lit 8107312217765660432990244338890966033951978854630936034601004281783064865

noncomputable def hp760787 := nat_lit 1041165274690727793099201959353320100522004371252261271624775720180001

noncomputable def hp760788 := nat_lit 21231751064655801860452288846304053284949575659813281191419999672551545121

noncomputable def hp760789 := BSN.sin_dyadic_bound_f 423828307 536870912 3 2 536870912 268435456 hp760786 hp708845 hp760787 hp760788 hp708848

noncomputable def hp760790 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 423828307) (BSN.sinEvenQ 536870912) 0 2 hp760786 hp708845 hp760787 rfl rfl rfl

noncomputable def hp760791 := hp760789 hp760787 381156997 rfl rfl rfl rfl rfl rfl rfl rfl (hp760790 rfl)

noncomputable def hp760792 := @BSN.binarySplit_of_base2 (BSN.sinOddP 423828307) (BSN.sinOddQ 536870912) 0 2 hp760788 hp708848 hp760787 rfl rfl rfl

noncomputable def hp760793 := hp760778 hd4928 hd4930 hd4932 hd4934 hd4918 (hp760784 (hp760785 rfl) rfl rfl rfl rfl) (hp760791 (hp760792 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760794 := hp760671 (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 500526925 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl rfl (hp760793 rfl rfl rfl rfl rfl) hp760747

noncomputable def hp760795 := nat_lit 27522169286116927847388524124800953072659870753120589747089952968286734465

noncomputable def hp760796 := nat_lit 11991243843100133295137741591873667324583915738956216832678898218371201

noncomputable def hp760797 := nat_lit 72062457545036458432111149697615653062250335156500377367506491938873608321

noncomputable def hp760798 := BSN.sin_dyadic_bound_f 575251857 536870912 3 2 536870912 268435456 hp760795 hp708845 hp760796 hp760797 hp708848

noncomputable def hp760799 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 575251857) (BSN.sinEvenQ 536870912) 0 2 hp760795 hp708845 hp760796 rfl rfl rfl

noncomputable def hp760800 := hp760798 hp760796 471327001 rfl rfl rfl rfl rfl rfl rfl rfl (hp760799 rfl)

noncomputable def hp760801 := @BSN.binarySplit_of_base2 (BSN.sinOddP 575251857) (BSN.sinOddQ 536870912) 0 2 hp760797 hp708848 hp760796 rfl rfl rfl

noncomputable def hp760802 := nat_lit 217461528424437896269067311554278593591714129527284480296912349785516641

noncomputable def hp760803 := nat_lit 2427602736355445209954049352860796024737752415811874362261592369761

noncomputable def hp760804 := nat_lit 652379730067840977916782026564130059183092913077021817142012526171810401

noncomputable def hp760805 := BSN.cos_dyadic_bound_f 198676821 536870912 3 2 536870912 268435456 hp760802 hp708868 hp760803 hp760804 hp708870

noncomputable def hp760806 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 198676821) (BSN.cosEvenQ 536870912) 0 2 hp760802 hp708868 hp760803 rfl rfl rfl

noncomputable def hp760807 := hp760805 hp760803 500526925 rfl rfl rfl rfl rfl rfl rfl rfl (hp760806 rfl)

noncomputable def hp760808 := @BSN.binarySplit_of_base2 (BSN.cosOddP 198676821) (BSN.cosOddQ 536870912) 0 2 hp760804 hp708870 hp760803 rfl rfl rfl

noncomputable def hp760809 := hp760794 hd4936 hd4938 hd4940 hd4942 hd4918 (hp760800 (hp760801 rfl) rfl rfl rfl rfl) (hp760807 (hp760808 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760810 := hp760666 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 505869157 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl rfl (hp760809 rfl rfl rfl rfl rfl) hp760747

noncomputable def hp760811 := nat_lit 167835501214837568384889387908138446391150387269447495059442213288050324714097385904212204989921868048681991540736

noncomputable def hp760812 := nat_lit 102341768813076756624346472073462532425490246127335368272773069315574196477959011859398213450034561901531136

noncomputable def hp760813 := nat_lit 838213005123364233935007960107817452284738017628628191656835867402987605234979071376561103839310497499765194756096

noncomputable def hp760814 := BSN.sin_dyadic_bound_f 826997906 536870912 4 3 536870912 268435456 hp760811 hp642702 hp760812 hp760813 hp642705

noncomputable def hp760815 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 826997906) (BSN.sinEvenQ 536870912) 0 3 hp760811 hp642702 hp760812 rfl rfl rfl

noncomputable def hp760816 := hp760814 hp760812 536622973 rfl rfl rfl rfl rfl rfl rfl rfl (hp760815 rfl)

noncomputable def hp760817 := @BSN.binarySplit_of_base3 (BSN.sinOddP 826997906) (BSN.sinOddQ 536870912) 0 3 hp760813 hp642705 hp760812 rfl rfl rfl

noncomputable def hp760818 := nat_lit 157693579315184098886649035122004346566941521251943820967512856406120001

noncomputable def hp760819 := nat_lit 1276566468846252087676278543853104664198296336033092547741527430721

noncomputable def hp760820 := nat_lit 473078184812614604155771752808925333491496167163159396717443086163498561

noncomputable def hp760821 := BSN.cos_dyadic_bound_f 183339241 536870912 3 2 536870912 268435456 hp760818 hp708868 hp760819 hp760820 hp708870

noncomputable def hp760822 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 183339241) (BSN.cosEvenQ 536870912) 0 2 hp760818 hp708868 hp760819 rfl rfl rfl

noncomputable def hp760823 := hp760821 hp760819 505869157 rfl rfl rfl rfl rfl rfl rfl rfl (hp760822 rfl)

noncomputable def hp760824 := @BSN.binarySplit_of_base2 (BSN.cosOddP 183339241) (BSN.cosOddQ 536870912) 0 2 hp760820 hp708870 hp760819 rfl rfl rfl

noncomputable def hp760825 := hp760810 hd4944 hd4946 hd4961 hd4963 hd4918 (hp760816 (hp760817 rfl) rfl rfl rfl rfl) (hp760823 (hp760824 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760826 := @hp760661 51 65536 (hp760825 rfl rfl rfl rfl rfl) (hp760825 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp760827 := @hp760659 Bool.true 135264161 134217728 51 65536 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 860908 1000)) (Enclosure.sfrac Bool.false 860908 1000) 11) hp760826

noncomputable def hp760828 := @Enclosure.Real.IsNear.mulLit_tf hp760650 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1))) 19614881 67108864 1

noncomputable def hp760829 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp760649 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760830 := @hp760829 1 1 0 1 19614881 67108864 1 67108864 19614881 67108864 1

noncomputable def hp760831 := @Enclosure.Real.IsNear.of_eq (hp760649 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760832 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 860908 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760833 := @hp760831 (@Inv.inv Real Real.instInv (Real.sqrt hp760651)) Bool.false 19614881 67108864 1 67108864 (hp760832 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 860908 1000) 860908 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000))))

noncomputable def hp760834 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp760651)) Bool.false 19614881 67108864 1 67108864 19614881 67108864

noncomputable def hp760835 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp760651) Bool.false 229601172 67108864 6 67108864 57400293 16777216 3 33554432

noncomputable def hp760836 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 860908 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760837 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 860908 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760838 := @hp760837 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 860908 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2298776525489

noncomputable def hp760839 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 860908 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 860908 1000 0

noncomputable def hp760840 := @hp760839 1 10680707 67108864 1 67108864 2298776525489 16777216000 215227 16777216000 (Enclosure.Real.IsNear.const Bool.false 860908 1000) hd4949

noncomputable def hp760841 := @hp760838 16777216000 215227 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 860908 1000) 860908 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000))) (hp760840 rfl)

noncomputable def hp760842 := @hp760836 2298776525489 16777216000 215227 16777216000 392769992 392770029 33554432 hp760841 rfl rfl rfl

noncomputable def hp760843 := @Enclosure.Real.IsNear.recentre' hp760651 Bool.false 785540021 67108864 37 67108864 785540021 67108864 37 67108864 (hp760842 rfl rfl rfl)

noncomputable def hp760844 := @Enclosure.Real.IsNear.sqrt_image hp760651 785540021 67108864 37 67108864 114800583 114800589 33554432 (hp760843 rfl) rfl rfl

noncomputable def hp760845 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp760651) 57400293 16777216 3 33554432 9807440 9807441 33554432 (hp760835 (hp760844 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp760846 := @hp760830 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp760833 (@hp760834 1 67108864 (hp760845 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp760847 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760848 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp760849 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1))) (hp760847 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760848 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp760850 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 860908 1000) 860908 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl

noncomputable def hp760851 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760852 := @hp760851 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760848 (Enclosure.sfrac Bool.false 1 16)))) 121475603

noncomputable def hp760853 := @hp760852 33554432 49 1048576 2132735 16777216 193352777 22837985280000 259075270164205 562949953421312 28040143248353867 766315624094760960000

noncomputable def hp760854 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760855 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760856 := @hp760854 (@Neg.neg Real Real.instNeg hp760855) Bool.true 121475603 33554432 49 1048576 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760857 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp760858 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp760859 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp760860 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 297461807) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp760861 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1))) Bool.false 41864027629681025647935

noncomputable def hp760862 := nat_lit 998484790541298806291899843

noncomputable def hp760863 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp760864 := @Enclosure.Real.IsNear.subLit_ff_p hp760651 (Enclosure.sfrac Bool.false 11 1) 785540021 67108864 37 67108864 11 1 0

noncomputable def hp760865 := @hp760863 500000000000000 47342517 67108864 37 67108864 41864027629681025647935 9444732965739290427392 hp760862 hp738031 hd4948 (@hp760864 1 47342517 47342517 67108864 37 67108864 (hp760843 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760866 := @hp760860 297461807 67108864 233 67108864 Bool.true 18537054 67108864 1 10890000 (@hp760861 9444732965739290427392 hp760862 hp738031 297461807 67108864 233 67108864 (hp760865 rfl) rfl) (Enclosure.sfrac_false_div 297461807 67108864)

noncomputable def hp760867 := nat_lit 12485144472098233294782464

noncomputable def hp760868 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 297461807) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp760867) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp760869 := BSN.sin_reduce_arg_pos_rat_q2 297461807 67108864 226375608064910080 72057594037927936 0 hp760867 hp617687 rfl rfl rfl rfl

noncomputable def hp760870 := nat_lit 2522185615431751347388186354926770335052231124151327634017772952257876430238494254352627553112077518764979975257677060448026234087437284372161

noncomputable def hp760871 := nat_lit 973117447797514721492151642286702149529877552627509298567011984765993397536381481784135513227186214072760565538985009381309446895922881

noncomputable def hp760872 := nat_lit 15284419015296045055822860469004813395301122983697845981970083741144494618547785155979530493442325887608130840220448931522130518659736742620865

noncomputable def hp760873 := BSN.cos_dyadic_bound_f 177424574191 137438953472 4 3 67108864 21801270 hp760870 hp740177 hp760871 hp760872 hp740180

noncomputable def hp760874 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 177424574191) (BSN.cosEvenQ 137438953472) 0 3 hp760870 hp740177 hp760871 rfl rfl rfl

noncomputable def hp760875 := hp760873 hp760871 18537054 rfl rfl rfl rfl rfl rfl rfl rfl (hp760874 rfl)

noncomputable def hp760876 := @BSN.binarySplit_of_base3 (BSN.cosOddP 177424574191) (BSN.cosOddQ 137438953472) 0 3 hp760872 hp740180 hp760871 rfl rfl rfl

noncomputable def hp760877 := @BSN.cos_arg_round Bool.false 18537054 67108864 hp760867 hp617687 177424574191 137438953472 21801270 21780000 (hp760875 (hp760876 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp760878 := hp760868 18537054 67108864 0 1000000000000000 21780000 10890000 hp760869 BSN.pi_near_15 hp760877 rfl rfl

noncomputable def hp760879 := @hp760858 9268527 33554432 162779929 45675970560000 (@hp760859 18537054 67108864 2604478864 730815528960000 9268527 33554432 162779929 45675970560000 (hp760866 (hp760878 rfl rfl) rfl rfl) rfl)

noncomputable def hp760880 := @hp760857 9268527 33554432 162779929 45675970560000 121474035 121477171 33554432 hp760879 rfl rfl rfl

noncomputable def hp760881 := @Enclosure.Real.IsNear.recentre' hp760855 Bool.false 242951206 67108864 3136 67108864 121475603 33554432 49 1048576 (hp760880 rfl rfl rfl)

noncomputable def hp760882 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760848 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp760883 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760848 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 56984221)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp760884 := nat_lit 1076401510258093727800853425525

noncomputable def hp760885 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760848 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp760884

noncomputable def hp760886 := nat_lit 6461951329759485226408044920298997

noncomputable def hp760887 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp760848 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp760888 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp760889 := @hp760888 (Enclosure.sfrac Bool.false 1 16) 935788618875399 4503599627370496 5986375595 4503599627370496 1 16 0

noncomputable def hp760890 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)) 2241313915895289

noncomputable def hp760891 := @hp760890 4503599627370496 3503347627 4503599627370496 47342517 67108864 37 67108864 62799711156856984436736 935788618875399 4503599627370496 5986375595

noncomputable def hp760892 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)) 47342517 67108864 37

noncomputable def hp760893 := @hp760892 67108864 47342517 67108864 37 67108864 2241313915895289 4503599627370496 3503347627 4503599627370496 (@hp760864 1 47342517 47342517 67108864 37 67108864 (hp760843 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760894 := hp760893 (@hp760864 1 47342517 47342517 67108864 37 67108864 (hp760843 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760895 := @hp760891 4503599627370496 (hp760894 rfl) (@hp760864 1 47342517 47342517 67108864 37 67108864 (hp760843 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp760896 := @hp760887 500000000000000 1217263595586055 4503599627370496 5986375595 4503599627370496 hp760884 hp627574 hp760886 hp747268 hd4948 (@hp760889 1 19476217529376880 1217263595586055 4503599627370496 5986375595 4503599627370496 (hp760895 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp760897 := @hp760883 56984221 33554432 281 33554432 Bool.true 4265470 33554432 1 10890000 (@hp760885 hp627574 hp760886 hp747268 56984221 33554432 281 33554432 (hp760896 rfl) rfl) (Enclosure.sfrac_true_div 56984221 33554432)

noncomputable def hp760898 := nat_lit 339851964589168757552168128997800803443245101899452425551084310237072270902287696926916519139787121

noncomputable def hp760899 := nat_lit 1172344871146787308038137139496342388229887482380410854218613245066112695948524121871274525041

noncomputable def hp760900 := nat_lit 2054990725488284641965916803142946583709955332047164203839249985213833741747649290136128893170794865

noncomputable def hp760901 := BSN.cos_dyadic_bound_t 56984221 33554432 4 3 33554432 10890000 hp760898 hp681868 hp760899 hp760900 hp681871

noncomputable def hp760902 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 56984221) (BSN.cosEvenQ 33554432) 0 3 hp760898 hp681868 hp760899 rfl rfl rfl

noncomputable def hp760903 := hp760901 hp760899 4265470 rfl rfl rfl rfl rfl rfl rfl rfl (hp760902 rfl)

noncomputable def hp760904 := @BSN.binarySplit_of_base3 (BSN.cosOddP 56984221) (BSN.cosOddQ 33554432) 0 3 hp760900 hp681871 hp760899 rfl rfl rfl

noncomputable def hp760905 := hp760897 (BSN.cos_neg_of_bound 56984221 33554432 Bool.true 4265470 33554432 1 10890000 (hp760903 (hp760904 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp760906 := hp760853 (hp760856 (@Enclosure.Real.IsNear.neg hp760855 Bool.false 121475603 33554432 49 1048576 (hp760881 rfl))) (@hp760882 4265470 33554432 3093644432 365407764480000 2132735 16777216 193352777 22837985280000 (hp760905 rfl) rfl)

noncomputable def hp760907 := @hp760828 67108864 259075270164205 562949953421312 28040143248353867 766315624094760960000 5081730594313731534605 37778931862957161709568 11465765985230600406353 hp750331 (hp760846 rfl) (@hp760849 Bool.false 259075270164205 562949953421312 28040143248353867 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760651 (Enclosure.sfrac Bool.false 11 1)) (hp760850 rfl (hp760654 rfl rfl))) (hp760906 rfl))

noncomputable def hp760908 := @hp760648 845217165000330524886353 hp750331 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 860908 1000))) (@hp760653 845217165000330524886353 hp750331 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 860908 1000) 11 (hp760654 rfl rfl)) (@hp760657 845217165000330524886353 hp750331 hp760827 (hp760907 rfl) rfl rfl))

theorem hd5052 : hp760647 hp750331 := hp760908

noncomputable def hp790762 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) Bool.false 556919581 10737418240 1213 10737418240

noncomputable def hp792597 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) 845556 1000 846837 1000

noncomputable def hp792598 := hp792597 (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl rfl rfl

noncomputable def hp792599 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598))

noncomputable def hp792600 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 845556 1000) 845556 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl rfl

noncomputable def hp792601 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598))

noncomputable def hp792602 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598)) 76793180622600504301829

noncomputable def hp792603 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 845556 1000))

noncomputable def hp792604 := @hp792602 37778931862957161709568 hp757535 hp741590 (@hp792603 Bool.true 76793180622600504301829 37778931862957161709568 hp757535 hp741590 (hd4340 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598) hd5040)

noncomputable def hp792605 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598)) 198734100447729969238121

noncomputable def hp792606 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 846837 1000))

noncomputable def hp792607 := @hp792605 75557863725914323419136 hp757794 hp757796 (@hp792606 Bool.false 198734100447729969238121 75557863725914323419136 hp757794 hp757796 (hd4359 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598) hd5041)

noncomputable def hp792608 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598) hp792600 (hp792601 (hp792604 rfl rfl rfl) (hp792607 rfl rfl rfl))

noncomputable def hp792609 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792610 := hp792609 (Enclosure.sfrac Bool.false 845556 1000) 749551 1000 845556 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792611 := hp792610 (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl rfl rfl rfl

noncomputable def hp792612 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792613 := @hp792612 Bool.true Bool.false 76793180622600504301829 37778931862957161709568 hp757535 hp741590 556919581 10737418240 1213 10737418240 (@hp792603 Bool.true 76793180622600504301829 37778931862957161709568 hp757535 hp741590 (hd4340 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598) hd5040)

noncomputable def hp792614 := hp792613 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792615 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792616 := hp792615 (Enclosure.sfrac Bool.false 846837 1000) 749551 1000 846837 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792617 := hp792616 (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl rfl rfl rfl

noncomputable def hp792618 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792619 := @hp792618 Bool.false Bool.false 198734100447729969238121 75557863725914323419136 hp757794 hp757796 556919581 10737418240 1213 10737418240 (@hp792606 Bool.false 198734100447729969238121 75557863725914323419136 hp757794 hp757796 (hd4359 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598) hd5041)

noncomputable def hp792620 := hp792619 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792622 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) 846837 1000 848118 1000

noncomputable def hp792623 := hp792622 (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl rfl rfl

noncomputable def hp792624 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623))

noncomputable def hp792625 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 846837 1000) 846837 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl rfl

noncomputable def hp792626 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623))

noncomputable def hp792627 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623)) 198734100447729969238121

noncomputable def hp792628 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 846837 1000))

noncomputable def hp792629 := @hp792627 75557863725914323419136 hp757794 hp757796 (@hp792628 Bool.false 198734100447729969238121 75557863725914323419136 hp757794 hp757796 (hd4340 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623) hd5041)

noncomputable def hp792630 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623)) 2012623543766027380309

noncomputable def hp792631 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 848118 1000))

noncomputable def hp792632 := @hp792630 9444732965739290427392 1100504667036348179557697 hp758057 (@hp792631 Bool.true 2012623543766027380309 9444732965739290427392 1100504667036348179557697 hp758057 (hd4359 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623) hd5042)

noncomputable def hp792633 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623) hp792625 (hp792626 (hp792629 rfl rfl rfl) (hp792632 rfl rfl rfl))

noncomputable def hp792634 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792635 := hp792634 (Enclosure.sfrac Bool.false 846837 1000) 749551 1000 846837 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792636 := hp792635 (@Eq.refl Real (Enclosure.sfrac Bool.false 846837 1000)) rfl rfl rfl rfl

noncomputable def hp792637 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792638 := @hp792637 Bool.false Bool.false 198734100447729969238121 75557863725914323419136 hp757794 hp757796 556919581 10737418240 1213 10737418240 (@hp792628 Bool.false 198734100447729969238121 75557863725914323419136 hp757794 hp757796 (hd4340 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623) hd5041)

noncomputable def hp792639 := hp792638 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792640 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792641 := hp792640 (Enclosure.sfrac Bool.false 848118 1000) 749551 1000 848118 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792642 := hp792641 (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl rfl rfl rfl

noncomputable def hp792643 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792644 := @hp792643 Bool.true Bool.false 2012623543766027380309 9444732965739290427392 1100504667036348179557697 hp758057 556919581 10737418240 1213 10737418240 (@hp792631 Bool.true 2012623543766027380309 9444732965739290427392 1100504667036348179557697 hp758057 (hd4359 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623) hd5042)

noncomputable def hp792645 := hp792644 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792647 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) 848118 1000 849559 1000

noncomputable def hp792648 := hp792647 (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl rfl rfl

noncomputable def hp792649 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648))

noncomputable def hp792650 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 848118 1000) 848118 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl rfl

noncomputable def hp792651 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648))

noncomputable def hp792652 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648)) 2012623543766027380309

noncomputable def hp792653 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 848118 1000))

noncomputable def hp792654 := @hp792652 9444732965739290427392 1100504667036348179557697 hp758057 (@hp792653 Bool.true 2012623543766027380309 9444732965739290427392 1100504667036348179557697 hp758057 (hd4340 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648) hd5042)

noncomputable def hp792655 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648)) 66827976788258391850993

noncomputable def hp792656 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 849559 1000))

noncomputable def hp792657 := @hp792655 75557863725914323419136 hp758316 hp738860 (@hp792656 Bool.false 66827976788258391850993 75557863725914323419136 hp758316 hp738860 (hd4359 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648) hd5043)

noncomputable def hp792658 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648) hp792650 (hp792651 (hp792654 rfl rfl rfl) (hp792657 rfl rfl rfl))

noncomputable def hp792659 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792660 := hp792659 (Enclosure.sfrac Bool.false 848118 1000) 749551 1000 848118 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792661 := hp792660 (@Eq.refl Real (Enclosure.sfrac Bool.false 848118 1000)) rfl rfl rfl rfl

noncomputable def hp792662 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792663 := @hp792662 Bool.true Bool.false 2012623543766027380309 9444732965739290427392 1100504667036348179557697 hp758057 556919581 10737418240 1213 10737418240 (@hp792653 Bool.true 2012623543766027380309 9444732965739290427392 1100504667036348179557697 hp758057 (hd4340 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648) hd5042)

noncomputable def hp792664 := hp792663 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792665 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792666 := hp792665 (Enclosure.sfrac Bool.false 849559 1000) 749551 1000 849559 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792667 := hp792666 (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl rfl rfl rfl

noncomputable def hp792668 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792669 := @hp792668 Bool.false Bool.false 66827976788258391850993 75557863725914323419136 hp758316 hp738860 556919581 10737418240 1213 10737418240 (@hp792656 Bool.false 66827976788258391850993 75557863725914323419136 hp758316 hp738860 (hd4359 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648) hd5043)

noncomputable def hp792670 := hp792669 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792672 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) 849559 1000 850199 1000

noncomputable def hp792673 := hp792672 (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl rfl rfl

noncomputable def hp792674 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673))

noncomputable def hp792675 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 849559 1000) 849559 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl rfl

noncomputable def hp792676 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673))

noncomputable def hp792677 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673)) 66827976788258391850993

noncomputable def hp792678 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 849559 1000))

noncomputable def hp792679 := @hp792677 75557863725914323419136 hp758316 hp738860 (@hp792678 Bool.false 66827976788258391850993 75557863725914323419136 hp758316 hp738860 (hd4340 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673) hd5043)

noncomputable def hp792680 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673)) 14915937657103259141907

noncomputable def hp792681 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 850199 1000))

noncomputable def hp792682 := @hp792680 18889465931478580854784 60205498711294375500991 hp746784 (@hp792681 Bool.true 14915937657103259141907 18889465931478580854784 60205498711294375500991 hp746784 (hd4359 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673) hd5044)

noncomputable def hp792683 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673) hp792675 (hp792676 (hp792679 rfl rfl rfl) (hp792682 rfl rfl rfl))

noncomputable def hp792684 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792685 := hp792684 (Enclosure.sfrac Bool.false 849559 1000) 749551 1000 849559 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792686 := hp792685 (@Eq.refl Real (Enclosure.sfrac Bool.false 849559 1000)) rfl rfl rfl rfl

noncomputable def hp792687 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792688 := @hp792687 Bool.false Bool.false 66827976788258391850993 75557863725914323419136 hp758316 hp738860 556919581 10737418240 1213 10737418240 (@hp792678 Bool.false 66827976788258391850993 75557863725914323419136 hp758316 hp738860 (hd4340 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673) hd5043)

noncomputable def hp792689 := hp792688 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792690 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792691 := hp792690 (Enclosure.sfrac Bool.false 850199 1000) 749551 1000 850199 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792692 := hp792691 (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl rfl rfl rfl

noncomputable def hp792693 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792694 := @hp792693 Bool.true Bool.false 14915937657103259141907 18889465931478580854784 60205498711294375500991 hp746784 556919581 10737418240 1213 10737418240 (@hp792681 Bool.true 14915937657103259141907 18889465931478580854784 60205498711294375500991 hp746784 (hd4359 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673) hd5044)

noncomputable def hp792695 := hp792694 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792697 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) 850199 1000 851320 1000

noncomputable def hp792698 := hp792697 (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl rfl rfl

noncomputable def hp792699 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698))

noncomputable def hp792700 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 850199 1000) 850199 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl rfl

noncomputable def hp792701 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698))

noncomputable def hp792702 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698)) 14915937657103259141907

noncomputable def hp792703 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 850199 1000))

noncomputable def hp792704 := @hp792702 18889465931478580854784 60205498711294375500991 hp746784 (@hp792703 Bool.true 14915937657103259141907 18889465931478580854784 60205498711294375500991 hp746784 (hd4340 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698) hd5044)

noncomputable def hp792705 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698)) 207964028705560656893247

noncomputable def hp792706 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 851320 1000))

noncomputable def hp792707 := @hp792705 37778931862957161709568 442233252000319433268739 hp751106 (@hp792706 Bool.false 207964028705560656893247 37778931862957161709568 442233252000319433268739 hp751106 (hd4359 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698) hd5045)

noncomputable def hp792708 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698) hp792700 (hp792701 (hp792704 rfl rfl rfl) (hp792707 rfl rfl rfl))

noncomputable def hp792709 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792710 := hp792709 (Enclosure.sfrac Bool.false 850199 1000) 749551 1000 850199 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792711 := hp792710 (@Eq.refl Real (Enclosure.sfrac Bool.false 850199 1000)) rfl rfl rfl rfl

noncomputable def hp792712 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792713 := @hp792712 Bool.true Bool.false 14915937657103259141907 18889465931478580854784 60205498711294375500991 hp746784 556919581 10737418240 1213 10737418240 (@hp792703 Bool.true 14915937657103259141907 18889465931478580854784 60205498711294375500991 hp746784 (hd4340 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698) hd5044)

noncomputable def hp792714 := hp792713 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792715 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792716 := hp792715 (Enclosure.sfrac Bool.false 851320 1000) 749551 1000 851320 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792717 := hp792716 (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl rfl rfl rfl

noncomputable def hp792718 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792719 := @hp792718 Bool.false Bool.false 207964028705560656893247 37778931862957161709568 442233252000319433268739 hp751106 556919581 10737418240 1213 10737418240 (@hp792706 Bool.false 207964028705560656893247 37778931862957161709568 442233252000319433268739 hp751106 (hd4359 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698) hd5045)

noncomputable def hp792720 := hp792719 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792722 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) 851320 1000 853239 1000

noncomputable def hp792723 := hp792722 (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl rfl rfl

noncomputable def hp792724 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723))

noncomputable def hp792725 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 851320 1000) 851320 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl rfl

noncomputable def hp792726 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723))

noncomputable def hp792727 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723)) 207964028705560656893247

noncomputable def hp792728 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 851320 1000))

noncomputable def hp792729 := @hp792727 37778931862957161709568 442233252000319433268739 hp751106 (@hp792728 Bool.false 207964028705560656893247 37778931862957161709568 442233252000319433268739 hp751106 (hd4340 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723) hd5045)

noncomputable def hp792730 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723)) 507836835258337612835

noncomputable def hp792731 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 853239 1000))

noncomputable def hp792732 := @hp792730 1180591620717411303424 hp759080 hp743344 (@hp792731 Bool.true 507836835258337612835 1180591620717411303424 hp759080 hp743344 (hd4359 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723) hd5046)

noncomputable def hp792733 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723) hp792725 (hp792726 (hp792729 rfl rfl rfl) (hp792732 rfl rfl rfl))

noncomputable def hp792734 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792735 := hp792734 (Enclosure.sfrac Bool.false 851320 1000) 749551 1000 851320 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792736 := hp792735 (@Eq.refl Real (Enclosure.sfrac Bool.false 851320 1000)) rfl rfl rfl rfl

noncomputable def hp792737 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792738 := @hp792737 Bool.false Bool.false 207964028705560656893247 37778931862957161709568 442233252000319433268739 hp751106 556919581 10737418240 1213 10737418240 (@hp792728 Bool.false 207964028705560656893247 37778931862957161709568 442233252000319433268739 hp751106 (hd4340 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723) hd5045)

noncomputable def hp792739 := hp792738 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792740 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792741 := hp792740 (Enclosure.sfrac Bool.false 853239 1000) 749551 1000 853239 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792742 := hp792741 (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl rfl rfl rfl

noncomputable def hp792743 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792744 := @hp792743 Bool.true Bool.false 507836835258337612835 1180591620717411303424 hp759080 hp743344 556919581 10737418240 1213 10737418240 (@hp792731 Bool.true 507836835258337612835 1180591620717411303424 hp759080 hp743344 (hd4359 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723) hd5046)

noncomputable def hp792745 := hp792744 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792747 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) 853239 1000 854518 1000

noncomputable def hp792748 := hp792747 (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl rfl rfl

noncomputable def hp792749 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748))

noncomputable def hp792750 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 853239 1000) 853239 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl rfl

noncomputable def hp792751 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748))

noncomputable def hp792752 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748)) 507836835258337612835

noncomputable def hp792753 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 853239 1000))

noncomputable def hp792754 := @hp792752 1180591620717411303424 hp759080 hp743344 (@hp792753 Bool.true 507836835258337612835 1180591620717411303424 hp759080 hp743344 (hd4340 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748) hd5046)

noncomputable def hp792755 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748)) 2886959732546382594731

noncomputable def hp792756 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 854518 1000))

noncomputable def hp792757 := @hp792755 2361183241434822606848 800074579515153408265423 hp759340 (@hp792756 Bool.false 2886959732546382594731 2361183241434822606848 800074579515153408265423 hp759340 (hd4359 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748) hd5047)

noncomputable def hp792758 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748) hp792750 (hp792751 (hp792754 rfl rfl rfl) (hp792757 rfl rfl rfl))

noncomputable def hp792759 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792760 := hp792759 (Enclosure.sfrac Bool.false 853239 1000) 749551 1000 853239 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792761 := hp792760 (@Eq.refl Real (Enclosure.sfrac Bool.false 853239 1000)) rfl rfl rfl rfl

noncomputable def hp792762 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792763 := @hp792762 Bool.true Bool.false 507836835258337612835 1180591620717411303424 hp759080 hp743344 556919581 10737418240 1213 10737418240 (@hp792753 Bool.true 507836835258337612835 1180591620717411303424 hp759080 hp743344 (hd4340 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748) hd5046)

noncomputable def hp792764 := hp792763 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792765 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792766 := hp792765 (Enclosure.sfrac Bool.false 854518 1000) 749551 1000 854518 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792767 := hp792766 (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl rfl rfl rfl

noncomputable def hp792768 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792769 := @hp792768 Bool.false Bool.false 2886959732546382594731 2361183241434822606848 800074579515153408265423 hp759340 556919581 10737418240 1213 10737418240 (@hp792756 Bool.false 2886959732546382594731 2361183241434822606848 800074579515153408265423 hp759340 (hd4359 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748) hd5047)

noncomputable def hp792770 := hp792769 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792772 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) 854518 1000 855797 1000

noncomputable def hp792773 := hp792772 (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl rfl rfl

noncomputable def hp792774 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773))

noncomputable def hp792775 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 854518 1000) 854518 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl rfl

noncomputable def hp792776 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773))

noncomputable def hp792777 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773)) 2886959732546382594731

noncomputable def hp792778 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 854518 1000))

noncomputable def hp792779 := @hp792777 2361183241434822606848 800074579515153408265423 hp759340 (@hp792778 Bool.false 2886959732546382594731 2361183241434822606848 800074579515153408265423 hp759340 (hd4340 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773) hd5047)

noncomputable def hp792780 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773)) 85716660984155317815201

noncomputable def hp792781 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 855797 1000))

noncomputable def hp792782 := @hp792780 75557863725914323419136 101239264006647441378349 hp759604 (@hp792781 Bool.true 85716660984155317815201 75557863725914323419136 101239264006647441378349 hp759604 (hd4359 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773) hd5048)

noncomputable def hp792783 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773) hp792775 (hp792776 (hp792779 rfl rfl rfl) (hp792782 rfl rfl rfl))

noncomputable def hp792784 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792785 := hp792784 (Enclosure.sfrac Bool.false 854518 1000) 749551 1000 854518 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792786 := hp792785 (@Eq.refl Real (Enclosure.sfrac Bool.false 854518 1000)) rfl rfl rfl rfl

noncomputable def hp792787 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792788 := @hp792787 Bool.false Bool.false 2886959732546382594731 2361183241434822606848 800074579515153408265423 hp759340 556919581 10737418240 1213 10737418240 (@hp792778 Bool.false 2886959732546382594731 2361183241434822606848 800074579515153408265423 hp759340 (hd4340 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773) hd5047)

noncomputable def hp792789 := hp792788 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792790 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792791 := hp792790 (Enclosure.sfrac Bool.false 855797 1000) 749551 1000 855797 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792792 := hp792791 (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl rfl rfl rfl

noncomputable def hp792793 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792794 := @hp792793 Bool.true Bool.false 85716660984155317815201 75557863725914323419136 101239264006647441378349 hp759604 556919581 10737418240 1213 10737418240 (@hp792781 Bool.true 85716660984155317815201 75557863725914323419136 101239264006647441378349 hp759604 (hd4359 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773) hd5048)

noncomputable def hp792795 := hp792794 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792797 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) 855797 1000 857075 1000

noncomputable def hp792798 := hp792797 (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl rfl rfl

noncomputable def hp792799 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798))

noncomputable def hp792800 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 855797 1000) 855797 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl rfl

noncomputable def hp792801 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798))

noncomputable def hp792802 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798)) 85716660984155317815201

noncomputable def hp792803 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 855797 1000))

noncomputable def hp792804 := @hp792802 75557863725914323419136 101239264006647441378349 hp759604 (@hp792803 Bool.true 85716660984155317815201 75557863725914323419136 101239264006647441378349 hp759604 (hd4340 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798) hd5048)

noncomputable def hp792805 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798)) 21465898029574878310945

noncomputable def hp792806 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 857075 1000))

noncomputable def hp792807 := @hp792805 37778931862957161709568 89328564439609642892211 hp752921 (@hp792806 Bool.false 21465898029574878310945 37778931862957161709568 89328564439609642892211 hp752921 (hd4359 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798) hd5049)

noncomputable def hp792808 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798) hp792800 (hp792801 (hp792804 rfl rfl rfl) (hp792807 rfl rfl rfl))

noncomputable def hp792809 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792810 := hp792809 (Enclosure.sfrac Bool.false 855797 1000) 749551 1000 855797 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792811 := hp792810 (@Eq.refl Real (Enclosure.sfrac Bool.false 855797 1000)) rfl rfl rfl rfl

noncomputable def hp792812 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792813 := @hp792812 Bool.true Bool.false 85716660984155317815201 75557863725914323419136 101239264006647441378349 hp759604 556919581 10737418240 1213 10737418240 (@hp792803 Bool.true 85716660984155317815201 75557863725914323419136 101239264006647441378349 hp759604 (hd4340 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798) hd5048)

noncomputable def hp792814 := hp792813 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792815 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792816 := hp792815 (Enclosure.sfrac Bool.false 857075 1000) 749551 1000 857075 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792817 := hp792816 (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl rfl rfl rfl

noncomputable def hp792818 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792819 := @hp792818 Bool.false Bool.false 21465898029574878310945 37778931862957161709568 89328564439609642892211 hp752921 556919581 10737418240 1213 10737418240 (@hp792806 Bool.false 21465898029574878310945 37778931862957161709568 89328564439609642892211 hp752921 (hd4359 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798) hd5049)

noncomputable def hp792820 := hp792819 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792822 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) 857075 1000 858353 1000

noncomputable def hp792823 := hp792822 (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl rfl rfl

noncomputable def hp792824 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823))

noncomputable def hp792825 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 857075 1000) 857075 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl rfl

noncomputable def hp792826 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823))

noncomputable def hp792827 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823)) 21465898029574878310945

noncomputable def hp792828 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 857075 1000))

noncomputable def hp792829 := @hp792827 37778931862957161709568 89328564439609642892211 hp752921 (@hp792828 Bool.false 21465898029574878310945 37778931862957161709568 89328564439609642892211 hp752921 (hd4340 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823) hd5049)

noncomputable def hp792830 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823)) 194420638923990726256605

noncomputable def hp792831 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 858353 1000))

noncomputable def hp792832 := @hp792830 75557863725914323419136 537395385163191866287469 hp760127 (@hp792831 Bool.true 194420638923990726256605 75557863725914323419136 537395385163191866287469 hp760127 (hd4359 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823) hd5050)

noncomputable def hp792833 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823) hp792825 (hp792826 (hp792829 rfl rfl rfl) (hp792832 rfl rfl rfl))

noncomputable def hp792834 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792835 := hp792834 (Enclosure.sfrac Bool.false 857075 1000) 749551 1000 857075 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792836 := hp792835 (@Eq.refl Real (Enclosure.sfrac Bool.false 857075 1000)) rfl rfl rfl rfl

noncomputable def hp792837 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792838 := @hp792837 Bool.false Bool.false 21465898029574878310945 37778931862957161709568 89328564439609642892211 hp752921 556919581 10737418240 1213 10737418240 (@hp792828 Bool.false 21465898029574878310945 37778931862957161709568 89328564439609642892211 hp752921 (hd4340 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823) hd5049)

noncomputable def hp792839 := hp792838 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792840 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792841 := hp792840 (Enclosure.sfrac Bool.false 858353 1000) 749551 1000 858353 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792842 := hp792841 (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl rfl rfl rfl

noncomputable def hp792843 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792844 := @hp792843 Bool.true Bool.false 194420638923990726256605 75557863725914323419136 537395385163191866287469 hp760127 556919581 10737418240 1213 10737418240 (@hp792831 Bool.true 194420638923990726256605 75557863725914323419136 537395385163191866287469 hp760127 (hd4359 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823) hd5050)

noncomputable def hp792845 := hp792844 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792847 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) 858353 1000 859631 1000

noncomputable def hp792848 := hp792847 (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl rfl rfl

noncomputable def hp792849 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848))

noncomputable def hp792850 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 858353 1000) 858353 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl rfl

noncomputable def hp792851 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848))

noncomputable def hp792852 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848)) 194420638923990726256605

noncomputable def hp792853 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 858353 1000))

noncomputable def hp792854 := @hp792852 75557863725914323419136 537395385163191866287469 hp760127 (@hp792853 Bool.true 194420638923990726256605 75557863725914323419136 537395385163191866287469 hp760127 (hd4340 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848) hd5050)

noncomputable def hp792855 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848)) 425875622419710952815017

noncomputable def hp792856 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 859631 1000))

noncomputable def hp792857 := @hp792855 151115727451828646838272 hp760388 hp755229 (@hp792856 Bool.false 425875622419710952815017 151115727451828646838272 hp760388 hp755229 (hd4359 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848) hd5051)

noncomputable def hp792858 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848) hp792850 (hp792851 (hp792854 rfl rfl rfl) (hp792857 rfl rfl rfl))

noncomputable def hp792859 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792860 := hp792859 (Enclosure.sfrac Bool.false 858353 1000) 749551 1000 858353 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792861 := hp792860 (@Eq.refl Real (Enclosure.sfrac Bool.false 858353 1000)) rfl rfl rfl rfl

noncomputable def hp792862 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792863 := @hp792862 Bool.true Bool.false 194420638923990726256605 75557863725914323419136 537395385163191866287469 hp760127 556919581 10737418240 1213 10737418240 (@hp792853 Bool.true 194420638923990726256605 75557863725914323419136 537395385163191866287469 hp760127 (hd4340 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848) hd5050)

noncomputable def hp792864 := hp792863 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792865 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792866 := hp792865 (Enclosure.sfrac Bool.false 859631 1000) 749551 1000 859631 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792867 := hp792866 (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl rfl rfl rfl

noncomputable def hp792868 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792869 := @hp792868 Bool.false Bool.false 425875622419710952815017 151115727451828646838272 hp760388 hp755229 556919581 10737418240 1213 10737418240 (@hp792856 Bool.false 425875622419710952815017 151115727451828646838272 hp760388 hp755229 (hd4359 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848) hd5051)

noncomputable def hp792870 := hp792869 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792872 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) 859631 1000 860908 1000

noncomputable def hp792873 := hp792872 (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl rfl rfl

noncomputable def hp792874 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873))

noncomputable def hp792875 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 859631 1000) 859631 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl rfl

noncomputable def hp792876 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873))

noncomputable def hp792877 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873)) 425875622419710952815017

noncomputable def hp792878 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 859631 1000))

noncomputable def hp792879 := @hp792877 151115727451828646838272 hp760388 hp755229 (@hp792878 Bool.false 425875622419710952815017 151115727451828646838272 hp760388 hp755229 (hd4340 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873) hd5051)

noncomputable def hp792880 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873)) 32991745972947692065011

noncomputable def hp792881 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 860908 1000))

noncomputable def hp792882 := @hp792880 37778931862957161709568 845217165000330524886353 hp750331 (@hp792881 Bool.true 32991745972947692065011 37778931862957161709568 845217165000330524886353 hp750331 (hd4359 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873) hd5052)

noncomputable def hp792883 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873) hp792875 (hp792876 (hp792879 rfl rfl rfl) (hp792882 rfl rfl rfl))

noncomputable def hp792884 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792885 := hp792884 (Enclosure.sfrac Bool.false 859631 1000) 749551 1000 859631 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792886 := hp792885 (@Eq.refl Real (Enclosure.sfrac Bool.false 859631 1000)) rfl rfl rfl rfl

noncomputable def hp792887 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792888 := @hp792887 Bool.false Bool.false 425875622419710952815017 151115727451828646838272 hp760388 hp755229 556919581 10737418240 1213 10737418240 (@hp792878 Bool.false 425875622419710952815017 151115727451828646838272 hp760388 hp755229 (hd4340 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873) hd5051)

noncomputable def hp792889 := hp792888 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792890 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792891 := hp792890 (Enclosure.sfrac Bool.false 860908 1000) 749551 1000 860908 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792892 := hp792891 (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl rfl rfl rfl

noncomputable def hp792893 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792894 := @hp792893 Bool.true Bool.false 32991745972947692065011 37778931862957161709568 845217165000330524886353 hp750331 556919581 10737418240 1213 10737418240 (@hp792881 Bool.true 32991745972947692065011 37778931862957161709568 845217165000330524886353 hp750331 (hd4359 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873) hd5052)

noncomputable def hp792895 := hp792894 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl
open Zeta.Certificates
noncomputable def certificatePairs : List (Σ' I : ZIntervalRS, I.Certified) := [(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 845556 1000) (Enclosure.sfrac Bool.false 846837 1000) hp792598) (hp792599 (hp792608 (hp792611 (hp792614 rfl rfl)) (hp792617 (hp792620 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 846837 1000) (Enclosure.sfrac Bool.false 848118 1000) hp792623) (hp792624 (hp792633 (hp792636 (hp792639 rfl rfl)) (hp792642 (hp792645 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 848118 1000) (Enclosure.sfrac Bool.false 849559 1000) hp792648) (hp792649 (hp792658 (hp792661 (hp792664 rfl rfl)) (hp792667 (hp792670 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 849559 1000) (Enclosure.sfrac Bool.false 850199 1000) hp792673) (hp792674 (hp792683 (hp792686 (hp792689 rfl rfl)) (hp792692 (hp792695 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 850199 1000) (Enclosure.sfrac Bool.false 851320 1000) hp792698) (hp792699 (hp792708 (hp792711 (hp792714 rfl rfl)) (hp792717 (hp792720 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 851320 1000) (Enclosure.sfrac Bool.false 853239 1000) hp792723) (hp792724 (hp792733 (hp792736 (hp792739 rfl rfl)) (hp792742 (hp792745 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 853239 1000) (Enclosure.sfrac Bool.false 854518 1000) hp792748) (hp792749 (hp792758 (hp792761 (hp792764 rfl rfl)) (hp792767 (hp792770 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 854518 1000) (Enclosure.sfrac Bool.false 855797 1000) hp792773) (hp792774 (hp792783 (hp792786 (hp792789 rfl rfl)) (hp792792 (hp792795 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 855797 1000) (Enclosure.sfrac Bool.false 857075 1000) hp792798) (hp792799 (hp792808 (hp792811 (hp792814 rfl rfl)) (hp792817 (hp792820 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 857075 1000) (Enclosure.sfrac Bool.false 858353 1000) hp792823) (hp792824 (hp792833 (hp792836 (hp792839 rfl rfl)) (hp792842 (hp792845 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 858353 1000) (Enclosure.sfrac Bool.false 859631 1000) hp792848) (hp792849 (hp792858 (hp792861 (hp792864 rfl rfl)) (hp792867 (hp792870 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 859631 1000) (Enclosure.sfrac Bool.false 860908 1000) hp792873) (hp792874 (hp792883 (hp792886 (hp792889 rfl rfl)) (hp792892 (hp792895 rfl rfl)))))]

theorem solution : Zeta.Certificates.BatchSpec 12 845556 1000 860908 1000 :=
  ⟨CertifiedZeroIntervals.ofCertifiedRS certificatePairs (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.singleton _)))))))))))), rfl, rfl, rfl⟩
#print axioms solution
