-- Prove2me | solution 1 for RHHeight1000.rs_main_0487_0498
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:38:50.496299+00:00
-- url     : https://prove2.me/submissions/ba1a5689-e408-4763-93b9-92ae4a746ce3

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

noncomputable def hp619387 := nat_lit 9903520314283042199192993792

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

noncomputable def hp630709 := nat_lit 2475880078570760549798248448

theorem hd4359 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 a b h))

noncomputable def hp631146 := nat_lit 39614081257132168796771975168

noncomputable def hp633059 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600

noncomputable def hp633062 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600

noncomputable def hp633087 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600

noncomputable def hp633090 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600

noncomputable def hp634261 := nat_lit 618970019642690137449562112

noncomputable def hp642702 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800

noncomputable def hp642705 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000

noncomputable def hp681368 := @BSN.binarySplit_of_base12 (BSN.artanhP 1) (BSN.artanhQ 2) 0 12 13079757671720842725 132638213186519040000 316234143225 rfl rfl rfl

noncomputable def hp681432 := @BSN.binarySplit_of_base6 (BSN.artanhP 3) (BSN.artanhQ 11) 0 6 11010900719820672 424111518688192335 5524329195 rfl rfl rfl

noncomputable def hp681868 := nat_lit 975743491921780970500323514261193594148711042915413329552712293065467609596717903600577236539801600

noncomputable def hp681871 := nat_lit 88792657764882068315529439797768617067532704905302612989296818668957552473301329227652528525121945600

noncomputable def hp682117 := nat_lit 28823037615171174400000000000000

noncomputable def hp682141 := nat_lit 158456325028528675187087900672

noncomputable def hp682143 := nat_lit 4835703278458516698824704000000000000000

noncomputable def hp682805 := nat_lit 144115188075855872000000000000000

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

noncomputable def hp739341 := nat_lit 142851586106806767714304000

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

noncomputable def hp740342 := nat_lit 2142773791602101515714560000

noncomputable def hp740893 := nat_lit 2973696000000000000000000

noncomputable def hp741590 := nat_lit 17142190332816812125716480000

noncomputable def hp741637 := nat_lit 2230272000000000000000000

noncomputable def hp742094 := nat_lit 12856642749612609094287360000

noncomputable def hp744142 := nat_lit 3568435200000000000000000

noncomputable def hp745658 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600

noncomputable def hp745661 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600

noncomputable def hp747268 := nat_lit 773712524553362671811952640000000000000

noncomputable def hp749778 := nat_lit 42817430781178796431748579083484854091482398720

noncomputable def hp749779 := nat_lit 299722015468251575022240053584393978640376791040

noncomputable def hp750331 := nat_lit 1071386895801050757857280000

noncomputable def hp751106 := nat_lit 571406344427227070857216000

noncomputable def hp752398 := nat_lit 6428321374806304547143680000

noncomputable def hp753999 := nat_lit 1486848000000000000000000

noncomputable def hp754729 := nat_lit 2571328549922521818857472000

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

noncomputable def hp760909 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 862185 1000)) Bool.false 25090042554906256788119 4722366482869645213696 5149422059257954218647

noncomputable def hp760910 := nat_lit 6493253913945762168832000

noncomputable def hp760911 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 862185 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 862185 1000)) Bool.false 25090042554906256788119 4722366482869645213696

noncomputable def hp760912 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 862185 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760913 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp760912 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp760914 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 862185 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp760915 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp760913 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp760916 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 862185 1000)) hp760915 Bool.false 25090042554906256788119 4722366482869645213696

noncomputable def hp760917 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 862185 1000) 862185 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl

noncomputable def hp760918 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp760913 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp760919 := nat_lit 105235265848213532471434674176

noncomputable def hp760920 := @hp760918 21711849 4194304 209209 268435456 644673788425137736343 4722366482869645213696 88812040279392170647 hp760910 hp760919 25090042554906256788119 4722366482869645213696

noncomputable def hp760921 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) 11)

noncomputable def hp760922 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) 11) hp760921

noncomputable def hp760923 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) 11)

noncomputable def hp760924 := @hp760923 1389558336 536870912 209209 536870912 1389558336 536870912 209209 536870912 1492026902251044864 21711849 4194304

noncomputable def hp760925 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp760926 := hp760925 BSN.quadSignPos 9 10 11 862185 1000 187 240 536870912 268435456 9007199254740992

noncomputable def hp760927 := hp760926 Bool.false 907406636153 3928 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp760928 := hp760927 Bool.false 1067968109 179600 Bool.true 718785074 Bool.true 140469559 28296951008113761 1 Bool.false 522492910

noncomputable def hp760929 := hp760928 Bool.false Bool.false 518598933 Bool.false Bool.false 1389558336 209209 BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 522492910 536870912) BSN.abs_quadSignPos

noncomputable def hp760930 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp760931 := hp760930 BSN.quadSignNeg 7 8 9 862185 1000 65 130 536870912 268435456 9007199254740992

noncomputable def hp760932 := hp760931 Bool.false 907406636153 3928 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp760933 := hp760932 Bool.false 1351632109 146679 Bool.true 314055344 Bool.true 18230474 28296951008113761 1 Bool.false 296447997

noncomputable def hp760934 := hp760933 Bool.true Bool.false 536561416 Bool.true Bool.false 1067968109 179600 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 296447997 536870912) BSN.abs_quadSignNeg

noncomputable def hp760935 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp760936 := hp760935 BSN.quadSignPos 5 6 7 862185 1000 92 7 536870912 268435456 9007199254740992

noncomputable def hp760937 := hp760936 Bool.false 907406636153 3928 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp760938 := hp760937 Bool.false 1003202952 109000 Bool.false 448384352 Bool.false 776571845 28296951008113761 1 Bool.false 360263758

noncomputable def hp760939 := hp760938 Bool.false Bool.false 532727555 Bool.false Bool.false 1351632109 146679 BSN.abs_quadSignPos (BSN.cos_quad_nat0 92 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 360263758 536870912) BSN.abs_quadSignPos

noncomputable def hp760940 := hp760925 BSN.quadSignPos 3 4 5 862185 1000 315 192 536870912 268435456 9007199254740992

noncomputable def hp760941 := hp760940 Bool.false 907406636153 3928 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp760942 := hp760941 Bool.false 827893917 64425 Bool.false 71696392 Bool.false 510281519 28296951008113761 1 Bool.false 71483473

noncomputable def hp760943 := hp760942 Bool.false Bool.false 312081964 Bool.false Bool.false 1003202952 109000 BSN.abs_quadSignPos (BSN.cos_quad_nat3 315 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 71483473 536870912) BSN.abs_quadSignPos

noncomputable def hp760944 := hp760925 BSN.quadSignPos 1 2 3 862185 1000 695 472 536870912 268435456 9007199254740992

noncomputable def hp760945 := hp760944 Bool.false 907406636153 3928 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp760946 := hp760945 Bool.false 536870888 3986 Bool.false 457437784 Bool.false 834123157 28296951008113761 1 Bool.false 404064090

noncomputable def hp760947 := hp760946 Bool.false Bool.false 9191250 Bool.false Bool.false 827893917 64425 BSN.abs_quadSignPos (BSN.cos_quad_nat3 695 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 404064090 536870912) BSN.abs_quadSignPos

noncomputable def hp760948 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) 1) Bool.false

noncomputable def hp760949 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)))

noncomputable def hp760950 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000))) Bool.false 67108861 67108864

noncomputable def hp760951 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 113425829519) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 113425829519 67108864

noncomputable def hp760952 := nat_lit 32018060684865318463114696546026137887611539266000639

noncomputable def hp760953 := nat_lit 18943618831387277738693263188360455817106020106240

noncomputable def hp760954 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) Bool.false hp760952 hp760953 26102836351946513651

noncomputable def hp760955 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 862185 4000) (Real.log (Enclosure.sfrac Bool.false 2973452896900 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1724370))))))

noncomputable def hp760956 := nat_lit 228688287195376987926602935500000000

noncomputable def hp760957 := nat_lit 1183029851043498196007659533474405000000

noncomputable def hp760958 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp760955 (Enclosure.sfrac Bool.false 862185 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 862185 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp760956 hp760957)) Bool.false

noncomputable def hp760959 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 862185 1000) 862185 1000 2973452896900 16000000 1724370

noncomputable def hp760960 := hp760959 4000 2000 hp760956 hp760957 (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl rfl rfl rfl

noncomputable def hp760961 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp760955 (Enclosure.sfrac Bool.false 862185 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 862185 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp760956 hp760957) 1217900710058448429271 720575940379279360

noncomputable def hp760962 := nat_lit 1440812730818939330840161344571176204942519266970028755000000

noncomputable def hp760963 := @hp760961 26102836351946513651 hp744142 hp760956 hp760957 0 1 hp760962 hp760952 hp760953 26102836351946513651 hp744142

noncomputable def hp760964 := @Enclosure.Real.IsNear.subLit_ff_p (hp760955 (Enclosure.sfrac Bool.false 862185 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 862185 2000) (Real.log Real.pi)) 7867468719152146359347 3602879701896396800 2175465692435081 871200000000000000000

noncomputable def hp760965 := nat_lit 81731933116815847690961158144000

noncomputable def hp760966 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 862185 4000) (Real.log (Enclosure.sfrac Bool.false 2973452896900 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1724370))))))

noncomputable def hp760967 := @hp760966 (Enclosure.sfrac Bool.false 862185 2000) 9420643137041918796851 3602879701896396800 2175465692435081 871200000000000000000 862185 2000 0

noncomputable def hp760968 := nat_lit 15734937438304292718694000

noncomputable def hp760969 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 862185 4000) (Real.log (Enclosure.sfrac Bool.false 2973452896900 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1724370))))) 9422057462270614200051

noncomputable def hp760970 := nat_lit 21213402460786202988281967560567554048

noncomputable def hp760971 := @hp760969 3602879701896396800 718488564108727 290400000000000000000 883953267934627 2251799813685248 200000001089 8712000000000000000 hp760970 9420643137041918796851 3602879701896396800 2175465692435081

noncomputable def hp760972 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 862185 4000) (Real.log (Enclosure.sfrac Bool.false 2973452896900 16000000)) 862185 4000 0 1 54640578659282023 4503599627370496

noncomputable def hp760973 := nat_lit 117339749188065907812859904

noncomputable def hp760974 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2973452896900) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp760973 hp617687

noncomputable def hp760975 := BSN.log_rat_reduce_isNear 2973452896900 16000000 17 5946905793800 4194304000000 93722530 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp760976 := nat_lit 116794450770809427040574977511822934719331201429598539411427182827899008395261385856752712167584193936346837639500000000000000000000

noncomputable def hp760977 := nat_lit 1184045875063091276467937091974492300216397994405679603800040980984987276256062022808221295004097546497346232900000000000000000000

noncomputable def hp760978 := nat_lit 252327375459181469603139298261697456305128578839614569632301301658213821207071586904353392643180330694500000000000000000000

noncomputable def hp760979 := BSN.log_dyadic_bound 876300896900 5070604896900 6 5 hp760976 268435456 87120000 hp760977 hp760978 93722530 5946905793800

noncomputable def hp760980 := hp760979 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp760981 := @BSN.binarySplit_of_base5 (BSN.artanhP 876300896900) (BSN.artanhQ 5070604896900) 0 5 hp760977 hp760976 hp760978 rfl rfl rfl

noncomputable def hp760982 := hp760975 rfl rfl rfl rfl (hp760980 (hp760981 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp760983 := @hp760972 12500018513 1089000000000000000 9422057462270614200051 3602879701896396800 718488564108727 290400000000000000000 (Enclosure.Real.IsNear.const Bool.false 862185 4000) (BSN.isNear_log_sfrac 2973452896900 16000000 54640578659282023 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp760974 1000001481040000 87120000000000000000000 54640578659282023 4503599627370496 12500018513 1089000000000000000 (hp760982 rfl rfl rfl) rfl)) rfl

noncomputable def hp760984 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1724370)))) 1 4

noncomputable def hp760985 := @hp760984 0 1 883953267934627 562949953421312 200000001089 2178000000000000000 883953267934627 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp760986 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1724370))) 884279719003555 562949953421312 1

noncomputable def hp760987 := @hp760986 2000000000000000 19458 33554432 1 10890000 29660549820090222116864 883953267934627 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp760988 := BSN.arctan_dyadic_bound_f 1000 1724370 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp760989 := hp760988 1 19458 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1724370) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1724370) 0 0 rfl)

noncomputable def hp760990 := hp760985 (hp760987 (hp760989 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp760991 := @hp760964 6623436394557 13421772800 517311 107374182400 hp760965 1217900710058448429271 720575940379279360 26102836351946513651 hp744142 (@hp760967 1 hp760968 7867468719152146359347 3602879701896396800 2175465692435081 871200000000000000000 (@hp760971 871200000000000000000 hp760983 hp760990 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 862185 2000) rfl rfl)

noncomputable def hp760992 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 862185 2000) (Real.log Real.pi) 862185 2000 0 1 38410761 33554432

noncomputable def hp760993 := hp760991 (@hp760992 3 268435456 6623436394557 13421772800 517311 107374182400 (Enclosure.Real.IsNear.const Bool.false 862185 2000) hd4909 rfl) rfl

noncomputable def hp760994 := @hp760954 hp744142 113425829519 67108864 123 16777216 (@hp760958 hp760952 hp760953 26102836351946513651 hp744142 (hp760960 rfl rfl rfl rfl rfl) (hp760963 (hp760993 rfl) (Enclosure.Real.IsNear.const Bool.true hp760956 hp760957) rfl rfl)) rfl

noncomputable def hp760995 := nat_lit 15189117154394516716781568

noncomputable def hp760996 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 113425829519) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp760995) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp760997 := BSN.sin_reduce_arg_pos_rat_q3 113425829519 67108864 226375608064910080 72057594037927936 268 hp760995 hp617687 rfl rfl rfl rfl

noncomputable def hp760998 := nat_lit 14370168719599838796984811278977126433468923260055885562942165912610076451825685013239963012054008779995952631243736085179453159687122710387761

noncomputable def hp760999 := nat_lit 10228990510723964143130718861109768053167152410703129968631498314237496741806123900641361894102533001602930884087976892208944989047053361

noncomputable def hp761000 := nat_lit 71761623245473542121704340394234440645652618489063824696158168298310044727456394846848429473321319867640663860700716614582175422870368426089521

noncomputable def hp761001 := BSN.sin_dyadic_bound_f 215850337133 137438953472 4 3 67108864 21801270 hp760998 hp737934 hp760999 hp761000 hp737937

noncomputable def hp761002 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215850337133) (BSN.sinEvenQ 137438953472) 0 3 hp760998 hp737934 hp760999 rfl rfl rfl

noncomputable def hp761003 := hp761001 hp760999 67108861 rfl rfl rfl rfl rfl rfl rfl rfl (hp761002 rfl)

noncomputable def hp761004 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215850337133) (BSN.sinOddQ 137438953472) 0 3 hp761000 hp737937 hp760999 rfl rfl rfl

noncomputable def hp761005 := @BSN.sin_arg_round Bool.false 67108861 67108864 hp760995 hp617687 215850337133 137438953472 21801270 21780000 (hp761003 (hp761004 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761006 := hp760996 67108861 67108864 268 1000000000000000 21780000 10890000 hp760997 BSN.pi_near_15 hp761005 rfl rfl

noncomputable def hp761007 := @hp760951 123 16777216 Bool.false 67108861 67108864 1 10890000 hp760994 (Enclosure.sfrac_false_div 113425829519 67108864) (hp761006 rfl rfl) rfl

noncomputable def hp761008 := @hp760948 67108861 67108864 84765451 11418992640000 536870888 536870912 3986 536870912 (@hp760949 Bool.false 67108861 67108864 84765451 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000)) (@hp760950 1356247216 182703882240000 67108861 67108864 84765451 11418992640000 (hp761007 rfl) rfl))

noncomputable def hp761009 := @hp760954 hp744142 907406636153 536870912 3928 536870912 (@hp760958 hp760952 hp760953 26102836351946513651 hp744142 (hp760960 rfl rfl rfl rfl rfl) (hp760963 (hp760993 rfl) (Enclosure.Real.IsNear.const Bool.true hp760956 hp760957) rfl rfl)) rfl

noncomputable def hp761010 := hp760947 (BSN.cos_quad_nat0 472 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 9191250 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl rfl (hp761008 rfl) hp761009

noncomputable def hp761011 := nat_lit 11001834459535635931786672319405052740096168956734187075321837248525107200

noncomputable def hp761012 := nat_lit 1917150790920611964733085646639448393907248952766159351239891690192896

noncomputable def hp761013 := nat_lit 28811224387979460735307907269299626640947449816951725701178994873876873216

noncomputable def hp761014 := BSN.sin_dyadic_bound_f 457437784 536870912 3 2 536870912 268435456 hp761011 hp708845 hp761012 hp761013 hp708848

noncomputable def hp761015 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 457437784) (BSN.sinEvenQ 536870912) 0 2 hp761011 hp708845 hp761012 rfl rfl rfl

noncomputable def hp761016 := hp761014 hp761012 404064090 rfl rfl rfl rfl rfl rfl rfl rfl (hp761015 rfl)

noncomputable def hp761017 := @BSN.binarySplit_of_base2 (BSN.sinOddP 457437784) (BSN.sinOddQ 536870912) 0 2 hp761013 hp708848 hp761012 rfl rfl rfl

noncomputable def hp761018 := nat_lit 66912903626680336854388406774266633402044228785503549855236730175933317597359511856841170708938825720321464433681

noncomputable def hp761019 := nat_lit 113438934696421633567697270864014551042939499861388727542920242132714835458105737099974079684297712832707601

noncomputable def hp761020 := nat_lit 405002309672882073017130695565462105759543233807198725591232524745777438430636933839272771960736977100798345182225

noncomputable def hp761021 := BSN.cos_dyadic_bound_f 834123157 536870912 4 3 536870912 268435456 hp761018 hp716712 hp761019 hp761020 hp716714

noncomputable def hp761022 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 834123157) (BSN.cosEvenQ 536870912) 0 3 hp761018 hp716712 hp761019 rfl rfl rfl

noncomputable def hp761023 := hp761021 hp761019 9191250 rfl rfl rfl rfl rfl rfl rfl rfl (hp761022 rfl)

noncomputable def hp761024 := @BSN.binarySplit_of_base3 (BSN.cosOddP 834123157) (BSN.cosOddQ 536870912) 0 3 hp761020 hp716714 hp761019 rfl rfl rfl

noncomputable def hp761025 := hp761010 hd4911 hd4913 hd4915 hd4917 hd4918 (hp761016 (hp761017 rfl) rfl rfl rfl rfl) (hp761023 (hp761024 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761026 := hp760943 (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 312081964 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl rfl (hp761025 rfl rfl rfl rfl rfl) hp761009

noncomputable def hp761027 := nat_lit 26423430732255585909764574416896

noncomputable def hp761028 := BSN.sin_dyadic_bound_f 71696392 536870912 2 1 536870912 268435456 hp761027 hp708890 hp761027 hp761027 hp708891

noncomputable def hp761029 := @BSN.binarySplit_of_base (BSN.sinEvenP 71696392) (BSN.sinEvenQ 536870912) 0 1 hp761027 hp708890 hp761027 rfl rfl rfl

noncomputable def hp761030 := hp761028 hp761027 71483473 rfl rfl rfl rfl rfl rfl rfl rfl (hp761029 rfl)

noncomputable def hp761031 := @BSN.binarySplit_of_base (BSN.sinOddP 71696392) (BSN.sinOddQ 536870912) 0 1 hp761027 hp708891 hp761027 rfl rfl rfl

noncomputable def hp761032 := nat_lit 9344047020524572041028261957669320127283537257552204195522978321301429186907306110934286815705756958025226517441

noncomputable def hp761033 := nat_lit 311686560084329194880044459823530372687720400600631500830691162490019802357638442908599293665863671348161

noncomputable def hp761034 := nat_lit 56668867119267495828262421029834698708019899418115558873956914651391501670351237452152950819158420063242017962945

noncomputable def hp761035 := BSN.cos_dyadic_bound_f 510281519 536870912 4 3 536870912 268435456 hp761032 hp716712 hp761033 hp761034 hp716714

noncomputable def hp761036 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 510281519) (BSN.cosEvenQ 536870912) 0 3 hp761032 hp716712 hp761033 rfl rfl rfl

noncomputable def hp761037 := hp761035 hp761033 312081964 rfl rfl rfl rfl rfl rfl rfl rfl (hp761036 rfl)

noncomputable def hp761038 := @BSN.binarySplit_of_base3 (BSN.cosOddP 510281519) (BSN.cosOddQ 536870912) 0 3 hp761034 hp716714 hp761033 rfl rfl rfl

noncomputable def hp761039 := hp761026 hd4920 hd4922 hd4924 hd4926 hd4918 (hp761030 (hp761031 rfl) rfl rfl rfl rfl) (hp761037 (hp761038 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761040 := hp760939 (BSN.cos_quad_nat3 7 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 532727555 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl rfl (hp761039 rfl rfl rfl rfl rfl) hp761009

noncomputable def hp761041 := nat_lit 5643081570519058858684098615269675603336361769009688333187633399344398336

noncomputable def hp761042 := nat_lit 1633817649395992062548181125413333127077172980846448307399682378694656

noncomputable def hp761043 := nat_lit 16925977076258384591927199483558200143754930961067372102948100833275805696

noncomputable def hp761044 := BSN.cos_dyadic_bound_f 448384352 536870912 3 2 536870912 268435456 hp761041 hp708868 hp761042 hp761043 hp708870

noncomputable def hp761045 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 448384352) (BSN.cosEvenQ 536870912) 0 2 hp761041 hp708868 hp761042 rfl rfl rfl

noncomputable def hp761046 := hp761044 hp761042 360263758 rfl rfl rfl rfl rfl rfl rfl rfl (hp761045 rfl)

noncomputable def hp761047 := @BSN.binarySplit_of_base2 (BSN.cosOddP 448384352) (BSN.cosOddQ 536870912) 0 2 hp761043 hp708870 hp761042 rfl rfl rfl

noncomputable def hp761048 := nat_lit 130440676501111130064738017672370465783792025873447749964391372816975438550502324159651579118431914011167902540625

noncomputable def hp761049 := nat_lit 48103833893554436762711897657216549453751296782033758572247480557654820125030847124218859676736562744140625

noncomputable def hp761050 := nat_lit 651620367817805016465171727834568498415837146578217491879587183289679564074211975674102163355917569090004536140625

noncomputable def hp761051 := BSN.sin_dyadic_bound_f 776571845 536870912 4 3 536870912 268435456 hp761048 hp642702 hp761049 hp761050 hp642705

noncomputable def hp761052 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 776571845) (BSN.sinEvenQ 536870912) 0 3 hp761048 hp642702 hp761049 rfl rfl rfl

noncomputable def hp761053 := hp761051 hp761049 532727555 rfl rfl rfl rfl rfl rfl rfl rfl (hp761052 rfl)

noncomputable def hp761054 := @BSN.binarySplit_of_base3 (BSN.sinOddP 776571845) (BSN.sinOddQ 536870912) 0 3 hp761050 hp642705 hp761049 rfl rfl rfl

noncomputable def hp761055 := hp761040 hd4928 hd4930 hd4932 hd4934 hd4918 (hp761046 (hp761047 rfl) rfl rfl rfl rfl) (hp761053 (hp761054 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761056 := hp760934 (BSN.cos_quad_nat2 130 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536561416 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl rfl (hp761055 rfl rfl rfl rfl rfl) hp761009

noncomputable def hp761057 := nat_lit 2444009286249766786689726400224875845405036014421787092437870970887208960

noncomputable def hp761058 := nat_lit 94634502301695448788318571738772334152495253725440288846356536098816

noncomputable def hp761059 := nat_lit 6400823484317091220127435675282335868472180759741505957822006060789006336

noncomputable def hp761060 := BSN.sin_dyadic_bound_f 314055344 536870912 3 2 536870912 268435456 hp761057 hp708845 hp761058 hp761059 hp708848

noncomputable def hp761061 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 314055344) (BSN.sinEvenQ 536870912) 0 2 hp761057 hp708845 hp761058 rfl rfl rfl

noncomputable def hp761062 := hp761060 hp761058 296447997 rfl rfl rfl rfl rfl rfl rfl rfl (hp761061 rfl)

noncomputable def hp761063 := @BSN.binarySplit_of_base2 (BSN.sinOddP 314055344) (BSN.sinOddQ 536870912) 0 2 hp761059 hp708848 hp761058 rfl rfl rfl

noncomputable def hp761064 := nat_lit 110456643651363357612117384976

noncomputable def hp761065 := BSN.cos_dyadic_bound_f 18230474 536870912 2 1 536870912 268435456 hp761064 hp708767 hp761064 hp761064 hp708768

noncomputable def hp761066 := @BSN.binarySplit_of_base (BSN.cosEvenP 18230474) (BSN.cosEvenQ 536870912) 0 1 hp761064 hp708767 hp761064 rfl rfl rfl

noncomputable def hp761067 := hp761065 hp761064 536561416 rfl rfl rfl rfl rfl rfl rfl rfl (hp761066 rfl)

noncomputable def hp761068 := @BSN.binarySplit_of_base (BSN.cosOddP 18230474) (BSN.cosOddQ 536870912) 0 1 hp761064 hp708768 hp761064 rfl rfl rfl

noncomputable def hp761069 := hp761056 hd4936 hd4938 hd4940 hd4942 hd4918 (hp761062 (hp761063 rfl) rfl rfl rfl rfl) (hp761067 (hp761068 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761070 := hp760929 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 518598933 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl rfl (hp761069 rfl rfl rfl rfl rfl) hp761009

noncomputable def hp761071 := nat_lit 95700796104522995111831834073993954566740920914623728007831974295282846653567154996072182616783789843270908645376

noncomputable def hp761072 := nat_lit 19019040435438869582797742484922219408603632641593658061479134032788051386097589603749786111217671230590976

noncomputable def hp761073 := nat_lit 478189943656168080786731034857741180394158622392574214958359354658736331068389259058193377689937729160717486657536

noncomputable def hp761074 := BSN.sin_dyadic_bound_f 718785074 536870912 4 3 536870912 268435456 hp761071 hp642702 hp761072 hp761073 hp642705

noncomputable def hp761075 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 718785074) (BSN.sinEvenQ 536870912) 0 3 hp761071 hp642702 hp761072 rfl rfl rfl

noncomputable def hp761076 := hp761074 hp761072 522492910 rfl rfl rfl rfl rfl rfl rfl rfl (hp761075 rfl)

noncomputable def hp761077 := @BSN.binarySplit_of_base3 (BSN.sinOddP 718785074) (BSN.sinOddQ 536870912) 0 3 hp761073 hp642705 hp761072 rfl rfl rfl

noncomputable def hp761078 := nat_lit 389339866722954011600487155379361

noncomputable def hp761079 := BSN.cos_dyadic_bound_f 140469559 536870912 2 1 536870912 268435456 hp761078 hp708767 hp761078 hp761078 hp708768

noncomputable def hp761080 := @BSN.binarySplit_of_base (BSN.cosEvenP 140469559) (BSN.cosEvenQ 536870912) 0 1 hp761078 hp708767 hp761078 rfl rfl rfl

noncomputable def hp761081 := hp761079 hp761078 518598933 rfl rfl rfl rfl rfl rfl rfl rfl (hp761080 rfl)

noncomputable def hp761082 := @BSN.binarySplit_of_base (BSN.cosOddP 140469559) (BSN.cosOddQ 536870912) 0 1 hp761078 hp708768 hp761078 rfl rfl rfl

noncomputable def hp761083 := hp761070 hd4944 hd4946 hd4961 hd4963 hd4918 (hp761076 (hp761077 rfl) rfl rfl rfl rfl) (hp761081 (hp761082 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761084 := @hp760924 209209 268435456 (hp761083 rfl rfl rfl rfl rfl) (hp761083 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp761085 := @hp760922 Bool.false 21711849 4194304 209209 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 862185 1000)) (Enclosure.sfrac Bool.false 862185 1000) 11) hp761084

noncomputable def hp761086 := @Enclosure.Real.IsNear.mulLit_tf hp760913 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1))) 9803807 33554432 1

noncomputable def hp761087 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp760912 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761088 := @hp761087 1 1 0 1 9803807 33554432 1 33554432 9803807 33554432 1

noncomputable def hp761089 := @Enclosure.Real.IsNear.of_eq (hp760912 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761090 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 862185 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761091 := @hp761089 (@Inv.inv Real Real.instInv (Real.sqrt hp760914)) Bool.false 9803807 33554432 1 33554432 (hp761090 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 862185 1000) 862185 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000))))

noncomputable def hp761092 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp760914)) Bool.false 19607614 67108864 2 67108864 9803807 33554432

noncomputable def hp761093 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp760914) Bool.false 229686268 67108864 6 67108864 57421567 16777216 3 33554432

noncomputable def hp761094 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 862185 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761095 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 862185 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761096 := @hp761095 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 862185 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 1841749072959

noncomputable def hp761097 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 862185 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 862185 1000 0

noncomputable def hp761098 := @hp761097 1 10680707 67108864 1 67108864 1841749072959 13421772800 172437 13421772800 (Enclosure.Real.IsNear.const Bool.false 862185 1000) hd4949

noncomputable def hp761099 := @hp761096 13421772800 172437 13421772800 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 862185 1000) 862185 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000))) (hp761098 rfl)

noncomputable def hp761100 := @hp761094 1841749072959 13421772800 172437 13421772800 393061185 393061223 33554432 hp761099 rfl rfl rfl

noncomputable def hp761101 := @Enclosure.Real.IsNear.recentre' hp760914 Bool.false 786122408 67108864 38 67108864 98265301 8388608 19 33554432 (hp761100 rfl rfl rfl)

noncomputable def hp761102 := @Enclosure.Real.IsNear.sqrt_image hp760914 98265301 8388608 19 33554432 114843131 114843137 33554432 (hp761101 rfl) rfl rfl

noncomputable def hp761103 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp760914) 57421567 16777216 3 33554432 9803806 9803808 33554432 (hp761093 (hp761102 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp761104 := @hp761088 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp761091 (@hp761092 1 33554432 (hp761103 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp761105 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761106 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp761107 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1))) (hp761105 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761106 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp761108 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 862185 1000) 862185 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl

noncomputable def hp761109 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761110 := @hp761109 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761106 (Enclosure.sfrac Bool.false 1 16)))) 75088177

noncomputable def hp761111 := @hp761110 16777216 1233 16777216 875737 8388608 99739201 11418992640000 65757494861449 140737488355328 40723697032603 870813209198592000

noncomputable def hp761112 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761113 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761114 := @hp761112 (@Neg.neg Real Real.instNeg hp761113) Bool.true 75088177 16777216 1233 16777216 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761115 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761116 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp761117 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp761118 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 75280263) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false

noncomputable def hp761119 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1))) Bool.false 5297377580299043629215

noncomputable def hp761120 := nat_lit 512735432977672758992149957

noncomputable def hp761121 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp761122 := @Enclosure.Real.IsNear.subLit_ff_p hp760914 (Enclosure.sfrac Bool.false 11 1) 98265301 8388608 19 33554432 11 1 0

noncomputable def hp761123 := @hp761121 500000000000000 5990613 8388608 19 33554432 5297377580299043629215 1180591620717411303424 hp761120 hp682805 hd4948 (@hp761122 1 5990613 5990613 8388608 19 33554432 (hp761101 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761124 := @hp761118 75280263 16777216 15 4194304 Bool.true 14994370 67108864 1 10890000 (@hp761119 1180591620717411303424 hp761120 hp682805 75280263 16777216 15 4194304 (hp761123 rfl) rfl) (Enclosure.sfrac_false_div 75280263 16777216)

noncomputable def hp761125 := nat_lit 3253124313372217128779776

noncomputable def hp761126 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 75280263) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp761125) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp761127 := BSN.sin_reduce_arg_pos_rat_q2 75280263 16777216 226375608064910080 72057594037927936 0 hp761125 hp619230 rfl rfl rfl rfl

noncomputable def hp761128 := nat_lit 2976969572689086883547545568629369773932253003855312703290527732555250708865784073700274325266817509842273006084158092698534043146630520934081

noncomputable def hp761129 := nat_lit 1598711885544839479309715108861730216424472904972372310449993019980988020667719615093509740150518181921901071849213427100287593742110401

noncomputable def hp761130 := nat_lit 18036833765392952138032514118296909946392407500953497255422131319982011198449421349621813307387240722676110897457905603016194666648625509863105

noncomputable def hp761131 := BSN.cos_dyadic_bound_f 184918707951 137438953472 4 3 67108864 21801270 hp761128 hp740177 hp761129 hp761130 hp740180

noncomputable def hp761132 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 184918707951) (BSN.cosEvenQ 137438953472) 0 3 hp761128 hp740177 hp761129 rfl rfl rfl

noncomputable def hp761133 := hp761131 hp761129 14994370 rfl rfl rfl rfl rfl rfl rfl rfl (hp761132 rfl)

noncomputable def hp761134 := @BSN.binarySplit_of_base3 (BSN.cosOddP 184918707951) (BSN.cosOddQ 137438953472) 0 3 hp761130 hp740180 hp761129 rfl rfl rfl

noncomputable def hp761135 := @BSN.cos_arg_round Bool.false 14994370 67108864 hp761125 hp619230 184918707951 137438953472 21801270 21780000 (hp761133 (hp761134 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761136 := hp761126 14994370 67108864 0 1000000000000000 21780000 10890000 hp761127 BSN.pi_near_15 hp761135 rfl rfl

noncomputable def hp761137 := @hp761116 7497185 33554432 10471519 2854748160000 (@hp761117 14994370 67108864 167544304 45675970560000 7497185 33554432 10471519 2854748160000 (hp761124 (hp761136 rfl rfl) rfl rfl) rfl)

noncomputable def hp761138 := @hp761115 7497185 33554432 10471519 2854748160000 150173888 150178820 33554432 hp761137 rfl rfl rfl

noncomputable def hp761139 := @Enclosure.Real.IsNear.recentre' hp761113 Bool.false 300352708 67108864 4932 67108864 75088177 16777216 1233 16777216 (hp761138 rfl rfl rfl)

noncomputable def hp761140 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761106 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp761141 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761106 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 112433041)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp761142 := nat_lit 16592188283672815682762398645

noncomputable def hp761143 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761106 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp761142

noncomputable def hp761144 := nat_lit 41777352350473966516507604294638823

noncomputable def hp761145 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761106 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp761146 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp761147 := @hp761146 (Enclosure.sfrac Bool.false 1 16) 14365460020935 70368744177664 1548107745 1125899906842624 1 16 0

noncomputable def hp761148 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)) 35887444115769

noncomputable def hp761149 := @hp761148 70368744177664 910573537 1125899906842624 5990613 8388608 19 33554432 120506212855295508480 14365460020935 70368744177664 1548107745

noncomputable def hp761150 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)) 5990613 8388608 19

noncomputable def hp761151 := @hp761150 33554432 5990613 8388608 19 33554432 35887444115769 70368744177664 910573537 1125899906842624 (@hp761122 1 5990613 5990613 8388608 19 33554432 (hp761101 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761152 := hp761151 (@hp761122 1 5990613 5990613 8388608 19 33554432 (hp761101 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761153 := @hp761149 1125899906842624 (hp761152 rfl) (@hp761122 1 5990613 5990613 8388608 19 33554432 (hp761101 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761154 := @hp761145 500000000000000 18763506532039 70368744177664 1548107745 1125899906842624 hp761142 hp619387 hp761144 hp682143 hd4948 (@hp761147 1 300216104512624 18763506532039 70368744177664 1548107745 1125899906842624 (hp761153 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp761155 := @hp761141 112433041 67108864 145 16777216 Bool.true 3502948 33554432 1 10890000 (@hp761143 hp619387 hp761144 hp682143 112433041 67108864 145 16777216 (hp761154 rfl) rfl) (Enclosure.sfrac_true_div 112433041 67108864)

noncomputable def hp761156 := nat_lit 1318177677863538400183597503304141665701290746816179869206988366877218503703931231528741184421546196161

noncomputable def hp761157 := nat_lit 4080632529682237943379407109273137144735988387082389526952674384821399506207688564207375843622081

noncomputable def hp761158 := nat_lit 7972038395175772285994364722674519929999254160910870555882561210895242535160745756622171617323901811905

noncomputable def hp761159 := BSN.cos_dyadic_bound_t 112433041 67108864 4 3 33554432 10890000 hp761156 hp745658 hp761157 hp761158 hp745661

noncomputable def hp761160 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 112433041) (BSN.cosEvenQ 67108864) 0 3 hp761156 hp745658 hp761157 rfl rfl rfl

noncomputable def hp761161 := hp761159 hp761157 3502948 rfl rfl rfl rfl rfl rfl rfl rfl (hp761160 rfl)

noncomputable def hp761162 := @BSN.binarySplit_of_base3 (BSN.cosOddP 112433041) (BSN.cosOddQ 67108864) 0 3 hp761158 hp745661 hp761157 rfl rfl rfl

noncomputable def hp761163 := hp761155 (BSN.cos_neg_of_bound 112433041 67108864 Bool.true 3502948 33554432 1 10890000 (hp761161 (hp761162 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp761164 := hp761111 (hp761114 (@Enclosure.Real.IsNear.neg hp761113 Bool.false 75088177 16777216 1233 16777216 (hp761139 rfl))) (@hp761140 3502948 33554432 1595827216 182703882240000 875737 8388608 99739201 11418992640000 (hp761163 rfl) rfl)

noncomputable def hp761165 := @hp761086 33554432 65757494861449 140737488355328 40723697032603 870813209198592000 644673788425137736343 4722366482869645213696 88812040279392170647 hp760910 (hp761104 rfl) (@hp761107 Bool.false 65757494861449 140737488355328 40723697032603 870813209198592000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp760914 (Enclosure.sfrac Bool.false 11 1)) (hp761108 rfl (hp760917 rfl rfl))) (hp761164 rfl))

noncomputable def hp761166 := @hp760911 5149422059257954218647 hp760910 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 862185 1000))) (@hp760916 5149422059257954218647 hp760910 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 862185 1000) 11 (hp760917 rfl rfl)) (@hp760920 5149422059257954218647 hp760910 hp761085 (hp761165 rfl) rfl rfl))

theorem hd5053 : hp760909 hp760910 := hp761166

noncomputable def hp761167 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 863462 1000)) Bool.true 6362793886179603060855 4722366482869645213696 114088751760915325805619

noncomputable def hp761168 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 863462 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 863462 1000)) Bool.true 6362793886179603060855 4722366482869645213696

noncomputable def hp761169 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 863462 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761170 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp761169 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761171 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 863462 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761172 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp761170 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp761173 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 863462 1000)) hp761172 Bool.true 6362793886179603060855 4722366482869645213696

noncomputable def hp761174 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 863462 1000) 863462 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl

noncomputable def hp761175 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp761170 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp761176 := nat_lit 1707999478270633845539607674880

noncomputable def hp761177 := @hp761175 398892285 268435456 209521 268435456 654593403222606669705 4722366482869645213696 2589296291499762541619 hp739341 hp761176 6362793886179603060855 4722366482869645213696

noncomputable def hp761178 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) 11)

noncomputable def hp761179 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) 11) hp761178

noncomputable def hp761180 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) 11)

noncomputable def hp761181 := @hp761180 398892285 536870912 209521 536870912 398892285 536870912 209521 536870912 428307329675427840 398892285 268435456

noncomputable def hp761182 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp761183 := hp761182 BSN.quadSignPos 9 10 11 863462 1000 187 240 536870912 268435456 9007199254740992

noncomputable def hp761184 := hp761183 Bool.false 909093972875 3934 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp761185 := hp761184 Bool.true 712125942 179868 Bool.true 610064203 Bool.true 97091838 28296951008113761 1 Bool.false 486993523

noncomputable def hp761186 := hp761185 Bool.false Bool.false 528115399 Bool.false Bool.true 398892285 209521 BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 486993523 536870912) BSN.abs_quadSignPos

noncomputable def hp761187 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp761188 := hp761187 BSN.quadSignNeg 7 8 9 863462 1000 65 129 536870912 268435456 9007199254740992

noncomputable def hp761189 := hp761188 Bool.false 909093972875 3934 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp761190 := hp761189 Bool.true 522846938 146898 Bool.true 52350792 Bool.true 680590944 28296951008113761 1 Bool.false 52267869

noncomputable def hp761191 := hp761190 Bool.true Bool.false 512398570 Bool.true Bool.true 712125942 179868 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 65 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 52267869 536870912) BSN.abs_quadSignNeg

noncomputable def hp761192 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp761193 := hp761192 BSN.quadSignPos 5 6 7 863462 1000 93 8 536870912 268435456 9007199254740992

noncomputable def hp761194 := hp761193 Bool.false 909093972875 3934 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp761195 := hp761194 Bool.true 671481323 109163 Bool.false 64004326 Bool.false 286508565 28296951008113761 1 Bool.false 63852820

noncomputable def hp761196 := hp761195 Bool.true Bool.false 462218537 Bool.false Bool.true 522846938 146898 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 63852820 536870912) BSN.abs_quadSignPos

noncomputable def hp761197 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp761198 := hp761197 BSN.quadSignNeg 3 4 5 863462 1000 315 193 536870912 268435456 9007199254740992

noncomputable def hp761199 := hp761198 Bool.false 909093972875 3934 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp761200 := hp761199 Bool.true 831190969 64522 Bool.false 808611685 Bool.false 250898274 28296951008113761 1 Bool.false 535749701

noncomputable def hp761201 := hp761200 Bool.false Bool.false 241864727 Bool.true Bool.true 671481323 109163 BSN.abs_quadSignPos (BSN.cos_quad_nat3 315 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535749701 536870912) BSN.abs_quadSignNeg

noncomputable def hp761202 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp761203 := hp761202 BSN.quadSignNeg 1 2 3 863462 1000 696 474 536870912 268435456 9007199254740992

noncomputable def hp761204 := hp761203 Bool.false 909093972875 3934 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp761205 := hp761204 Bool.true 536870616 3994 Bool.false 826248944 Bool.false 81638995 28296951008113761 1 Bool.false 17063038

noncomputable def hp761206 := hp761205 Bool.false Bool.false 530675668 Bool.true Bool.true 831190969 64522 BSN.abs_quadSignPos (BSN.cos_quad_nat0 696 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 17063038 536870912) BSN.abs_quadSignNeg

noncomputable def hp761207 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) 1) Bool.true

noncomputable def hp761208 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)))

noncomputable def hp761209 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000))) Bool.true 67108827 67108864

noncomputable def hp761210 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 113636746609) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 113636746609 67108864

noncomputable def hp761211 := nat_lit 888896147170769817925887785544807348013399299455188091473

noncomputable def hp761212 := nat_lit 524942964581718413282621688760506821476534418669568000

noncomputable def hp761213 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) Bool.false hp761211 hp761212 65353441170641657413

noncomputable def hp761214 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 863462 4000) (Real.log (Enclosure.sfrac Bool.false 2982267501776 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1726924))))))

noncomputable def hp761215 := nat_lit 230386885540890562313499125519360000

noncomputable def hp761216 := nat_lit 1193582112550117047436792037752881745920

noncomputable def hp761217 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp761214 (Enclosure.sfrac Bool.false 863462 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 863462 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp761215 hp761216)) Bool.false

noncomputable def hp761218 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 863462 1000) 863462 1000 2982267501776 16000000 1726924

noncomputable def hp761219 := hp761218 4000 2000 hp761215 hp761216 (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl rfl rfl rfl

noncomputable def hp761220 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp761214 (Enclosure.sfrac Bool.false 863462 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 863462 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp761215 hp761216) 15252067685819613870437 9007199254740992000

noncomputable def hp761221 := nat_lit 18204593094057365871122181847957654487314417652842252113367040

noncomputable def hp761222 := @hp761220 65353441170641657413 hp739631 hp761215 hp761216 0 1 hp761221 hp761211 hp761212 65353441170641657413 hp739631

noncomputable def hp761223 := @Enclosure.Real.IsNear.subLit_ff_p (hp761214 (Enclosure.sfrac Bool.false 863462 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 863462 2000) (Real.log Real.pi)) 19703564060246536780133 9007199254740992000 5446645492908253 2178000000000000000000

noncomputable def hp761224 := nat_lit 511774468023231597881835126784000

noncomputable def hp761225 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 863462 4000) (Real.log (Enclosure.sfrac Bool.false 2982267501776 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1726924))))))

noncomputable def hp761226 := @hp761225 (Enclosure.sfrac Bool.false 863462 2000) 4718450240339023999457 1801439850948198400 5446645492908253 2178000000000000000000 863462 2000 0

noncomputable def hp761227 := nat_lit 7881425624098614712053200

noncomputable def hp761228 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 863462 4000) (Real.log (Enclosure.sfrac Bool.false 2982267501776 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1726924))))) 4719157403329181339457

noncomputable def hp761229 := nat_lit 10625005372078527888871620219120910336

noncomputable def hp761230 := @hp761228 1801439850948198400 5396645492636003 2178000000000000000000 883953737696675 2251799813685248 200000001089 8712000000000000000 hp761229 4718450240339023999457 1801439850948198400 5446645492908253

noncomputable def hp761231 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 863462 4000) (Real.log (Enclosure.sfrac Bool.false 2982267501776 16000000)) 863462 4000 0 1 54653909533125735 4503599627370496

noncomputable def hp761232 := nat_lit 117368377021658830240481280

noncomputable def hp761233 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2982267501776) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp761232 hp617687

noncomputable def hp761234 := BSN.log_rat_reduce_isNear 2982267501776 16000000 17 5964535003552 4194304000000 94517112 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp761235 := nat_lit 118840730906419255522688146158265056666106006116725157939641175594760299217266923437020779865328936471903039167397870318135038443520

noncomputable def hp761236 := nat_lit 1225263640128149420918349568763680517616345249075101325147254102360724469394655449998433492061985233516701612725392757901443989504

noncomputable def hp761237 := nat_lit 278888931452383643000337848584194151045567966612610813669605045170700672770356554744057918903302908867133181415177658040320

noncomputable def hp761238 := BSN.log_dyadic_bound 885115501776 5079419501776 6 5 hp761235 268435456 87120000 hp761236 hp761237 94517112 5964535003552

noncomputable def hp761239 := hp761238 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp761240 := @BSN.binarySplit_of_base5 (BSN.artanhP 885115501776) (BSN.artanhQ 5079419501776) 0 5 hp761236 hp761235 hp761237 rfl rfl rfl

noncomputable def hp761241 := hp761234 rfl rfl rfl rfl (hp761239 (hp761240 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp761242 := @hp761231 12500018513 1089000000000000000 4719157403329181339457 1801439850948198400 5396645492636003 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 863462 4000) (BSN.isNear_log_sfrac 2982267501776 16000000 54653909533125735 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp761233 1000001481040000 87120000000000000000000 54653909533125735 4503599627370496 12500018513 1089000000000000000 (hp761241 rfl rfl rfl) rfl)) rfl

noncomputable def hp761243 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1726924)))) 1 4

noncomputable def hp761244 := @hp761243 0 1 883953737696675 562949953421312 200000001089 2178000000000000000 883953737696675 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp761245 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1726924))) 884279719003555 562949953421312 1

noncomputable def hp761246 := @hp761245 2000000000000000 19430 33554432 1 10890000 29660565582688917913600 883953737696675 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp761247 := BSN.arctan_dyadic_bound_f 1000 1726924 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp761248 := hp761247 1 19430 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1726924) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1726924) 0 0 rfl)

noncomputable def hp761249 := hp761244 (hp761246 (hp761248 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp761250 := @hp761223 16583116257291 33554432000 1295193 268435456000 hp761224 15252067685819613870437 9007199254740992000 65353441170641657413 hp739631 (@hp761226 1 hp761227 19703564060246536780133 9007199254740992000 5446645492908253 2178000000000000000000 (@hp761230 2178000000000000000000 hp761242 hp761249 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 863462 2000) rfl rfl)

noncomputable def hp761251 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 863462 2000) (Real.log Real.pi) 863462 2000 0 1 38410761 33554432

noncomputable def hp761252 := hp761250 (@hp761251 3 268435456 16583116257291 33554432000 1295193 268435456000 (Enclosure.Real.IsNear.const Bool.false 863462 2000) hd4909 rfl) rfl

noncomputable def hp761253 := @hp761213 hp739631 113636746609 67108864 493 67108864 (@hp761217 hp761211 hp761212 65353441170641657413 hp739631 (hp761219 rfl rfl rfl rfl rfl) (hp761222 (hp761252 rfl) (Enclosure.Real.IsNear.const Bool.true hp761215 hp761216) rfl rfl)) rfl

noncomputable def hp761254 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 113636746609) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 10043564520675305586688) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp761255 := BSN.sin_reduce_arg_pos_rat_q2 113636746609 67108864 226375608064910080 72057594037927936 269 10043564520675305586688 hp617687 rfl rfl rfl rfl

noncomputable def hp761256 := BSN.cos_dyadic_bound_f 142727636 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp761257 := hp761256 1 67108827 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 142727636) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp761258 := hp761257 (@BSN.binarySplit_of_le (BSN.cosOddP 142727636) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp761259 := @BSN.cos_arg_round Bool.false 67108827 67108864 10043564520675305586688 hp617687 142727636 137438953472 21801270 21780000 hp761258 rfl

noncomputable def hp761260 := hp761254 67108827 67108864 269 1000000000000000 21780000 10890000 hp761255 BSN.pi_near_15 hp761259 rfl rfl

noncomputable def hp761261 := @hp761210 493 67108864 Bool.true 67108827 67108864 1 10890000 hp761253 (Enclosure.sfrac_false_div 113636746609 67108864) (hp761260 rfl rfl) rfl

noncomputable def hp761262 := @hp761207 67108827 67108864 339742429 45675970560000 536870616 536870912 3994 536870912 (@hp761208 Bool.true 67108827 67108864 339742429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000)) (@hp761209 5435878864 730815528960000 67108827 67108864 339742429 45675970560000 (hp761261 rfl) rfl))

noncomputable def hp761263 := @hp761213 hp739631 909093972875 536870912 3934 536870912 (@hp761217 hp761211 hp761212 65353441170641657413 hp739631 (hp761219 rfl rfl rfl rfl rfl) (hp761222 (hp761252 rfl) (Enclosure.Real.IsNear.const Bool.true hp761215 hp761216) rfl rfl)) rfl

noncomputable def hp761264 := hp761206 (BSN.cos_quad_nat2 474 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530675668 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl rfl (hp761262 rfl) hp761263

noncomputable def hp761265 := nat_lit 64413498908237122571023804303568309863154708305067352130578220927134499791265241851258219331508635720931623305216

noncomputable def hp761266 := nat_lit 101235075070992281132000174993734546768113583790063138054015978754391326882776107839757956168986527516327936

noncomputable def hp761267 := nat_lit 389907667760918404011090627866160207581076577115672473048188880676570557990965621685774498456083921825619372933120

noncomputable def hp761268 := BSN.cos_dyadic_bound_f 826248944 536870912 4 3 536870912 268435456 hp761265 hp716712 hp761266 hp761267 hp716714

noncomputable def hp761269 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 826248944) (BSN.cosEvenQ 536870912) 0 3 hp761265 hp716712 hp761266 rfl rfl rfl

noncomputable def hp761270 := hp761268 hp761266 17063038 rfl rfl rfl rfl rfl rfl rfl rfl (hp761269 rfl)

noncomputable def hp761271 := @BSN.binarySplit_of_base3 (BSN.cosOddP 826248944) (BSN.cosOddQ 536870912) 0 3 hp761267 hp716714 hp761266 rfl rfl rfl

noncomputable def hp761272 := nat_lit 44421231982001196377527330500625

noncomputable def hp761273 := BSN.cos_dyadic_bound_f 81638995 536870912 2 1 536870912 268435456 hp761272 hp708767 hp761272 hp761272 hp708768

noncomputable def hp761274 := @BSN.binarySplit_of_base (BSN.cosEvenP 81638995) (BSN.cosEvenQ 536870912) 0 1 hp761272 hp708767 hp761272 rfl rfl rfl

noncomputable def hp761275 := hp761273 hp761272 530675668 rfl rfl rfl rfl rfl rfl rfl rfl (hp761274 rfl)

noncomputable def hp761276 := @BSN.binarySplit_of_base (BSN.cosOddP 81638995) (BSN.cosOddQ 536870912) 0 1 hp761272 hp708768 hp761272 rfl rfl rfl

noncomputable def hp761277 := hp761264 hd4911 hd4913 hd4915 hd4917 hd4918 (hp761270 (hp761271 rfl) rfl rfl rfl rfl) (hp761275 (hp761276 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761278 := hp761201 (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 241864727 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl rfl (hp761277 rfl rfl rfl rfl rfl) hp761263

noncomputable def hp761279 := nat_lit 153375776641455249691627882554430485040697311824482553787200156156978235200594906764260095223841120566501188540625

noncomputable def hp761280 := nat_lit 78141214119855593411410990698390468672445505339490986033606094485807291449241691706162410087796406494140625

noncomputable def hp761281 := nat_lit 766073186423438896190183839713848254832888404648020392045167440775077899918862732100513728609875581302175966140625

noncomputable def hp761282 := BSN.sin_dyadic_bound_f 808611685 536870912 4 3 536870912 268435456 hp761279 hp642702 hp761280 hp761281 hp642705

noncomputable def hp761283 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 808611685) (BSN.sinEvenQ 536870912) 0 3 hp761279 hp642702 hp761280 rfl rfl rfl

noncomputable def hp761284 := hp761282 hp761280 535749701 rfl rfl rfl rfl rfl rfl rfl rfl (hp761283 rfl)

noncomputable def hp761285 := @BSN.binarySplit_of_base3 (BSN.sinOddP 808611685) (BSN.sinOddQ 536870912) 0 3 hp761281 hp642705 hp761280 rfl rfl rfl

noncomputable def hp761286 := nat_lit 995540262713556596195488837413962677456120637841847041645247613913104640

noncomputable def hp761287 := nat_lit 15702955122712277535602272446481385830650647703212249349353220178176

noncomputable def hp761288 := nat_lit 2607341930893878122538841694309750804427066331394270384476701940749271296

noncomputable def hp761289 := BSN.sin_dyadic_bound_f 250898274 536870912 3 2 536870912 268435456 hp761286 hp708845 hp761287 hp761288 hp708848

noncomputable def hp761290 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 250898274) (BSN.sinEvenQ 536870912) 0 2 hp761286 hp708845 hp761287 rfl rfl rfl

noncomputable def hp761291 := hp761289 hp761287 241864727 rfl rfl rfl rfl rfl rfl rfl rfl (hp761290 rfl)

noncomputable def hp761292 := @BSN.binarySplit_of_base2 (BSN.sinOddP 250898274) (BSN.sinOddQ 536870912) 0 2 hp761288 hp708848 hp761287 rfl rfl rfl

noncomputable def hp761293 := hp761278 hd4920 hd4922 hd4924 hd4926 hd4918 (hp761284 (hp761285 rfl) rfl rfl rfl rfl) (hp761291 (hp761292 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761294 := hp761196 (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 462218537 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl rfl (hp761293 rfl rfl rfl rfl rfl) hp761263

noncomputable def hp761295 := nat_lit 16781752599718772563465982204176

noncomputable def hp761296 := BSN.sin_dyadic_bound_f 64004326 536870912 2 1 536870912 268435456 hp761295 hp708890 hp761295 hp761295 hp708891

noncomputable def hp761297 := @BSN.binarySplit_of_base (BSN.sinEvenP 64004326) (BSN.sinEvenQ 536870912) 0 1 hp761295 hp708890 hp761295 rfl rfl rfl

noncomputable def hp761298 := hp761296 hp761295 63852820 rfl rfl rfl rfl rfl rfl rfl rfl (hp761297 rfl)

noncomputable def hp761299 := @BSN.binarySplit_of_base (BSN.sinOddP 64004326) (BSN.sinOddQ 536870912) 0 1 hp761295 hp708891 hp761295 rfl rfl rfl

noncomputable def hp761300 := nat_lit 940502996506617676436592298602011589881899370846947342355400002311190625

noncomputable def hp761301 := nat_lit 45404706817799584669354767419829847631390936435986522623688250390625

noncomputable def hp761302 := nat_lit 2821418180106217430140438186271195109950435330667970054020952630432790625

noncomputable def hp761303 := BSN.cos_dyadic_bound_f 286508565 536870912 3 2 536870912 268435456 hp761300 hp708868 hp761301 hp761302 hp708870

noncomputable def hp761304 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 286508565) (BSN.cosEvenQ 536870912) 0 2 hp761300 hp708868 hp761301 rfl rfl rfl

noncomputable def hp761305 := hp761303 hp761301 462218537 rfl rfl rfl rfl rfl rfl rfl rfl (hp761304 rfl)

noncomputable def hp761306 := @BSN.binarySplit_of_base2 (BSN.cosOddP 286508565) (BSN.cosOddQ 536870912) 0 2 hp761302 hp708870 hp761301 rfl rfl rfl

noncomputable def hp761307 := hp761294 hd4928 hd4930 hd4932 hd4934 hd4918 (hp761298 (hp761299 rfl) rfl rfl rfl rfl) (hp761305 (hp761306 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761308 := hp761191 (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 512398570 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl rfl (hp761307 rfl rfl rfl rfl rfl) hp761263

noncomputable def hp761309 := nat_lit 7510918084726448661506087325696

noncomputable def hp761310 := BSN.sin_dyadic_bound_f 52350792 536870912 2 1 536870912 268435456 hp761309 hp708890 hp761309 hp761309 hp708891

noncomputable def hp761311 := @BSN.binarySplit_of_base (BSN.sinEvenP 52350792) (BSN.sinEvenQ 536870912) 0 1 hp761309 hp708890 hp761309 rfl rfl rfl

noncomputable def hp761312 := hp761310 hp761309 52267869 rfl rfl rfl rfl rfl rfl rfl rfl (hp761311 rfl)

noncomputable def hp761313 := @BSN.binarySplit_of_base (BSN.sinOddP 52350792) (BSN.sinOddQ 536870912) 0 1 hp761309 hp708891 hp761309 rfl rfl rfl

noncomputable def hp761314 := nat_lit 76908357303263361657275167794139370100598275147040672601026082576685575525774271666725030110724046886124478529536

noncomputable def hp761315 := nat_lit 9877203291802315756910967381388433049283715186609443664593220182258388986777783217818619656804135323303936

noncomputable def hp761316 := nat_lit 384338898255211486261517631207418573985089128317856377139378279803730338389829233180317541159210682683487888080896

noncomputable def hp761317 := BSN.sin_dyadic_bound_f 680590944 536870912 4 3 536870912 268435456 hp761314 hp642702 hp761315 hp761316 hp642705

noncomputable def hp761318 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 680590944) (BSN.sinEvenQ 536870912) 0 3 hp761314 hp642702 hp761315 rfl rfl rfl

noncomputable def hp761319 := hp761317 hp761315 512398570 rfl rfl rfl rfl rfl rfl rfl rfl (hp761318 rfl)

noncomputable def hp761320 := @BSN.binarySplit_of_base3 (BSN.sinOddP 680590944) (BSN.sinOddQ 536870912) 0 3 hp761316 hp642705 hp761315 rfl rfl rfl

noncomputable def hp761321 := hp761308 hd4936 hd4938 hd4940 hd4942 hd4918 (hp761312 (hp761313 rfl) rfl rfl rfl rfl) (hp761319 (hp761320 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761322 := hp761186 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 528115399 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl rfl (hp761321 rfl rfl rfl rfl rfl) hp761263

noncomputable def hp761323 := nat_lit 34817921628162697023836226318571402185176305956552209387243815290634914145

noncomputable def hp761324 := nat_lit 19186879128755950604065913142462866129606271928105272112814955702929761

noncomputable def hp761325 := nat_lit 91158730269455744475735914594027780130299534017372187478408292023381936481

noncomputable def hp761326 := BSN.sin_dyadic_bound_f 610064203 536870912 3 2 536870912 268435456 hp761323 hp708845 hp761324 hp761325 hp708848

noncomputable def hp761327 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 610064203) (BSN.sinEvenQ 536870912) 0 2 hp761323 hp708845 hp761324 rfl rfl rfl

noncomputable def hp761328 := hp761326 hp761324 486993523 rfl rfl rfl rfl rfl rfl rfl rfl (hp761327 rfl)

noncomputable def hp761329 := @BSN.binarySplit_of_base2 (BSN.sinOddP 610064203) (BSN.sinOddQ 536870912) 0 2 hp761325 hp708848 hp761324 rfl rfl rfl

noncomputable def hp761330 := nat_lit 88865029697861596029266558443536

noncomputable def hp761331 := BSN.cos_dyadic_bound_f 97091838 536870912 2 1 536870912 268435456 hp761330 hp708767 hp761330 hp761330 hp708768

noncomputable def hp761332 := @BSN.binarySplit_of_base (BSN.cosEvenP 97091838) (BSN.cosEvenQ 536870912) 0 1 hp761330 hp708767 hp761330 rfl rfl rfl

noncomputable def hp761333 := hp761331 hp761330 528115399 rfl rfl rfl rfl rfl rfl rfl rfl (hp761332 rfl)

noncomputable def hp761334 := @BSN.binarySplit_of_base (BSN.cosOddP 97091838) (BSN.cosOddQ 536870912) 0 1 hp761330 hp708768 hp761330 rfl rfl rfl

noncomputable def hp761335 := hp761322 hd4944 hd4946 hd4961 hd4963 hd4918 (hp761328 (hp761329 rfl) rfl rfl rfl rfl) (hp761333 (hp761334 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761336 := @hp761181 209521 268435456 (hp761335 rfl rfl rfl rfl rfl) (hp761335 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp761337 := @hp761179 Bool.true 398892285 268435456 209521 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 863462 1000)) (Enclosure.sfrac Bool.false 863462 1000) 11) hp761336

noncomputable def hp761338 := @Enclosure.Real.IsNear.mulLit_tf hp761170 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1))) 2450045 8388608 1

noncomputable def hp761339 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp761169 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761340 := @hp761339 1 1 0 1 2450045 8388608 1 33554432 2450045 8388608 1

noncomputable def hp761341 := @Enclosure.Real.IsNear.of_eq (hp761169 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761342 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 863462 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761343 := @hp761341 (@Inv.inv Real Real.instInv (Real.sqrt hp761171)) Bool.false 2450045 8388608 1 33554432 (hp761342 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 863462 1000) 863462 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000))))

noncomputable def hp761344 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp761171)) Bool.false 19600360 67108864 2 67108864 2450045 8388608

noncomputable def hp761345 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp761171) Bool.false 229771269 67108864 7 67108864 229771269 67108864 7 67108864

noncomputable def hp761346 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 863462 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761347 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 863462 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761348 := @hp761347 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 863462 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4611192313817

noncomputable def hp761349 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 863462 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 863462 1000 0

noncomputable def hp761350 := @hp761349 1 10680707 67108864 1 67108864 4611192313817 33554432000 431731 33554432000 (Enclosure.Real.IsNear.const Bool.false 863462 1000) hd4949

noncomputable def hp761351 := @hp761348 33554432000 431731 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 863462 1000) 863462 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000))) (hp761350 rfl)

noncomputable def hp761352 := @hp761346 4611192313817 33554432000 431731 33554432000 393352163 393352201 33554432 hp761351 rfl rfl rfl

noncomputable def hp761353 := @Enclosure.Real.IsNear.recentre' hp761171 Bool.false 786704364 67108864 38 67108864 196676091 16777216 19 33554432 (hp761352 rfl rfl rfl)

noncomputable def hp761354 := @Enclosure.Real.IsNear.sqrt_image hp761171 196676091 16777216 19 33554432 114885631 114885638 33554432 (hp761353 rfl) rfl rfl

noncomputable def hp761355 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp761171) 229771269 67108864 7 67108864 9800179 9800181 33554432 (hp761345 (hp761354 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp761356 := @hp761340 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp761343 (@hp761344 1 33554432 (hp761355 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp761357 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761358 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp761359 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1))) (hp761357 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761358 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp761360 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 863462 1000) 863462 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl

noncomputable def hp761361 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761362 := @hp761361 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761358 (Enclosure.sfrac Bool.false 1 16)))) 197356919

noncomputable def hp761363 := @hp761362 33554432 4241 33554432 1353771 16777216 402359929 45675970560000 267176073591549 562949953421312 4752051406395257 76631562409476096000

noncomputable def hp761364 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761365 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761366 := @hp761364 (@Neg.neg Real Real.instNeg hp761365) Bool.true 197356919 33554432 4241 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761367 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761368 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp761369 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp761370 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 152388795) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp761371 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1))) Bool.false 10723408132636195471825

noncomputable def hp761372 := nat_lit 512735432980172240979860933

noncomputable def hp761373 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp761374 := @Enclosure.Real.IsNear.subLit_ff_p hp761171 (Enclosure.sfrac Bool.false 11 1) 196676091 16777216 19 33554432 11 1 0

noncomputable def hp761375 := @hp761373 500000000000000 12126715 16777216 19 33554432 10723408132636195471825 2361183241434822606848 hp761372 hp682805 hd4948 (@hp761374 1 12126715 12126715 16777216 19 33554432 (hp761353 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761376 := @hp761370 152388795 33554432 239 67108864 Bool.true 11409784 67108864 1 10890000 (@hp761371 2361183241434822606848 hp761372 hp682805 152388795 33554432 239 67108864 (hp761375 rfl) rfl) (Enclosure.sfrac_false_div 152388795 33554432)

noncomputable def hp761377 := nat_lit 6769729957532691196805120

noncomputable def hp761378 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 152388795) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp761377) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp761379 := BSN.sin_reduce_arg_pos_rat_q2 152388795 33554432 226375608064910080 72057594037927936 0 hp761377 hp619237 rfl rfl rfl rfl

noncomputable def hp761380 := nat_lit 3490460472840775737545206081997668027575439760688937539926915114854833825968281037626327705493061992323090855992287721888954180587730087890625

noncomputable def hp761381 := nat_lit 2574296008527548791114039327018295633691007649069257271017138615354909644146857139533182118512384947525715930864980669081211090087890625

noncomputable def hp761382 := nat_lit 21143244851110915149182548301753803883436403938206826926442787673071028557829767646293737156487778803309256074686491966100596870762706087890625

noncomputable def hp761383 := BSN.cos_dyadic_bound_f 192407297775 137438953472 4 3 67108864 21801270 hp761380 hp740177 hp761381 hp761382 hp740180

noncomputable def hp761384 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 192407297775) (BSN.cosEvenQ 137438953472) 0 3 hp761380 hp740177 hp761381 rfl rfl rfl

noncomputable def hp761385 := hp761383 hp761381 11409784 rfl rfl rfl rfl rfl rfl rfl rfl (hp761384 rfl)

noncomputable def hp761386 := @BSN.binarySplit_of_base3 (BSN.cosOddP 192407297775) (BSN.cosOddQ 137438953472) 0 3 hp761382 hp740180 hp761381 rfl rfl rfl

noncomputable def hp761387 := @BSN.cos_arg_round Bool.false 11409784 67108864 hp761377 hp619237 192407297775 137438953472 21801270 21780000 (hp761385 (hp761386 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761388 := hp761378 11409784 67108864 0 1000000000000000 21780000 10890000 hp761379 BSN.pi_near_15 hp761387 rfl rfl

noncomputable def hp761389 := @hp761368 1426223 8388608 166863679 45675970560000 (@hp761369 11409784 67108864 2669818864 730815528960000 1426223 8388608 166863679 45675970560000 (hp761376 (hp761388 rfl rfl) rfl rfl) rfl)

noncomputable def hp761390 := @hp761367 1426223 8388608 166863679 45675970560000 197352678 197361160 33554432 hp761389 rfl rfl rfl

noncomputable def hp761391 := @Enclosure.Real.IsNear.recentre' hp761365 Bool.false 394713838 67108864 8482 67108864 197356919 33554432 4241 33554432 (hp761390 rfl rfl rfl)

noncomputable def hp761392 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761358 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp761393 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761358 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 55417667)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp761394 := nat_lit 65425633576247201898409533205

noncomputable def hp761395 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761358 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp761394

noncomputable def hp761396 := nat_lit 42075741811951487580140137121393211

noncomputable def hp761397 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761358 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp761398 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp761399 := @hp761398 (Enclosure.sfrac Bool.false 1 16) 56395300234215 281474976710656 1559164909 1125899906842624 1 16 0

noncomputable def hp761400 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)) 147057216691225

noncomputable def hp761401 := @hp761400 281474976710656 921630701 1125899906842624 12126715 16777216 19 33554432 946156133414275645440 56395300234215 281474976710656 1559164909

noncomputable def hp761402 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)) 12126715 16777216 19

noncomputable def hp761403 := @hp761402 33554432 12126715 16777216 19 33554432 147057216691225 281474976710656 921630701 1125899906842624 (@hp761374 1 12126715 12126715 16777216 19 33554432 (hp761353 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761404 := hp761403 (@hp761374 1 12126715 12126715 16777216 19 33554432 (hp761353 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761405 := @hp761401 1125899906842624 (hp761404 rfl) (@hp761374 1 12126715 12126715 16777216 19 33554432 (hp761353 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761406 := @hp761397 500000000000000 73987486278631 281474976710656 1559164909 1125899906842624 hp761394 hp631146 hp761396 hp682143 hd4948 (@hp761399 1 1183799780458096 73987486278631 281474976710656 1559164909 1125899906842624 (hp761405 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp761407 := @hp761393 55417667 33554432 585 67108864 Bool.true 2707542 33554432 1 10890000 (@hp761395 hp631146 hp761396 hp682143 55417667 33554432 585 67108864 (hp761406 rfl) rfl) (Enclosure.sfrac_true_div 55417667 33554432)

noncomputable def hp761408 := nat_lit 303835249584624402148224047980789545344593088979262107879933203639952345499418283554021990432102641

noncomputable def hp761409 := nat_lit 839032655885606737838958775580279515390598509943375951498979572873543187000358482294591314161

noncomputable def hp761410 := nat_lit 1837844657867741564508899941832670001585758544182548652717006597509609388886019014487188757106776305

noncomputable def hp761411 := BSN.cos_dyadic_bound_t 55417667 33554432 4 3 33554432 10890000 hp761408 hp681868 hp761409 hp761410 hp681871

noncomputable def hp761412 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 55417667) (BSN.cosEvenQ 33554432) 0 3 hp761408 hp681868 hp761409 rfl rfl rfl

noncomputable def hp761413 := hp761411 hp761409 2707542 rfl rfl rfl rfl rfl rfl rfl rfl (hp761412 rfl)

noncomputable def hp761414 := @BSN.binarySplit_of_base3 (BSN.cosOddP 55417667) (BSN.cosOddQ 33554432) 0 3 hp761410 hp681871 hp761409 rfl rfl rfl

noncomputable def hp761415 := hp761407 (BSN.cos_neg_of_bound 55417667 33554432 Bool.true 2707542 33554432 1 10890000 (hp761413 (hp761414 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp761416 := hp761363 (hp761366 (@Enclosure.Real.IsNear.neg hp761365 Bool.false 197356919 33554432 4241 33554432 (hp761391 rfl))) (@hp761392 2707542 33554432 6437758864 730815528960000 1353771 16777216 402359929 45675970560000 (hp761415 rfl) rfl)

noncomputable def hp761417 := @hp761338 33554432 267176073591549 562949953421312 4752051406395257 76631562409476096000 654593403222606669705 4722366482869645213696 2589296291499762541619 hp739341 (hp761356 rfl) (@hp761359 Bool.false 267176073591549 562949953421312 4752051406395257 76631562409476096000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761171 (Enclosure.sfrac Bool.false 11 1)) (hp761360 rfl (hp761174 rfl rfl))) (hp761416 rfl))

noncomputable def hp761418 := @hp761168 114088751760915325805619 hp739341 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 863462 1000))) (@hp761173 114088751760915325805619 hp739341 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 863462 1000) 11 (hp761174 rfl rfl)) (@hp761177 114088751760915325805619 hp739341 hp761337 (hp761417 rfl) rfl rfl))

theorem hd5054 : hp761167 hp739341 := hp761418

noncomputable def hp761419 := nat_lit 10393443054483586544924759

noncomputable def hp761420 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 864738 1000)) Bool.false 22580982327743074310781 18889465931478580854784 hp761419

noncomputable def hp761421 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 864738 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 864738 1000)) Bool.false 22580982327743074310781 18889465931478580854784

noncomputable def hp761422 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 864738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761423 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp761422 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761424 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 864738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761425 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp761423 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp761426 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 864738 1000)) hp761425 Bool.false 22580982327743074310781 18889465931478580854784

noncomputable def hp761427 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 864738 1000) 864738 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl

noncomputable def hp761428 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp761423 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp761429 := nat_lit 6061536288075653603456383451136

noncomputable def hp761430 := @hp761428 283095669 268435456 104913 134217728 2659895618077429373565 18889465931478580854784 343884170651879470364759 hp742094 hp761429 22580982327743074310781 18889465931478580854784

noncomputable def hp761431 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) 11)

noncomputable def hp761432 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) 11) hp761431

noncomputable def hp761433 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) 11)

noncomputable def hp761434 := @hp761433 283095669 536870912 209826 536870912 283095669 536870912 209826 536870912 303971659998560256 283095669 268435456

noncomputable def hp761435 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp761436 := hp761435 BSN.quadSignPos 9 10 11 864738 1000 187 240 536870912 268435456 9007199254740992

noncomputable def hp761437 := hp761436 Bool.false 910780494683 3940 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp761438 := hp761437 Bool.true 14383400 180129 Bool.true 500922054 Bool.true 53241671 28296951008113761 1 Bool.false 431340166

noncomputable def hp761439 := hp761438 Bool.false Bool.false 534233077 Bool.false Bool.false 283095669 209826 BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 431340166 536870912) BSN.abs_quadSignPos

noncomputable def hp761440 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp761441 := hp761440 BSN.quadSignNeg 7 8 9 864738 1000 64 129 536870912 268435456 9007199254740992

noncomputable def hp761442 := hp761441 Bool.false 910780494683 3940 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp761443 := hp761442 Bool.false 56813833 147110 Bool.true 633659619 Bool.true 499271845 28296951008113761 1 Bool.false 204366962

noncomputable def hp761444 := hp761443 Bool.false Bool.false 430355605 Bool.true Bool.true 14383400 180129 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 204366962 536870912) BSN.abs_quadSignNeg

noncomputable def hp761445 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp761446 := hp761445 BSN.quadSignPos 5 6 7 864738 1000 93 8 536870912 268435456 9007199254740992

noncomputable def hp761447 := hp761446 Bool.false 910780494683 3940 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp761448 := hp761447 Bool.false 163117919 109319 Bool.false 523086186 Bool.false 639989931 28296951008113761 1 Bool.false 444165288

noncomputable def hp761449 := hp761448 Bool.true Bool.false 198499164 Bool.false Bool.false 56813833 147110 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 93 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 444165288 536870912) BSN.abs_quadSignPos

noncomputable def hp761450 := hp761440 BSN.quadSignNeg 3 4 5 864738 1000 316 193 536870912 268435456 9007199254740992

noncomputable def hp761451 := hp761450 Bool.false 910780494683 3940 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp761452 := hp761451 Bool.false 333408218 64612 Bool.false 702141467 Bool.false 834879032 28296951008113761 1 Bool.false 139552080

noncomputable def hp761453 := hp761452 Bool.false Bool.false 536804637 Bool.true Bool.false 163117919 109319 BSN.abs_quadSignPos (BSN.cos_quad_nat0 316 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 139552080 536870912) BSN.abs_quadSignNeg

noncomputable def hp761454 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp761455 := hp761454 BSN.quadSignPos 1 2 3 864738 1000 698 475 536870912 268435456 9007199254740992

noncomputable def hp761456 := hp761455 Bool.false 910780494683 3940 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp761457 := hp761456 Bool.false 536870720 3994 Bool.false 351302465 Bool.false 172244589 28296951008113761 1 Bool.false 425976251

noncomputable def hp761458 := hp761457 Bool.true Bool.false 169304839 Bool.false Bool.false 333408218 64612 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 698 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 425976251 536870912) BSN.abs_quadSignPos

noncomputable def hp761459 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) 1) Bool.false

noncomputable def hp761460 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)))

noncomputable def hp761461 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000))) Bool.false 67108840 67108864

noncomputable def hp761462 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 113847561835) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 113847561835 67108864

noncomputable def hp761463 := nat_lit 99830062443173892392513202988551228155896710474021752891

noncomputable def hp761464 := nat_lit 58846074308482067931740087300439192657071546826752000

noncomputable def hp761465 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) Bool.false hp761463 hp761464 65449716010915248887

noncomputable def hp761466 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 864738 4000) (Real.log (Enclosure.sfrac Bool.false 2991088234576 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1729476))))))

noncomputable def hp761467 := nat_lit 232094220099829146126717662960640000

noncomputable def hp761468 := nat_lit 1204204338083260634870523030494843473920

noncomputable def hp761469 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp761466 (Enclosure.sfrac Bool.false 864738 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 864738 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp761467 hp761468)) Bool.false

noncomputable def hp761470 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 864738 1000) 864738 1000 2991088234576 16000000 1729476

noncomputable def hp761471 := hp761470 4000 2000 hp761467 hp761468 (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl rfl rfl rfl

noncomputable def hp761472 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp761466 (Enclosure.sfrac Bool.false 864738 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 864738 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp761467 hp761468) 15280362823915060044311 9007199254740992000

noncomputable def hp761473 := nat_lit 18400677109525811845788033574849762373694881674571689492869120

noncomputable def hp761474 := @hp761472 65449716010915248887 hp739631 hp761467 hp761468 0 1 hp761473 hp761463 hp761464 65449716010915248887 hp739631

noncomputable def hp761475 := @Enclosure.Real.IsNear.subLit_ff_p (hp761466 (Enclosure.sfrac Bool.false 864738 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 864738 2000) (Real.log Real.pi)) 3947687499042814632043 1801439850948198400 5454620504719547 2178000000000000000000

noncomputable def hp761476 := nat_lit 102544779062077171206550087270400

noncomputable def hp761477 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 864738 4000) (Real.log (Enclosure.sfrac Bool.false 2991088234576 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1729476))))))

noncomputable def hp761478 := @hp761477 (Enclosure.sfrac Bool.false 864738 2000) 23632871229787181130263 9007199254740992000 5454620504719547 2178000000000000000000 864738 2000 0

noncomputable def hp761479 := nat_lit 39476874990428146320430000

noncomputable def hp761480 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 864738 4000) (Real.log (Enclosure.sfrac Bool.false 2991088234576 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1729476))))) 23636407046684124886263

noncomputable def hp761481 := nat_lit 53216495032082232243392558335969460224

noncomputable def hp761482 := @hp761480 9007199254740992000 600513389383033 242000000000000000000 883954224235939 2251799813685248 200000001089 8712000000000000000 hp761481 23632871229787181130263 9007199254740992000 5454620504719547

noncomputable def hp761483 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 864738 4000) (Real.log (Enclosure.sfrac Bool.false 2991088234576 16000000)) 864738 4000 0 1 54667210291866727 4503599627370496

noncomputable def hp761484 := nat_lit 117396940183561103627780096

noncomputable def hp761485 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2991088234576) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp761484 hp617687

noncomputable def hp761486 := BSN.log_rat_reduce_isNear 2991088234576 16000000 17 5982176469152 4194304000000 95309899 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp761487 := nat_lit 120920677373637449744743397925504836216383083664445693610759168103535005744886476093831984401771976986139975596087952866614465003520

noncomputable def hp761488 := nat_lit 1267666097356313556721763835570356374401514169067981605306118247571634569909920870464385446322006166683844196784884953073271701504

noncomputable def hp761489 := nat_lit 307962063272143986706565270045223756591976144127833922823543343877055782805789731820934550090038356017778405481388515000320

noncomputable def hp761490 := BSN.log_dyadic_bound 893936234576 5088240234576 6 5 hp761487 268435456 87120000 hp761488 hp761489 95309899 5982176469152

noncomputable def hp761491 := hp761490 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp761492 := @BSN.binarySplit_of_base5 (BSN.artanhP 893936234576) (BSN.artanhQ 5088240234576) 0 5 hp761488 hp761487 hp761489 rfl rfl rfl

noncomputable def hp761493 := hp761486 rfl rfl rfl rfl (hp761491 (hp761492 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp761494 := @hp761483 12500018513 1089000000000000000 23636407046684124886263 9007199254740992000 600513389383033 242000000000000000000 (Enclosure.Real.IsNear.const Bool.false 864738 4000) (BSN.isNear_log_sfrac 2991088234576 16000000 54667210291866727 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp761485 1000001481040000 87120000000000000000000 54667210291866727 4503599627370496 12500018513 1089000000000000000 (hp761493 rfl rfl rfl) rfl)) rfl

noncomputable def hp761495 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1729476)))) 1 4

noncomputable def hp761496 := @hp761495 0 1 883954224235939 562949953421312 200000001089 2178000000000000000 883954224235939 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp761497 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1729476))) 884279719003555 562949953421312 1

noncomputable def hp761498 := @hp761497 2000000000000000 19401 33554432 1 10890000 29660581908237567131648 883954224235939 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp761499 := BSN.arctan_dyadic_bound_f 1000 1729476 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp761500 := hp761499 1 19401 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1729476) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1729476) 0 0 rfl)

noncomputable def hp761501 := hp761496 (hp761498 (hp761500 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp761502 := @hp761475 16607622322809 33554432000 1297107 268435456000 hp761476 15280362823915060044311 9007199254740992000 65449716010915248887 hp739631 (@hp761478 1 hp761479 3947687499042814632043 1801439850948198400 5454620504719547 2178000000000000000000 (@hp761482 2178000000000000000000 hp761494 hp761501 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 864738 2000) rfl rfl)

noncomputable def hp761503 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 864738 2000) (Real.log Real.pi) 864738 2000 0 1 38410761 33554432

noncomputable def hp761504 := hp761502 (@hp761503 3 268435456 16607622322809 33554432000 1297107 268435456000 (Enclosure.Real.IsNear.const Bool.false 864738 2000) hd4909 rfl) rfl

noncomputable def hp761505 := @hp761465 hp739631 113847561835 67108864 493 67108864 (@hp761469 hp761463 hp761464 65449716010915248887 hp739631 (hp761471 rfl rfl rfl rfl rfl) (hp761474 (hp761504 rfl) (Enclosure.Real.IsNear.const Bool.true hp761467 hp761468) rfl rfl)) rfl

noncomputable def hp761506 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 113847561835) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 8099719674028642795520) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp761507 := BSN.sin_reduce_arg_pos_rat_q0 113847561835 67108864 226375608064910080 72057594037927936 270 8099719674028642795520 hp617687 rfl rfl rfl rfl

noncomputable def hp761508 := BSN.cos_dyadic_bound_f 115103939 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp761509 := hp761508 1 67108840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 115103939) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp761510 := hp761509 (@BSN.binarySplit_of_le (BSN.cosOddP 115103939) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp761511 := @BSN.cos_arg_round Bool.false 67108840 67108864 8099719674028642795520 hp617687 115103939 137438953472 21801270 21780000 hp761510 rfl

noncomputable def hp761512 := hp761506 67108840 67108864 270 1000000000000000 21780000 10890000 hp761507 BSN.pi_near_15 hp761511 rfl rfl

noncomputable def hp761513 := @hp761462 493 67108864 Bool.false 67108840 67108864 1 10890000 hp761505 (Enclosure.sfrac_false_div 113847561835 67108864) (hp761512 rfl rfl) rfl

noncomputable def hp761514 := @hp761459 8388605 8388608 339742429 45675970560000 536870720 536870912 3994 536870912 (@hp761460 Bool.false 8388605 8388608 339742429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000)) (@hp761461 5435878864 730815528960000 8388605 8388608 339742429 45675970560000 (hp761513 rfl) rfl))

noncomputable def hp761515 := @hp761465 hp739631 910780494683 536870912 3940 536870912 (@hp761469 hp761463 hp761464 65449716010915248887 hp739631 (hp761471 rfl rfl rfl rfl rfl) (hp761474 (hp761504 rfl) (Enclosure.Real.IsNear.const Bool.true hp761467 hp761468) rfl rfl)) rfl

noncomputable def hp761516 := hp761458 (BSN.cos_quad_nat3 475 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 169304839 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl rfl (hp761514 rfl) hp761515

noncomputable def hp761517 := nat_lit 2125988731983089202230880118625087290328546578515508160319780084345690625

noncomputable def hp761518 := nat_lit 231979483471321892686569728476681951025579550722772172314512812890625

noncomputable def hp761519 := nat_lit 6377502236982324962907267216418308507083588576445078936614711227411290625

noncomputable def hp761520 := BSN.cos_dyadic_bound_f 351302465 536870912 3 2 536870912 268435456 hp761517 hp708868 hp761518 hp761519 hp708870

noncomputable def hp761521 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 351302465) (BSN.cosEvenQ 536870912) 0 2 hp761517 hp708868 hp761518 rfl rfl rfl

noncomputable def hp761522 := hp761520 hp761518 425976251 rfl rfl rfl rfl rfl rfl rfl rfl (hp761521 rfl)

noncomputable def hp761523 := @BSN.binarySplit_of_base2 (BSN.cosOddP 351302465) (BSN.cosOddQ 536870912) 0 2 hp761519 hp708870 hp761518 rfl rfl rfl

noncomputable def hp761524 := nat_lit 880201998662100402314215355924241

noncomputable def hp761525 := BSN.sin_dyadic_bound_f 172244589 536870912 2 1 536870912 268435456 hp761524 hp708890 hp761524 hp761524 hp708891

noncomputable def hp761526 := @BSN.binarySplit_of_base (BSN.sinEvenP 172244589) (BSN.sinEvenQ 536870912) 0 1 hp761524 hp708890 hp761524 rfl rfl rfl

noncomputable def hp761527 := hp761525 hp761524 169304839 rfl rfl rfl rfl rfl rfl rfl rfl (hp761526 rfl)

noncomputable def hp761528 := @BSN.binarySplit_of_base (BSN.sinOddP 172244589) (BSN.sinOddQ 536870912) 0 1 hp761524 hp708891 hp761524 rfl rfl rfl

noncomputable def hp761529 := hp761516 hd4911 hd4913 hd4915 hd4917 hd4918 (hp761522 (hp761523 rfl) rfl rfl rfl rfl) (hp761527 (hp761528 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761530 := hp761453 (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536804637 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl rfl (hp761529 rfl rfl rfl rfl rfl) hp761515

noncomputable def hp761531 := nat_lit 33538144663957748518097538953757030769196385870907549521471517932184130442544831944249864259683739262201796204241

noncomputable def hp761532 := nat_lit 14358050210576333149085738752694243467883823093056039671041221619767919502188916940918628329181402766218961

noncomputable def hp761533 := nat_lit 203228867209226207787631191738092944527797573186933263623668264317360304247115843016736946633527697186554029774545

noncomputable def hp761534 := BSN.cos_dyadic_bound_f 702141467 536870912 4 3 536870912 268435456 hp761531 hp716712 hp761532 hp761533 hp716714

noncomputable def hp761535 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 702141467) (BSN.cosEvenQ 536870912) 0 3 hp761531 hp716712 hp761532 rfl rfl rfl

noncomputable def hp761536 := hp761534 hp761532 139552080 rfl rfl rfl rfl rfl rfl rfl rfl (hp761535 rfl)

noncomputable def hp761537 := @BSN.binarySplit_of_base3 (BSN.cosOddP 702141467) (BSN.cosOddQ 536870912) 0 3 hp761533 hp716714 hp761532 rfl rfl rfl

noncomputable def hp761538 := nat_lit 174337829409527465089204851860742351155613449796502539434057446020362215603110233074839652386661329823613505765376

noncomputable def hp761539 := nat_lit 114678669739996338199454808219097552425878481304841556983769981070767652294719261740862321583881235229310976

noncomputable def hp761540 := nat_lit 870648597081401760619352632182737631000990264846974843502318703955475250458933442133762282557486787573743706177536

noncomputable def hp761541 := BSN.sin_dyadic_bound_f 834879032 536870912 4 3 536870912 268435456 hp761538 hp642702 hp761539 hp761540 hp642705

noncomputable def hp761542 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 834879032) (BSN.sinEvenQ 536870912) 0 3 hp761538 hp642702 hp761539 rfl rfl rfl

noncomputable def hp761543 := hp761541 hp761539 536804637 rfl rfl rfl rfl rfl rfl rfl rfl (hp761542 rfl)

noncomputable def hp761544 := @BSN.binarySplit_of_base3 (BSN.sinOddP 834879032) (BSN.sinOddQ 536870912) 0 3 hp761540 hp642705 hp761539 rfl rfl rfl

noncomputable def hp761545 := hp761530 hd4920 hd4922 hd4924 hd4926 hd4918 (hp761536 (hp761537 rfl) rfl rfl rfl rfl) (hp761543 (hp761544 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761546 := hp761449 (BSN.cos_quad_nat0 8 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 198499164 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl rfl (hp761545 rfl rfl rfl rfl rfl) hp761515

noncomputable def hp761547 := nat_lit 18814110617232947322414705969868248488932675256801110835882445656633729280

noncomputable def hp761548 := nat_lit 5605134113578124720392340320689456911460962576012806775489604878950656

noncomputable def hp761549 := nat_lit 49265976637521449832967404227230963112205117447451269549674660216617656576

noncomputable def hp761550 := BSN.sin_dyadic_bound_f 523086186 536870912 3 2 536870912 268435456 hp761547 hp708845 hp761548 hp761549 hp708848

noncomputable def hp761551 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 523086186) (BSN.sinEvenQ 536870912) 0 2 hp761547 hp708845 hp761548 rfl rfl rfl

noncomputable def hp761552 := hp761550 hp761548 444165288 rfl rfl rfl rfl rfl rfl rfl rfl (hp761551 rfl)

noncomputable def hp761553 := @BSN.binarySplit_of_base2 (BSN.sinOddP 523086186) (BSN.sinOddQ 536870912) 0 2 hp761549 hp708848 hp761548 rfl rfl rfl

noncomputable def hp761554 := nat_lit 23136575464147685330078015841572891188173274006560984598527867017077739022701897966863221194983183383473367149841

noncomputable def hp761555 := nat_lit 4721475006734947302797750278914623668379193129048544627990700903071152484836011028152453297340329143692561

noncomputable def hp761556 := nat_lit 140249525798523975393411610005841929578627570419385274066084222504685050619877191199216392162232999761929622121745

noncomputable def hp761557 := BSN.cos_dyadic_bound_f 639989931 536870912 4 3 536870912 268435456 hp761554 hp716712 hp761555 hp761556 hp716714

noncomputable def hp761558 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 639989931) (BSN.cosEvenQ 536870912) 0 3 hp761554 hp716712 hp761555 rfl rfl rfl

noncomputable def hp761559 := hp761557 hp761555 198499164 rfl rfl rfl rfl rfl rfl rfl rfl (hp761558 rfl)

noncomputable def hp761560 := @BSN.binarySplit_of_base3 (BSN.cosOddP 639989931) (BSN.cosOddQ 536870912) 0 3 hp761556 hp716714 hp761555 rfl rfl rfl

noncomputable def hp761561 := hp761546 hd4928 hd4930 hd4932 hd4934 hd4918 (hp761552 (hp761553 rfl) rfl rfl rfl rfl) (hp761559 (hp761560 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761562 := hp761444 (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 430355605 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl rfl (hp761561 rfl rfl rfl rfl rfl) hp761515

noncomputable def hp761563 := nat_lit 22233626617436365780301212007168927511466376356346091376466373513798990962733503328326555961604234098860537360241

noncomputable def hp761564 := nat_lit 4190563081114409070898103071937451588696105610987638721829425734698173859213722759713870728758985636654961

noncomputable def hp761565 := nat_lit 134780226672661725543416939553913017027439412067307977840588220965262648407800971685066230088416840804535813746545

noncomputable def hp761566 := BSN.cos_dyadic_bound_f 633659619 536870912 4 3 536870912 268435456 hp761563 hp716712 hp761564 hp761565 hp716714

noncomputable def hp761567 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 633659619) (BSN.cosEvenQ 536870912) 0 3 hp761563 hp716712 hp761564 rfl rfl rfl

noncomputable def hp761568 := hp761566 hp761564 204366962 rfl rfl rfl rfl rfl rfl rfl rfl (hp761567 rfl)

noncomputable def hp761569 := @BSN.binarySplit_of_base3 (BSN.cosOddP 633659619) (BSN.cosOddQ 536870912) 0 3 hp761565 hp716714 hp761564 rfl rfl rfl

noncomputable def hp761570 := nat_lit 15614101241013655276280054175499580973327430066910947803068836010440230625

noncomputable def hp761571 := nat_lit 3860971604843006960772997055893006296745511509021718470601566500390625

noncomputable def hp761572 := nat_lit 40887823581961256093273176083456028158043776489942637654323120348247590625

noncomputable def hp761573 := BSN.sin_dyadic_bound_f 499271845 536870912 3 2 536870912 268435456 hp761570 hp708845 hp761571 hp761572 hp708848

noncomputable def hp761574 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 499271845) (BSN.sinEvenQ 536870912) 0 2 hp761570 hp708845 hp761571 rfl rfl rfl

noncomputable def hp761575 := hp761573 hp761571 430355605 rfl rfl rfl rfl rfl rfl rfl rfl (hp761574 rfl)

noncomputable def hp761576 := @BSN.binarySplit_of_base2 (BSN.sinOddP 499271845) (BSN.sinOddQ 536870912) 0 2 hp761572 hp708848 hp761571 rfl rfl rfl

noncomputable def hp761577 := hp761562 hd4936 hd4938 hd4940 hd4942 hd4918 (hp761568 (hp761569 rfl) rfl rfl rfl rfl) (hp761575 (hp761576 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761578 := hp761439 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 534233077 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl rfl (hp761577 rfl rfl rfl rfl rfl) hp761515

noncomputable def hp761579 := nat_lit 15821611814963653224955683536010639986492721055426745952506844705673355520

noncomputable def hp761580 := nat_lit 3964251705334295301363749988151987445499879823842137860766866995323136

noncomputable def hp761581 := nat_lit 41431136441191407682491248903856572937331079149260018795267161206390169856

noncomputable def hp761582 := BSN.sin_dyadic_bound_f 500922054 536870912 3 2 536870912 268435456 hp761579 hp708845 hp761580 hp761581 hp708848

noncomputable def hp761583 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 500922054) (BSN.sinEvenQ 536870912) 0 2 hp761579 hp708845 hp761580 rfl rfl rfl

noncomputable def hp761584 := hp761582 hp761580 431340166 rfl rfl rfl rfl rfl rfl rfl rfl (hp761583 rfl)

noncomputable def hp761585 := @BSN.binarySplit_of_base2 (BSN.sinOddP 500922054) (BSN.sinOddQ 536870912) 0 2 hp761581 hp708848 hp761580 rfl rfl rfl

noncomputable def hp761586 := nat_lit 8035385365325821338686264362081

noncomputable def hp761587 := BSN.cos_dyadic_bound_f 53241671 536870912 2 1 536870912 268435456 hp761586 hp708767 hp761586 hp761586 hp708768

noncomputable def hp761588 := @BSN.binarySplit_of_base (BSN.cosEvenP 53241671) (BSN.cosEvenQ 536870912) 0 1 hp761586 hp708767 hp761586 rfl rfl rfl

noncomputable def hp761589 := hp761587 hp761586 534233077 rfl rfl rfl rfl rfl rfl rfl rfl (hp761588 rfl)

noncomputable def hp761590 := @BSN.binarySplit_of_base (BSN.cosOddP 53241671) (BSN.cosOddQ 536870912) 0 1 hp761586 hp708768 hp761586 rfl rfl rfl

noncomputable def hp761591 := hp761578 hd4944 hd4946 hd4961 hd4963 hd4918 (hp761584 (hp761585 rfl) rfl rfl rfl rfl) (hp761589 (hp761590 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761592 := @hp761434 104913 134217728 (hp761591 rfl rfl rfl rfl rfl) (hp761591 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp761593 := @hp761432 Bool.false 283095669 268435456 104913 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 864738 1000)) (Enclosure.sfrac Bool.false 864738 1000) 11) hp761592

noncomputable def hp761594 := @Enclosure.Real.IsNear.mulLit_tf hp761423 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1))) 9796563 33554432 1

noncomputable def hp761595 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp761422 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761596 := @hp761595 1 1 0 1 9796563 33554432 1 33554432 9796563 33554432 1

noncomputable def hp761597 := @Enclosure.Real.IsNear.of_eq (hp761422 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761598 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 864738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761599 := @hp761597 (@Inv.inv Real Real.instInv (Real.sqrt hp761424)) Bool.false 9796563 33554432 1 33554432 (hp761598 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 864738 1000) 864738 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000))))

noncomputable def hp761600 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp761424)) Bool.false 19593126 67108864 2 67108864 9796563 33554432

noncomputable def hp761601 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp761424) Bool.false 229856110 67108864 6 67108864 114928055 33554432 3 33554432

noncomputable def hp761602 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 864738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761603 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 864738 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761604 := @hp761603 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 864738 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4618006604883

noncomputable def hp761605 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 864738 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 864738 1000 0

noncomputable def hp761606 := @hp761605 1 10680707 67108864 1 67108864 4618006604883 33554432000 432369 33554432000 (Enclosure.Real.IsNear.const Bool.false 864738 1000) hd4949

noncomputable def hp761607 := @hp761604 33554432000 432369 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 864738 1000) 864738 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000))) (hp761606 rfl)

noncomputable def hp761608 := @hp761602 4618006604883 33554432000 432369 33554432000 393642698 393642736 33554432 hp761607 rfl rfl rfl

noncomputable def hp761609 := @Enclosure.Real.IsNear.recentre' hp761424 Bool.false 787285434 67108864 38 67108864 393642717 33554432 19 33554432 (hp761608 rfl rfl rfl)

noncomputable def hp761610 := @Enclosure.Real.IsNear.sqrt_image hp761424 393642717 33554432 19 33554432 114928052 114928058 33554432 (hp761609 rfl) rfl rfl

noncomputable def hp761611 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp761424) 114928055 33554432 3 33554432 9796562 9796564 33554432 (hp761601 (hp761610 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp761612 := @hp761596 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp761599 (@hp761600 1 33554432 (hp761611 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp761613 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761614 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp761615 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1))) (hp761613 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761614 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp761616 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 864738 1000) 864738 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl

noncomputable def hp761617 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761618 := @hp761617 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761614 (Enclosure.sfrac Bool.false 1 16)))) 288808437

noncomputable def hp761619 := @hp761618 33554432 9119 33554432 940115 16777216 405082429 45675970560000 271513143750255 562949953421312 17541832627154503 191578906023690240000

noncomputable def hp761620 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761621 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761622 := @hp761620 (@Neg.neg Real Real.instNeg hp761621) Bool.true 288808437 33554432 9119 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761623 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761624 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp761625 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp761626 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 19276785) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false

noncomputable def hp761627 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1))) Bool.false 21703730473433088795575

noncomputable def hp761628 := nat_lit 512735432982667917626547653

noncomputable def hp761629 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp761630 := @Enclosure.Real.IsNear.subLit_ff_p hp761424 (Enclosure.sfrac Bool.false 11 1) 393642717 33554432 19 33554432 11 1 0

noncomputable def hp761631 := @hp761629 500000000000000 24543965 33554432 19 33554432 21703730473433088795575 4722366482869645213696 hp761628 hp682805 hd4948 (@hp761630 1 24543965 24543965 33554432 19 33554432 (hp761609 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761632 := @hp761626 19276785 4194304 15 4194304 Bool.true 7796863 67108864 1 10890000 (@hp761627 4722366482869645213696 hp761628 hp682805 19276785 4194304 15 4194304 (hp761631 rfl) rfl) (Enclosure.sfrac_false_div 19276785 4194304)

noncomputable def hp761633 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 19276785) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 879101258954668119162880) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp761634 := BSN.sin_reduce_arg_pos_rat_q2 19276785 4194304 226375608064910080 72057594037927936 0 879101258954668119162880 604462909807314587353088 rfl rfl rfl rfl

noncomputable def hp761635 := nat_lit 4067018889815739284795419865921064315247629141497587428907558831675253624674598273082853339342858088657860938011209251335651943937963431890625

noncomputable def hp761636 := nat_lit 4067700879972122160827056095744856029392243877488266295981197431070673910018994284677662577725975756897335901021509902520927090087890625

noncomputable def hp761637 := nat_lit 24629540812407019720635143388733807361420091645490365288943230976022956435127630689894636456003209838258110247226298424909227271015698241490625

noncomputable def hp761638 := BSN.cos_dyadic_bound_f 199884484335 137438953472 4 3 67108864 21801270 hp761635 hp740177 hp761636 hp761637 hp740180

noncomputable def hp761639 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 199884484335) (BSN.cosEvenQ 137438953472) 0 3 hp761635 hp740177 hp761636 rfl rfl rfl

noncomputable def hp761640 := hp761638 hp761636 7796863 rfl rfl rfl rfl rfl rfl rfl rfl (hp761639 rfl)

noncomputable def hp761641 := @BSN.binarySplit_of_base3 (BSN.cosOddP 199884484335) (BSN.cosOddQ 137438953472) 0 3 hp761637 hp740180 hp761636 rfl rfl rfl

noncomputable def hp761642 := @BSN.cos_arg_round Bool.false 7796863 67108864 879101258954668119162880 604462909807314587353088 199884484335 137438953472 21801270 21780000 (hp761640 (hp761641 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761643 := hp761633 7796863 67108864 0 1000000000000000 21780000 10890000 hp761634 BSN.pi_near_15 hp761642 rfl rfl

noncomputable def hp761644 := @hp761624 7796863 67108864 10471519 2854748160000 (@hp761625 7796863 67108864 167544304 45675970560000 7796863 67108864 10471519 2854748160000 (hp761632 (hp761643 rfl rfl) rfl rfl) rfl)

noncomputable def hp761645 := @hp761623 7796863 67108864 10471519 2854748160000 288799318 288817556 33554432 hp761644 rfl rfl rfl

noncomputable def hp761646 := @Enclosure.Real.IsNear.recentre' hp761621 Bool.false 577616874 67108864 18238 67108864 288808437 33554432 9119 33554432 (hp761645 rfl rfl rfl)

noncomputable def hp761647 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761614 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp761648 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761614 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 109176787)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp761649 := nat_lit 257786400535820992182565879045

noncomputable def hp761650 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761614 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp761649

noncomputable def hp761651 := nat_lit 42373676989834177319714792977280961

noncomputable def hp761652 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761614 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp761653 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp761654 := @hp761653 (Enclosure.sfrac Bool.false 1 16) 221152586681655 1125899906842624 1570205239 1125899906842624 1 16 0

noncomputable def hp761655 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)) 602406217921225

noncomputable def hp761656 := @hp761655 1125899906842624 932671031 1125899906842624 24543965 33554432 19 33554432 7420649431433698344960 221152586681655 1125899906842624 1570205239

noncomputable def hp761657 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)) 24543965 33554432 19

noncomputable def hp761658 := @hp761657 33554432 24543965 33554432 19 33554432 602406217921225 1125899906842624 932671031 1125899906842624 (@hp761630 1 24543965 24543965 33554432 19 33554432 (hp761609 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761659 := hp761658 (@hp761630 1 24543965 24543965 33554432 19 33554432 (hp761609 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761660 := @hp761656 1125899906842624 (hp761659 rfl) (@hp761630 1 24543965 24543965 33554432 19 33554432 (hp761609 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761661 := @hp761652 500000000000000 291521330859319 1125899906842624 1570205239 1125899906842624 hp761649 hp682141 hp761651 hp682143 hd4948 (@hp761654 1 4664341293749104 291521330859319 1125899906842624 1570205239 1125899906842624 (hp761660 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp761662 := @hp761648 109176787 67108864 589 67108864 Bool.true 1880230 33554432 1 10890000 (@hp761650 hp682141 hp761651 hp682143 109176787 67108864 589 67108864 (hp761661 rfl) rfl) (Enclosure.sfrac_true_div 109176787 67108864)

noncomputable def hp761663 := nat_lit 1171370228095616281587864978907906494098266916420321436849748505548929776881178880281626926075108141361

noncomputable def hp761664 := nat_lit 2867898058325971930267014846118714943933456065657944023043296889108997064030818168383455040383281

noncomputable def hp761665 := nat_lit 7086626692771272726087507481417140429680392470374209482843637152313386071695715997615427842413603072305

noncomputable def hp761666 := BSN.cos_dyadic_bound_t 109176787 67108864 4 3 33554432 10890000 hp761663 hp745658 hp761664 hp761665 hp745661

noncomputable def hp761667 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 109176787) (BSN.cosEvenQ 67108864) 0 3 hp761663 hp745658 hp761664 rfl rfl rfl

noncomputable def hp761668 := hp761666 hp761664 1880230 rfl rfl rfl rfl rfl rfl rfl rfl (hp761667 rfl)

noncomputable def hp761669 := @BSN.binarySplit_of_base3 (BSN.cosOddP 109176787) (BSN.cosOddQ 67108864) 0 3 hp761665 hp745661 hp761664 rfl rfl rfl

noncomputable def hp761670 := hp761662 (BSN.cos_neg_of_bound 109176787 67108864 Bool.true 1880230 33554432 1 10890000 (hp761668 (hp761669 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp761671 := hp761619 (hp761622 (@Enclosure.Real.IsNear.neg hp761621 Bool.false 288808437 33554432 9119 33554432 (hp761646 rfl))) (@hp761647 1880230 33554432 6481318864 730815528960000 940115 16777216 405082429 45675970560000 (hp761670 rfl) rfl)

noncomputable def hp761672 := @hp761594 33554432 271513143750255 562949953421312 17541832627154503 191578906023690240000 2659895618077429373565 18889465931478580854784 343884170651879470364759 hp742094 (hp761612 rfl) (@hp761615 Bool.false 271513143750255 562949953421312 17541832627154503 191578906023690240000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761424 (Enclosure.sfrac Bool.false 11 1)) (hp761616 rfl (hp761427 rfl rfl))) (hp761671 rfl))

noncomputable def hp761673 := @hp761421 hp761419 hp742094 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 864738 1000))) (@hp761426 hp761419 hp742094 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 864738 1000) 11 (hp761427 rfl rfl)) (@hp761430 hp761419 hp742094 hp761593 (hp761672 rfl) rfl rfl))

theorem hd5055 : hp761420 hp742094 := hp761673

noncomputable def hp761674 := nat_lit 42854776492062960687472957

noncomputable def hp761675 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 866013 1000)) Bool.true 44234242815971035122205 75557863725914323419136 hp761674

noncomputable def hp761676 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 866013 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 866013 1000)) Bool.true 44234242815971035122205 75557863725914323419136

noncomputable def hp761677 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 866013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761678 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp761677 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761679 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 866013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761680 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp761678 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp761681 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 866013 1000)) hp761680 Bool.true 44234242815971035122205 75557863725914323419136

noncomputable def hp761682 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 866013 1000) 866013 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl

noncomputable def hp761683 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp761678 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp761684 := nat_lit 2597726232586859485552957

noncomputable def hp761685 := nat_lit 2968509785279977223955278725120

noncomputable def hp761686 := @hp761683 48891895 67108864 210133 268435456 10813137209888319010275 75557863725914323419136 hp761684 hp738860 hp761685 44234242815971035122205 75557863725914323419136

noncomputable def hp761687 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) 11)

noncomputable def hp761688 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) 11) hp761687

noncomputable def hp761689 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) 11)

noncomputable def hp761690 := @hp761689 195567580 536870912 210133 536870912 195567580 536870912 210133 536870912 209989090064465920 48891895 67108864

noncomputable def hp761691 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp761692 := hp761691 BSN.quadSignPos 9 10 11 866013 1000 187 240 536870912 268435456 9007199254740992

noncomputable def hp761693 := hp761692 Bool.false 912466199554 3945 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp761694 := hp761693 Bool.true 470503815 180393 Bool.true 391360652 Bool.true 8921081 28296951008113761 1 Bool.false 357609061

noncomputable def hp761695 := hp761694 Bool.false Bool.false 536796793 Bool.false Bool.true 195567580 210133 BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 357609061 536870912) BSN.abs_quadSignPos

noncomputable def hp761696 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp761697 := hp761696 BSN.quadSignNeg 7 8 9 866013 1000 64 129 536870912 268435456 9007199254740992

noncomputable def hp761698 := hp761697 Bool.false 912466199554 3945 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp761699 := hp761698 Bool.true 516894071 147326 Bool.true 371354135 Bool.true 317590058 28296951008113761 1 Bool.false 413477663

noncomputable def hp761700 := hp761699 Bool.false Bool.false 299388536 Bool.true Bool.true 470503815 180393 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 413477663 536870912) BSN.abs_quadSignNeg

noncomputable def hp761701 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp761702 := hp761701 BSN.quadSignNeg 5 6 7 866013 1000 94 9 536870912 268435456 9007199254740992

noncomputable def hp761703 := hp761702 Bool.false 912466199554 3945 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp761704 := hp761703 Bool.true 248922865 109480 Bool.false 138998196 Bool.false 150384206 28296951008113761 1 Bool.false 518977582

noncomputable def hp761705 := hp761704 Bool.true Bool.false 148425308 Bool.true Bool.true 516894071 147326 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 518977582 536870912) BSN.abs_quadSignNeg

noncomputable def hp761706 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp761707 := hp761706 BSN.quadSignNeg 3 4 5 866013 1000 317 194 536870912 268435456 9007199254740992

noncomputable def hp761708 := hp761707 Bool.false 912466199554 3945 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp761709 := hp761708 Bool.false 106269760 64708 Bool.false 595598574 Bool.false 575592057 28296951008113761 1 Bool.false 480728569

noncomputable def hp761710 := hp761709 Bool.true Bool.false 256763984 Bool.true Bool.true 248922865 109480 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 317 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 480728569 536870912) BSN.abs_quadSignNeg

noncomputable def hp761711 := hp761691 BSN.quadSignPos 1 2 3 866013 1000 699 476 536870912 268435456 9007199254740992

noncomputable def hp761712 := hp761711 Bool.false 912466199554 3945 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp761713 := hp761712 Bool.true 536870696 4002 Bool.false 719226036 Bool.false 262623059 28296951008113761 1 Bool.false 522594102

noncomputable def hp761714 := hp761713 Bool.false Bool.false 473907495 Bool.false Bool.false 106269760 64708 BSN.abs_quadSignPos (BSN.cos_quad_nat3 699 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 522594102 536870912) BSN.abs_quadSignPos

noncomputable def hp761715 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) 1) Bool.true

noncomputable def hp761716 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)))

noncomputable def hp761717 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000))) Bool.true 67108837 67108864

noncomputable def hp761718 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 891080273) (@Nat.cast Real Real.instNatCast 524288)) Bool.false 891080273 524288

noncomputable def hp761719 := nat_lit 12915570078212762801202510216112500079917715308026051549379

noncomputable def hp761720 := nat_lit 7599178895917297412484945069687234502146817634861056000

noncomputable def hp761721 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) Bool.false hp761719 hp761720 131091830801374117099

noncomputable def hp761722 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 866013 4000) (Real.log (Enclosure.sfrac Bool.false 2999915064676 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1732026))))))

noncomputable def hp761723 := nat_lit 233810311837760689608070848620640000

noncomputable def hp761724 := nat_lit 1214896806502986178919281201643533849920

noncomputable def hp761725 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp761722 (Enclosure.sfrac Bool.false 866013 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 866013 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp761723 hp761724)) Bool.false

noncomputable def hp761726 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 866013 1000) 866013 1000 2999915064676 16000000 1732026

noncomputable def hp761727 := hp761726 4000 2000 hp761723 hp761724 (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl rfl rfl rfl

noncomputable def hp761728 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp761722 (Enclosure.sfrac Bool.false 866013 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 866013 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp761723 hp761724) 30617288512160939026731 18014398509481984000

noncomputable def hp761729 := nat_lit 37196841825252756867463229422404000230163020087115028462211520

noncomputable def hp761730 := @hp761728 131091830801374117099 hp738659 hp761723 hp761724 0 1 hp761729 hp761719 hp761720 131091830801374117099 hp738659

noncomputable def hp761731 := @Enclosure.Real.IsNear.subLit_ff_p (hp761722 (Enclosure.sfrac Bool.false 866013 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 866013 2000) (Real.log Real.pi)) 39546584137693001328939 18014398509481984000 10925178533043169 4356000000000000000000

noncomputable def hp761732 := nat_lit 2054691450811370803257183043584000

noncomputable def hp761733 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 866013 4000) (Real.log (Enclosure.sfrac Bool.false 2999915064676 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1732026))))))

noncomputable def hp761734 := @hp761733 (Enclosure.sfrac Bool.false 866013 2000) 9469387157177802406767 3602879701896396800 10925178533043169 4356000000000000000000 866013 2000 0

noncomputable def hp761735 := nat_lit 15818633655077200531575600

noncomputable def hp761736 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 866013 4000) (Real.log (Enclosure.sfrac Bool.false 2999915064676 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1732026))))) 9470801484715042731567

noncomputable def hp761737 := nat_lit 21323164236246455677990655278203273216

noncomputable def hp761738 := @hp761736 3602879701896396800 3608392844166223 1452000000000000000000 883954710775203 2251799813685248 200000001089 8712000000000000000 hp761737 9469387157177802406767 3602879701896396800 10925178533043169

noncomputable def hp761739 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 866013 4000) (Real.log (Enclosure.sfrac Bool.false 2999915064676 16000000)) 866013 4000 0 1 54680481036168295 4503599627370496

noncomputable def hp761740 := nat_lit 117425438889945510088540160

noncomputable def hp761741 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2999915064676) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp761740 hp617687

noncomputable def hp761742 := BSN.log_rat_reduce_isNear 2999915064676 16000000 17 5999830129352 4194304000000 96100897 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp761743 := nat_lit 123034801308659381160500843679548305076428040149527477397860648426838191621135806525035256383178642712726482484704676341755564523520

noncomputable def hp761744 := nat_lit 1311281672868077995477803820573547660360034190816782399996554315540358132607153956952672339076970927583926874323964901850432405504

noncomputable def hp761745 := nat_lit 339757952292988088012720851398305746741722385629889648385505703145519255974451971924665074445930404195934370803972251320320

noncomputable def hp761746 := BSN.log_dyadic_bound 902763064676 5097067064676 6 5 hp761743 268435456 87120000 hp761744 hp761745 96100897 5999830129352

noncomputable def hp761747 := hp761746 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp761748 := @BSN.binarySplit_of_base5 (BSN.artanhP 902763064676) (BSN.artanhQ 5097067064676) 0 5 hp761744 hp761743 hp761745 rfl rfl rfl

noncomputable def hp761749 := hp761742 rfl rfl rfl rfl (hp761747 (hp761748 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp761750 := @hp761739 12500018513 1089000000000000000 9470801484715042731567 3602879701896396800 3608392844166223 1452000000000000000000 (Enclosure.Real.IsNear.const Bool.false 866013 4000) (BSN.isNear_log_sfrac 2999915064676 16000000 54680481036168295 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp761741 1000001481040000 87120000000000000000000 54680481036168295 4503599627370496 12500018513 1089000000000000000 (hp761749 rfl rfl rfl) rfl)) rfl

noncomputable def hp761751 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1732026)))) 1 4

noncomputable def hp761752 := @hp761751 0 1 883954710775203 562949953421312 200000001089 2178000000000000000 883954710775203 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp761753 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1732026))) 884279719003555 562949953421312 1

noncomputable def hp761754 := @hp761753 2000000000000000 19372 33554432 1 10890000 29660598233786216349696 883954710775203 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp761755 := BSN.arctan_dyadic_bound_f 1000 1732026 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp761756 := hp761755 1 19372 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1732026) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1732026) 0 0 rfl)

noncomputable def hp761757 := hp761752 (hp761754 (hp761756 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp761758 := @hp761731 33264218365893 67108864000 2598039 536870912000 hp761732 30617288512160939026731 18014398509481984000 131091830801374117099 hp738659 (@hp761734 1 hp761735 39546584137693001328939 18014398509481984000 10925178533043169 4356000000000000000000 (@hp761738 4356000000000000000000 hp761750 hp761757 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 866013 2000) rfl rfl)

noncomputable def hp761759 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 866013 2000) (Real.log Real.pi) 866013 2000 0 1 38410761 33554432

noncomputable def hp761760 := hp761758 (@hp761759 3 268435456 33264218365893 67108864000 2598039 536870912000 (Enclosure.Real.IsNear.const Bool.false 866013 2000) hd4909 rfl) rfl

noncomputable def hp761761 := @hp761721 hp738659 891080273 524288 247 33554432 (@hp761725 hp761719 hp761720 131091830801374117099 hp738659 (hp761727 rfl rfl rfl rfl rfl) (hp761730 (hp761760 rfl) (Enclosure.Real.IsNear.const Bool.true hp761723 hp761724) rfl rfl)) rfl

noncomputable def hp761762 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 891080273) (@Nat.cast Real Real.instNatCast 524288)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 118619134052437449506816) (@Nat.cast Real Real.instNatCast 75557863725914323419136)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp761763 := BSN.sin_reduce_arg_pos_rat_q1 891080273 524288 226375608064910080 72057594037927936 270 118619134052437449506816 75557863725914323419136 rfl rfl rfl rfl

noncomputable def hp761764 := nat_lit 14347930613444886214444028148850088269915899096165684843236324281329949895558108609059198704221418516894574426508434076663572019293069765784401

noncomputable def hp761765 := nat_lit 10181670079885465125840324840462258680135912520567105100350181938362001799678624789408246864083673830706610404204283820154020874467685201

noncomputable def hp761766 := nat_lit 71650708152371687553348690351437809581107618882357070822031594798467897802649773638212613170016641180787469767110337289649664946982419751514961

noncomputable def hp761767 := BSN.sin_dyadic_bound_f 215766947899 137438953472 4 3 67108864 21801270 hp761764 hp737934 hp761765 hp761766 hp737937

noncomputable def hp761768 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215766947899) (BSN.sinEvenQ 137438953472) 0 3 hp761764 hp737934 hp761765 rfl rfl rfl

noncomputable def hp761769 := hp761767 hp761765 67108837 rfl rfl rfl rfl rfl rfl rfl rfl (hp761768 rfl)

noncomputable def hp761770 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215766947899) (BSN.sinOddQ 137438953472) 0 3 hp761766 hp737937 hp761765 rfl rfl rfl

noncomputable def hp761771 := @BSN.sin_arg_round Bool.false 67108837 67108864 118619134052437449506816 75557863725914323419136 215766947899 137438953472 21801270 21780000 (hp761769 (hp761770 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761772 := hp761762 67108837 67108864 270 1000000000000000 21780000 10890000 hp761763 BSN.pi_near_15 hp761771 rfl rfl

noncomputable def hp761773 := @hp761718 247 33554432 Bool.true 67108837 67108864 1 10890000 hp761761 (Enclosure.sfrac_false_div 891080273 524288) (hp761772 rfl rfl) rfl

noncomputable def hp761774 := @hp761715 67108837 67108864 170211527 22837985280000 536870696 536870912 4002 536870912 (@hp761716 Bool.true 67108837 67108864 170211527 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000)) (@hp761717 2723384432 365407764480000 67108837 67108864 170211527 22837985280000 (hp761773 rfl) rfl))

noncomputable def hp761775 := @hp761721 hp738659 912466199554 536870912 3945 536870912 (@hp761725 hp761719 hp761720 131091830801374117099 hp738659 (hp761727 rfl rfl rfl rfl rfl) (hp761730 (hp761760 rfl) (Enclosure.Real.IsNear.const Bool.true hp761723 hp761724) rfl rfl)) rfl

noncomputable def hp761776 := hp761714 (BSN.cos_quad_nat0 476 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 473907495 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl rfl (hp761774 rfl) hp761775

noncomputable def hp761777 := nat_lit 95936105516715993612979790905457111863772177215753265443331951010957345550341667836646434174328608932036603805696

noncomputable def hp761778 := nat_lit 19159527993417592492904310889989503140291830059612499684102731068544434290099252922567249078502047818448896

noncomputable def hp761779 := nat_lit 479364945967190442194071093699169542255392642795134736506300721403208722463858785874741898023216042507420886368256

noncomputable def hp761780 := BSN.sin_dyadic_bound_f 719226036 536870912 4 3 536870912 268435456 hp761777 hp642702 hp761778 hp761779 hp642705

noncomputable def hp761781 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 719226036) (BSN.sinEvenQ 536870912) 0 3 hp761777 hp642702 hp761778 rfl rfl rfl

noncomputable def hp761782 := hp761780 hp761778 522594102 rfl rfl rfl rfl rfl rfl rfl rfl (hp761781 rfl)

noncomputable def hp761783 := @BSN.binarySplit_of_base3 (BSN.sinOddP 719226036) (BSN.sinOddQ 536870912) 0 3 hp761779 hp642705 hp761778 rfl rfl rfl

noncomputable def hp761784 := nat_lit 663949431305119312571865176631067003277487115466919275931105087693453601

noncomputable def hp761785 := nat_lit 22628868832286389447382429623147146030535835830736137556890691500321

noncomputable def hp761786 := nat_lit 1991803036177693364936700765033954715540400274729096355518201481697360161

noncomputable def hp761787 := BSN.cos_dyadic_bound_f 262623059 536870912 3 2 536870912 268435456 hp761784 hp708868 hp761785 hp761786 hp708870

noncomputable def hp761788 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 262623059) (BSN.cosEvenQ 536870912) 0 2 hp761784 hp708868 hp761785 rfl rfl rfl

noncomputable def hp761789 := hp761787 hp761785 473907495 rfl rfl rfl rfl rfl rfl rfl rfl (hp761788 rfl)

noncomputable def hp761790 := @BSN.binarySplit_of_base2 (BSN.cosOddP 262623059) (BSN.cosOddQ 536870912) 0 2 hp761786 hp708870 hp761785 rfl rfl rfl

noncomputable def hp761791 := hp761776 hd4911 hd4913 hd4915 hd4917 hd4918 (hp761782 (hp761783 rfl) rfl rfl rfl rfl) (hp761789 (hp761790 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761792 := hp761710 (BSN.cos_quad_nat2 194 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 256763984 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl rfl (hp761791 rfl rfl rfl rfl rfl) hp761775

noncomputable def hp761793 := nat_lit 31629575679238014946554368592538196053827782110352084390915549236604125440

noncomputable def hp761794 := nat_lit 15835405694664116746225545130434415053095934491221571300503610907115776

noncomputable def hp761795 := nat_lit 82813726598308202004338981145484095849939178776031576575054194535351664896

noncomputable def hp761796 := BSN.sin_dyadic_bound_f 595598574 536870912 3 2 536870912 268435456 hp761793 hp708845 hp761794 hp761795 hp708848

noncomputable def hp761797 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 595598574) (BSN.sinEvenQ 536870912) 0 2 hp761793 hp708845 hp761794 rfl rfl rfl

noncomputable def hp761798 := hp761796 hp761794 480728569 rfl rfl rfl rfl rfl rfl rfl rfl (hp761797 rfl)

noncomputable def hp761799 := @BSN.binarySplit_of_base2 (BSN.sinOddP 595598574) (BSN.sinOddQ 536870912) 0 2 hp761795 hp708848 hp761794 rfl rfl rfl

noncomputable def hp761800 := nat_lit 15131616962138592603869604733141324952288545914600258576017670061216683391395455888462920270257141780946516674081

noncomputable def hp761801 := nat_lit 1322444656251688538572987697531573727343199893194497270359683837771974476726027863232363754152424190740001

noncomputable def hp761802 := nat_lit 91750377502170484065487941927680470679422923923648046046665602107144592910901113436054060866624525234494294165025

noncomputable def hp761803 := BSN.cos_dyadic_bound_f 575592057 536870912 4 3 536870912 268435456 hp761800 hp716712 hp761801 hp761802 hp716714

noncomputable def hp761804 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 575592057) (BSN.cosEvenQ 536870912) 0 3 hp761800 hp716712 hp761801 rfl rfl rfl

noncomputable def hp761805 := hp761803 hp761801 256763984 rfl rfl rfl rfl rfl rfl rfl rfl (hp761804 rfl)

noncomputable def hp761806 := @BSN.binarySplit_of_base3 (BSN.cosOddP 575592057) (BSN.cosOddQ 536870912) 0 3 hp761802 hp716714 hp761801 rfl rfl rfl

noncomputable def hp761807 := hp761792 hd4920 hd4922 hd4924 hd4926 hd4918 (hp761798 (hp761799 rfl) rfl rfl rfl rfl) (hp761805 (hp761806 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761808 := hp761705 (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 148425308 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl rfl (hp761807 rfl rfl rfl rfl rfl) hp761775

noncomputable def hp761809 := nat_lit 373281661950564164969237239501056

noncomputable def hp761810 := BSN.cos_dyadic_bound_f 138998196 536870912 2 1 536870912 268435456 hp761809 hp708767 hp761809 hp761809 hp708768

noncomputable def hp761811 := @BSN.binarySplit_of_base (BSN.cosEvenP 138998196) (BSN.cosEvenQ 536870912) 0 1 hp761809 hp708767 hp761809 rfl rfl rfl

noncomputable def hp761812 := hp761810 hp761809 518977582 rfl rfl rfl rfl rfl rfl rfl rfl (hp761811 rfl)

noncomputable def hp761813 := @BSN.binarySplit_of_base (BSN.cosOddP 138998196) (BSN.cosOddQ 536870912) 0 1 hp761809 hp708768 hp761809 rfl rfl rfl

noncomputable def hp761814 := nat_lit 511456742974167248740071726190096

noncomputable def hp761815 := BSN.sin_dyadic_bound_f 150384206 536870912 2 1 536870912 268435456 hp761814 hp708890 hp761814 hp761814 hp708891

noncomputable def hp761816 := @BSN.binarySplit_of_base (BSN.sinEvenP 150384206) (BSN.sinEvenQ 536870912) 0 1 hp761814 hp708890 hp761814 rfl rfl rfl

noncomputable def hp761817 := hp761815 hp761814 148425308 rfl rfl rfl rfl rfl rfl rfl rfl (hp761816 rfl)

noncomputable def hp761818 := @BSN.binarySplit_of_base (BSN.sinOddP 150384206) (BSN.sinOddQ 536870912) 0 1 hp761814 hp708891 hp761814 rfl rfl rfl

noncomputable def hp761819 := hp761808 hd4928 hd4930 hd4932 hd4934 hd4918 (hp761812 (hp761813 rfl) rfl rfl rfl rfl) (hp761817 (hp761818 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761820 := hp761700 (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 299388536 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl rfl (hp761819 rfl rfl rfl rfl rfl) hp761775

noncomputable def hp761821 := nat_lit 2654611720775959109200551985468225369514173952857950598258535796162690625

noncomputable def hp761822 := nat_lit 361664692554195294693411498888747608464986890959761173357576437890625

noncomputable def hp761823 := nat_lit 7963111832942768937012269133406898613325591884791932272428892235612290625

noncomputable def hp761824 := BSN.cos_dyadic_bound_f 371354135 536870912 3 2 536870912 268435456 hp761821 hp708868 hp761822 hp761823 hp708870

noncomputable def hp761825 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 371354135) (BSN.cosEvenQ 536870912) 0 2 hp761821 hp708868 hp761822 rfl rfl rfl

noncomputable def hp761826 := hp761824 hp761822 413477663 rfl rfl rfl rfl rfl rfl rfl rfl (hp761825 rfl)

noncomputable def hp761827 := @BSN.binarySplit_of_base2 (BSN.cosOddP 371354135) (BSN.cosOddQ 536870912) 0 2 hp761823 hp708870 hp761822 rfl rfl rfl

noncomputable def hp761828 := nat_lit 2555915341793713403089000432798053132070677947288231525220342266858594560

noncomputable def hp761829 := nat_lit 103498770039627029236908701502591020867732490327656407672024999158016

noncomputable def hp761830 := nat_lit 6693896420974899516709569948001992103294180199818171122345617896535777536

noncomputable def hp761831 := BSN.sin_dyadic_bound_f 317590058 536870912 3 2 536870912 268435456 hp761828 hp708845 hp761829 hp761830 hp708848

noncomputable def hp761832 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 317590058) (BSN.sinEvenQ 536870912) 0 2 hp761828 hp708845 hp761829 rfl rfl rfl

noncomputable def hp761833 := hp761831 hp761829 299388536 rfl rfl rfl rfl rfl rfl rfl rfl (hp761832 rfl)

noncomputable def hp761834 := @BSN.binarySplit_of_base2 (BSN.sinOddP 317590058) (BSN.sinOddQ 536870912) 0 2 hp761830 hp708848 hp761829 rfl rfl rfl

noncomputable def hp761835 := hp761820 hd4936 hd4938 hd4940 hd4942 hd4918 (hp761826 (hp761827 rfl) rfl rfl rfl rfl) (hp761833 (hp761834 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761836 := hp761695 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536796793 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl rfl (hp761835 rfl rfl rfl rfl rfl) hp761775

noncomputable def hp761837 := nat_lit 5894004611427564357681204042646675686989932696817068951098126972531834880

noncomputable def hp761838 := nat_lit 550322502173717407176898443138767075578998111229360846657838194425856

noncomputable def hp761839 := nat_lit 15435787745878196822886771799928592604946505351864618763886219856697163776

noncomputable def hp761840 := BSN.sin_dyadic_bound_f 391360652 536870912 3 2 536870912 268435456 hp761837 hp708845 hp761838 hp761839 hp708848

noncomputable def hp761841 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 391360652) (BSN.sinEvenQ 536870912) 0 2 hp761837 hp708845 hp761838 rfl rfl rfl

noncomputable def hp761842 := hp761840 hp761838 357609061 rfl rfl rfl rfl rfl rfl rfl rfl (hp761841 rfl)

noncomputable def hp761843 := @BSN.binarySplit_of_base2 (BSN.sinOddP 391360652) (BSN.sinOddQ 536870912) 0 2 hp761839 hp708848 hp761838 rfl rfl rfl

noncomputable def hp761844 := nat_lit 6333881449287536559189690721

noncomputable def hp761845 := BSN.cos_dyadic_bound_f 8921081 536870912 2 1 536870912 268435456 hp761844 hp708767 hp761844 hp761844 hp708768

noncomputable def hp761846 := @BSN.binarySplit_of_base (BSN.cosEvenP 8921081) (BSN.cosEvenQ 536870912) 0 1 hp761844 hp708767 hp761844 rfl rfl rfl

noncomputable def hp761847 := hp761845 hp761844 536796793 rfl rfl rfl rfl rfl rfl rfl rfl (hp761846 rfl)

noncomputable def hp761848 := @BSN.binarySplit_of_base (BSN.cosOddP 8921081) (BSN.cosOddQ 536870912) 0 1 hp761844 hp708768 hp761844 rfl rfl rfl

noncomputable def hp761849 := hp761836 hd4944 hd4946 hd4961 hd4963 hd4918 (hp761842 (hp761843 rfl) rfl rfl rfl rfl) (hp761847 (hp761848 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761850 := @hp761690 210133 268435456 (hp761849 rfl rfl rfl rfl rfl) (hp761849 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp761851 := @hp761688 Bool.true 48891895 67108864 210133 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 866013 1000)) (Enclosure.sfrac Bool.false 866013 1000) 11) hp761850

noncomputable def hp761852 := @Enclosure.Real.IsNear.mulLit_tf hp761678 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1))) 9792955 33554432 1

noncomputable def hp761853 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp761677 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761854 := @hp761853 1 1 0 1 9792955 33554432 1 33554432 9792955 33554432 1

noncomputable def hp761855 := @Enclosure.Real.IsNear.of_eq (hp761677 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761856 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 866013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761857 := @hp761855 (@Inv.inv Real Real.instInv (Real.sqrt hp761679)) Bool.false 9792955 33554432 1 33554432 (hp761856 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 866013 1000) 866013 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000))))

noncomputable def hp761858 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp761679)) Bool.false 19585910 67108864 2 67108864 9792955 33554432

noncomputable def hp761859 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp761679) Bool.false 229940790 67108864 6 67108864 114970395 33554432 3 33554432

noncomputable def hp761860 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 866013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761861 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 866013 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761862 := @hp761861 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 866013 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9249631111191

noncomputable def hp761863 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 866013 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 866013 1000 0

noncomputable def hp761864 := @hp761863 1 10680707 67108864 1 67108864 9249631111191 67108864000 866013 67108864000 (Enclosure.Real.IsNear.const Bool.false 866013 1000) hd4949

noncomputable def hp761865 := @hp761862 67108864000 866013 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 866013 1000) 866013 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000))) (hp761864 rfl)

noncomputable def hp761866 := @hp761860 9249631111191 67108864000 866013 67108864000 393932791 393932829 33554432 hp761865 rfl rfl rfl

noncomputable def hp761867 := @Enclosure.Real.IsNear.recentre' hp761679 Bool.false 787865620 67108864 38 67108864 196966405 16777216 19 33554432 (hp761866 rfl rfl rfl)

noncomputable def hp761868 := @Enclosure.Real.IsNear.sqrt_image hp761679 196966405 16777216 19 33554432 114970392 114970398 33554432 (hp761867 rfl) rfl rfl

noncomputable def hp761869 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp761679) 114970395 33554432 3 33554432 9792954 9792956 33554432 (hp761859 (hp761868 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp761870 := @hp761854 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp761857 (@hp761858 1 33554432 (hp761869 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp761871 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761872 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp761873 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1))) (hp761871 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761872 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp761874 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 866013 1000) 866013 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl

noncomputable def hp761875 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761876 := @hp761875 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761872 (Enclosure.sfrac Bool.false 1 16)))) 1080929721

noncomputable def hp761877 := @hp761876 67108864 63865 67108864 1021505 33554432 204242777 22837985280000 1104175114650105 2251799813685248 265188029375343947 1532631248189521920000

noncomputable def hp761878 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761879 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761880 := @hp761878 (@Neg.neg Real Real.instNeg hp761879) Bool.true 1080929721 67108864 63865 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761881 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp761882 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp761883 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp761884 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 39009247) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false

noncomputable def hp761885 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1))) Bool.false 10980126914978993538095

noncomputable def hp761886 := nat_lit 512735432985159797522144709

noncomputable def hp761887 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp761888 := @Enclosure.Real.IsNear.subLit_ff_p hp761679 (Enclosure.sfrac Bool.false 11 1) 196966405 16777216 19 33554432 11 1 0

noncomputable def hp761889 := @hp761887 500000000000000 12417029 16777216 19 33554432 10980126914978993538095 2361183241434822606848 hp761886 hp682805 hd4948 (@hp761888 1 12417029 12417029 16777216 19 33554432 (hp761867 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761890 := @hp761884 39009247 8388608 15 4194304 Bool.true 4166413 67108864 1 10890000 (@hp761885 2361183241434822606848 hp761886 hp682805 39009247 8388608 15 4194304 (hp761889 rfl) rfl) (Enclosure.sfrac_false_div 39009247 8388608)

noncomputable def hp761891 := nat_lit 1823872494466178014511104

noncomputable def hp761892 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 39009247) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp761891) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp761893 := BSN.sin_reduce_arg_pos_rat_q2 39009247 8388608 226375608064910080 72057594037927936 0 hp761891 hp630689 rfl rfl rfl rfl

noncomputable def hp761894 := nat_lit 4711517722409558242073577966612506931005799538087460587282622749409405960828688651670266672528787852300413937891884841201364011938499392573121

noncomputable def hp761895 := nat_lit 6316200732333872830799964433954093282073885302832078387689961210079497587185996584806391507421847999691616545984535092555953498637864641

noncomputable def hp761896 := nat_lit 28524595164752405594197091843906523547956470312104180029120608343207147422196412421506854796593361138370104082200414594736130780292393767931585

noncomputable def hp761897 := BSN.cos_dyadic_bound_f 207350296303 137438953472 4 3 67108864 21801270 hp761894 hp740177 hp761895 hp761896 hp740180

noncomputable def hp761898 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 207350296303) (BSN.cosEvenQ 137438953472) 0 3 hp761894 hp740177 hp761895 rfl rfl rfl

noncomputable def hp761899 := hp761897 hp761895 4166413 rfl rfl rfl rfl rfl rfl rfl rfl (hp761898 rfl)

noncomputable def hp761900 := @BSN.binarySplit_of_base3 (BSN.cosOddP 207350296303) (BSN.cosOddQ 137438953472) 0 3 hp761896 hp740180 hp761895 rfl rfl rfl

noncomputable def hp761901 := @BSN.cos_arg_round Bool.false 4166413 67108864 hp761891 hp630689 207350296303 137438953472 21801270 21780000 (hp761899 (hp761900 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp761902 := hp761892 4166413 67108864 0 1000000000000000 21780000 10890000 hp761893 BSN.pi_near_15 hp761901 rfl rfl

noncomputable def hp761903 := @hp761882 4166413 67108864 10471519 2854748160000 (@hp761883 4166413 67108864 167544304 45675970560000 4166413 67108864 10471519 2854748160000 (hp761890 (hp761902 rfl rfl) rfl rfl) rfl)

noncomputable def hp761904 := @hp761881 4166413 67108864 10471519 2854748160000 540432928 540496793 33554432 hp761903 rfl rfl rfl

noncomputable def hp761905 := @Enclosure.Real.IsNear.recentre' hp761879 Bool.false 1080929721 67108864 63865 67108864 1080929721 67108864 63865 67108864 (hp761904 rfl rfl rfl)

noncomputable def hp761906 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761872 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp761907 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761872 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 53728841)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp761908 := nat_lit 63431819965055955118377722645

noncomputable def hp761909 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761872 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp761908

noncomputable def hp761910 := nat_lit 42671158909592907773998343045802243

noncomputable def hp761911 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp761872 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp761912 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp761913 := @hp761912 (Enclosure.sfrac Bool.false 1 16) 54140568424423 281474976710656 1581228773 1125899906842624 1 16 0

noncomputable def hp761914 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)) 154182609186841

noncomputable def hp761915 := @hp761914 281474976710656 943694565 1125899906842624 12417029 16777216 19 33554432 908328010819324346368 54140568424423 281474976710656 1581228773

noncomputable def hp761916 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)) 12417029 16777216 19

noncomputable def hp761917 := @hp761916 33554432 12417029 16777216 19 33554432 154182609186841 281474976710656 943694565 1125899906842624 (@hp761888 1 12417029 12417029 16777216 19 33554432 (hp761867 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761918 := hp761917 (@hp761888 1 12417029 12417029 16777216 19 33554432 (hp761867 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761919 := @hp761915 1125899906842624 (hp761918 rfl) (@hp761888 1 12417029 12417029 16777216 19 33554432 (hp761867 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp761920 := @hp761911 500000000000000 71732754468839 281474976710656 1581228773 1125899906842624 hp761908 hp631146 hp761910 hp682143 hd4948 (@hp761913 1 1147724071501424 71732754468839 281474976710656 1581228773 1125899906842624 (hp761919 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp761921 := @hp761907 53728841 33554432 297 33554432 Bool.true 1021505 33554432 1 10890000 (@hp761909 hp631146 hp761910 hp682143 53728841 33554432 297 33554432 (hp761920 rfl) rfl) (Enclosure.sfrac_true_div 53728841 33554432)

noncomputable def hp761922 := nat_lit 268319232593155410587081913608478650434751839987921070429502307162801044332220806648997527027182561

noncomputable def hp761923 := nat_lit 578748220345951219035403432497611169949804578270032086581469705491855944214196499849406835681

noncomputable def hp761924 := nat_lit 1623570467660336641292604667434636206239544672515195226193543802949648372601639504445508895384267745

noncomputable def hp761925 := BSN.cos_dyadic_bound_t 53728841 33554432 4 3 33554432 10890000 hp761922 hp681868 hp761923 hp761924 hp681871

noncomputable def hp761926 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 53728841) (BSN.cosEvenQ 33554432) 0 3 hp761922 hp681868 hp761923 rfl rfl rfl

noncomputable def hp761927 := hp761925 hp761923 1021505 rfl rfl rfl rfl rfl rfl rfl rfl (hp761926 rfl)

noncomputable def hp761928 := @BSN.binarySplit_of_base3 (BSN.cosOddP 53728841) (BSN.cosOddQ 33554432) 0 3 hp761924 hp681871 hp761923 rfl rfl rfl

noncomputable def hp761929 := hp761921 (BSN.cos_neg_of_bound 53728841 33554432 Bool.true 1021505 33554432 1 10890000 (hp761927 (hp761928 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp761930 := hp761877 (hp761880 (@Enclosure.Real.IsNear.neg hp761879 Bool.false 1080929721 67108864 63865 67108864 (hp761905 rfl))) (@hp761906 1021505 33554432 3267884432 365407764480000 1021505 33554432 204242777 22837985280000 (hp761929 rfl) rfl)

noncomputable def hp761931 := @hp761852 33554432 1104175114650105 2251799813685248 265188029375343947 1532631248189521920000 10813137209888319010275 75557863725914323419136 hp761684 hp738860 (hp761870 rfl) (@hp761873 Bool.false 1104175114650105 2251799813685248 265188029375343947 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761679 (Enclosure.sfrac Bool.false 11 1)) (hp761874 rfl (hp761682 rfl rfl))) (hp761930 rfl))

noncomputable def hp761932 := @hp761676 hp761674 hp738860 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 866013 1000))) (@hp761681 hp761674 hp738860 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 866013 1000) 11 (hp761682 rfl rfl)) (@hp761686 hp761674 hp738860 hp761851 (hp761931 rfl) rfl rfl))

theorem hd5056 : hp761675 hp738860 := hp761932

noncomputable def hp761933 := nat_lit 7641490835283237948209869

noncomputable def hp761934 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 867289 1000)) Bool.false 11106355472190084315145 9444732965739290427392 hp761933

noncomputable def hp761935 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 867289 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 867289 1000)) Bool.false 11106355472190084315145 9444732965739290427392

noncomputable def hp761936 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 867289 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761937 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp761936 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp761938 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 867289 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp761939 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp761937 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp761940 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 867289 1000)) hp761939 Bool.false 11106355472190084315145 9444732965739290427392

noncomputable def hp761941 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 867289 1000) 867289 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl

noncomputable def hp761942 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp761937 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp761943 := nat_lit 2601864028150548417329869

noncomputable def hp761944 := nat_lit 2981339595675440601814395781120

noncomputable def hp761945 := @hp761942 276600839 268435456 105223 134217728 1374328632730970585097 9444732965739290427392 hp761943 hp752398 hp761944 11106355472190084315145 9444732965739290427392

noncomputable def hp761946 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) 11)

noncomputable def hp761947 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) 11) hp761946

noncomputable def hp761948 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) 11)

noncomputable def hp761949 := @hp761948 276600839 536870912 210446 536870912 276600839 536870912 210446 536870912 296997889387790336 276600839 268435456

noncomputable def hp761950 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp761951 := hp761950 BSN.quadSignPos 9 10 11 867289 1000 187 239 536870912 268435456 9007199254740992

noncomputable def hp761952 := hp761951 Bool.false 914153731327 3951 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp761953 := hp761952 Bool.false 30175617 180662 Bool.true 281208539 Bool.true 807375805 28296951008113761 1 Bool.false 268525159

noncomputable def hp761954 := hp761953 Bool.false Bool.false 535668450 Bool.false Bool.false 276600839 210446 BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 268525159 536870912) BSN.abs_quadSignPos

noncomputable def hp761955 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp761956 := hp761955 BSN.quadSignNeg 7 8 9 867289 1000 64 129 536870912 268435456 9007199254740992

noncomputable def hp761957 := hp761956 Bool.false 914153731327 3951 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp761958 := hp761957 Bool.true 111173773 147546 Bool.true 108338141 Bool.true 135260995 28296951008113761 1 Bool.false 525976880

noncomputable def hp761959 := hp761958 Bool.false Bool.false 133834572 Bool.true Bool.false 30175617 180662 BSN.abs_quadSignPos (BSN.cos_quad_nat0 64 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 525976880 536870912) BSN.abs_quadSignNeg

noncomputable def hp761960 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp761961 := hp761960 BSN.quadSignNeg 5 6 7 867289 1000 94 9 536870912 268435456 9007199254740992

noncomputable def hp761962 := hp761961 Bool.false 914153731327 3951 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp761963 := hp761962 Bool.false 149043754 109644 Bool.false 599090020 Bool.false 504875536 28296951008113761 1 Bool.false 235888335

noncomputable def hp761964 := hp761963 Bool.true Bool.false 433682330 Bool.true Bool.true 111173773 147546 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 94 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 235888335 536870912) BSN.abs_quadSignNeg

noncomputable def hp761965 := hp761960 BSN.quadSignPos 3 4 5 867289 1000 318 195 536870912 268435456 9007199254740992

noncomputable def hp761966 := hp761965 Bool.false 914153731327 3951 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp761967 := hp761966 Bool.false 179397137 64806 Bool.false 490138322 Bool.false 317267924 28296951008113761 1 Bool.false 328248815

noncomputable def hp761968 := hp761967 Bool.true Bool.false 299121087 Bool.false Bool.false 149043754 109644 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 318 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 328248815 536870912) BSN.abs_quadSignPos

noncomputable def hp761969 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp761970 := hp761969 BSN.quadSignNeg 1 2 3 867289 1000 701 477 536870912 268435456 9007199254740992

noncomputable def hp761971 := hp761970 Bool.false 914153731327 3951 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp761972 := hp761971 Bool.false 536870736 4010 Bool.false 245289522 Bool.false 354238618 28296951008113761 1 Bool.false 236844281

noncomputable def hp761973 := hp761972 Bool.true Bool.false 329088613 Bool.true Bool.false 179397137 64806 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 701 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 236844281 536870912) BSN.abs_quadSignNeg

noncomputable def hp761974 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) 1) Bool.false

noncomputable def hp761975 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)))

noncomputable def hp761976 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000))) Bool.false 67108842 67108864

noncomputable def hp761977 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 114269216415) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 114269216415 67108864

noncomputable def hp761978 := nat_lit 117488429749528393968786903605654038189934247202228236664711

noncomputable def hp761979 := nat_lit 68999467231289452800665323791767903025695454098620416000

noncomputable def hp761980 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) Bool.false hp761978 hp761979 43761460160640433349

noncomputable def hp761981 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 867289 4000) (Real.log (Enclosure.sfrac Bool.false 3008761838084 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1734578))))))

noncomputable def hp761982 := nat_lit 235537897441871551290162081015520000

noncomputable def hp761983 := nat_lit 1225676755312744830928745255103391951680

noncomputable def hp761984 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp761981 (Enclosure.sfrac Bool.false 867289 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 867289 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp761982 hp761983)) Bool.false

noncomputable def hp761985 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 867289 1000) 867289 1000 3008761838084 16000000 1734578

noncomputable def hp761986 := hp761985 4000 2000 hp761982 hp761983 (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl rfl rfl rfl

noncomputable def hp761987 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp761981 (Enclosure.sfrac Bool.false 867289 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 867289 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp761982 hp761983) 30673912677188307319439 18014398509481984000

noncomputable def hp761988 := nat_lit 37596297519849086070011809153809292220778959104713035732707520

noncomputable def hp761989 := @hp761987 43761460160640433349 hp737908 hp761982 hp761983 0 1 hp761988 hp761978 hp761979 43761460160640433349 hp737908

noncomputable def hp761990 := @Enclosure.Real.IsNear.subLit_ff_p (hp761981 (Enclosure.sfrac Bool.false 867289 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 867289 2000) (Real.log Real.pi)) 39616364896464550034063 18014398509481984000 3647042852221919 1452000000000000000000

noncomputable def hp761991 := nat_lit 2058491434201306018290436407296000

noncomputable def hp761992 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 867289 4000) (Real.log (Enclosure.sfrac Bool.false 3008761838084 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1734578))))))

noncomputable def hp761993 := @hp761992 (Enclosure.sfrac Bool.false 867289 2000) 47428209730909610244751 18014398509481984000 3647042852221919 1452000000000000000000 867289 2000 0

noncomputable def hp761994 := nat_lit 79232729792929100068126000

noncomputable def hp761995 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 867289 4000) (Real.log (Enclosure.sfrac Bool.false 3008761838084 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1734578))))) 47435281372353908252751

noncomputable def hp761996 := nat_lit 106798833835487126530719534632558133248

noncomputable def hp761997 := @hp761995 18014398509481984000 10841128556121257 4356000000000000000000 883955180537251 2251799813685248 200000001089 8712000000000000000 hp761996 47428209730909610244751 18014398509481984000 3647042852221919

noncomputable def hp761998 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 867289 4000) (Real.log (Enclosure.sfrac Bool.false 3008761838084 16000000)) 867289 4000 0 1 54693742653664359 4503599627370496

noncomputable def hp761999 := nat_lit 117453917996664338232901632

noncomputable def hp762000 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3008761838084) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp761999 hp617687

noncomputable def hp762001 := BSN.log_rat_reduce_isNear 3008761838084 16000000 17 6017523676168 4194304000000 96891351 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp762002 := nat_lit 125187023071667999637604965665421829440446051700778969099330219454918892786690908964131643261878272764000688027028593512729170411520

noncomputable def hp762003 := nat_lit 1356210812270869683988548983130501446366094049643477089381444540864774207657257536692442880531020133942933908305848482819661103104

noncomputable def hp762004 := nat_lit 374560385094544083285865752936962001993840852669101604054501397884733169457409610932880772832161373475606008763436179128320

noncomputable def hp762005 := BSN.log_dyadic_bound 911609838084 5105913838084 6 5 hp762002 268435456 87120000 hp762003 hp762004 96891351 6017523676168

noncomputable def hp762006 := hp762005 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp762007 := @BSN.binarySplit_of_base5 (BSN.artanhP 911609838084) (BSN.artanhQ 5105913838084) 0 5 hp762003 hp762002 hp762004 rfl rfl rfl

noncomputable def hp762008 := hp762001 rfl rfl rfl rfl (hp762006 (hp762007 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp762009 := @hp761998 12500018513 1089000000000000000 47435281372353908252751 18014398509481984000 10841128556121257 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 867289 4000) (BSN.isNear_log_sfrac 3008761838084 16000000 54693742653664359 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp762000 1000001481040000 87120000000000000000000 54693742653664359 4503599627370496 12500018513 1089000000000000000 (hp762008 rfl rfl rfl) rfl)) rfl

noncomputable def hp762010 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1734578)))) 1 4

noncomputable def hp762011 := @hp762010 0 1 883955180537251 562949953421312 200000001089 2178000000000000000 883955180537251 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp762012 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1734578))) 884279719003555 562949953421312 1

noncomputable def hp762013 := @hp762012 2000000000000000 19344 33554432 1 10890000 29660613996384912146432 883955180537251 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp762014 := BSN.arctan_dyadic_bound_f 1000 1734578 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp762015 := hp762014 1 19344 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1734578) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1734578) 0 0 rfl)

noncomputable def hp762016 := hp762011 (hp762013 (hp762015 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp762017 := @hp761990 33313230496929 67108864000 2601867 536870912000 hp761991 30673912677188307319439 18014398509481984000 43761460160640433349 hp737908 (@hp761993 1 hp761994 39616364896464550034063 18014398509481984000 3647042852221919 1452000000000000000000 (@hp761997 1452000000000000000000 hp762009 hp762016 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 867289 2000) rfl rfl)

noncomputable def hp762018 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 867289 2000) (Real.log Real.pi) 867289 2000 0 1 38410761 33554432

noncomputable def hp762019 := hp762017 (@hp762018 3 268435456 33313230496929 67108864000 2601867 536870912000 (Enclosure.Real.IsNear.const Bool.false 867289 2000) hd4909 rfl) rfl

noncomputable def hp762020 := @hp761980 hp737908 114269216415 67108864 495 67108864 (@hp761984 hp761978 hp761979 43761460160640433349 hp737908 (hp761986 rfl rfl rfl rfl rfl) (hp761989 (hp762019 rfl) (Enclosure.Real.IsNear.const Bool.true hp761982 hp761983) rfl rfl)) rfl

noncomputable def hp762021 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 114269216415) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 7689241238629567692800) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp762022 := BSN.sin_reduce_arg_pos_rat_q0 114269216415 67108864 226375608064910080 72057594037927936 271 7689241238629567692800 hp617687 rfl rfl rfl rfl

noncomputable def hp762023 := BSN.cos_dyadic_bound_f 109270690 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp762024 := hp762023 1 67108842 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 109270690) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp762025 := hp762024 (@BSN.binarySplit_of_le (BSN.cosOddP 109270690) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp762026 := @BSN.cos_arg_round Bool.false 67108842 67108864 7689241238629567692800 hp617687 109270690 137438953472 21801270 21780000 hp762025 rfl

noncomputable def hp762027 := hp762021 67108842 67108864 271 1000000000000000 21780000 10890000 hp762022 BSN.pi_near_15 hp762026 rfl rfl

noncomputable def hp762028 := @hp761977 495 67108864 Bool.false 67108842 67108864 1 10890000 hp762020 (Enclosure.sfrac_false_div 114269216415 67108864) (hp762027 rfl rfl) rfl

noncomputable def hp762029 := @hp761974 33554421 33554432 341103679 45675970560000 536870736 536870912 4010 536870912 (@hp761975 Bool.false 33554421 33554432 341103679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000)) (@hp761976 5457658864 730815528960000 33554421 33554432 341103679 45675970560000 (hp762028 rfl) rfl))

noncomputable def hp762030 := @hp761980 hp737908 914153731327 536870912 3951 536870912 (@hp761984 hp761978 hp761979 43761460160640433349 hp737908 (hp761986 rfl rfl rfl rfl rfl) (hp761989 (hp762019 rfl) (Enclosure.Real.IsNear.const Bool.true hp761982 hp761983) rfl rfl)) rfl

noncomputable def hp762031 := hp761973 (BSN.cos_quad_nat1 477 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 329088613 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl rfl (hp762029 rfl) hp762030

noncomputable def hp762032 := nat_lit 909459846814737730766175036551049433850278601438545189630466271934398720

noncomputable def hp762033 := nat_lit 13104847613409018440345473178330455075251209588849536258522272481536

noncomputable def hp762034 := nat_lit 2381897429047224727881555012581888363156798311333045930735374057101312256

noncomputable def hp762035 := BSN.sin_dyadic_bound_f 245289522 536870912 3 2 536870912 268435456 hp762032 hp708845 hp762033 hp762034 hp708848

noncomputable def hp762036 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 245289522) (BSN.sinEvenQ 536870912) 0 2 hp762032 hp708845 hp762033 rfl rfl rfl

noncomputable def hp762037 := hp762035 hp762033 236844281 rfl rfl rfl rfl rfl rfl rfl rfl (hp762036 rfl)

noncomputable def hp762038 := @BSN.binarySplit_of_base2 (BSN.sinOddP 245289522) (BSN.sinOddQ 536870912) 0 2 hp762034 hp708848 hp762033 rfl rfl rfl

noncomputable def hp762039 := nat_lit 3956144296407749699204132079088027503373258468121760081128751359912976640

noncomputable def hp762040 := nat_lit 247951784947535577382013392729579356553522465271928295663136558162176

noncomputable def hp762041 := nat_lit 10360928854368477011742679804499462237495542665851312328572798959630295296

noncomputable def hp762042 := BSN.sin_dyadic_bound_f 354238618 536870912 3 2 536870912 268435456 hp762039 hp708845 hp762040 hp762041 hp708848

noncomputable def hp762043 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 354238618) (BSN.sinEvenQ 536870912) 0 2 hp762039 hp708845 hp762040 rfl rfl rfl

noncomputable def hp762044 := hp762042 hp762040 329088613 rfl rfl rfl rfl rfl rfl rfl rfl (hp762043 rfl)

noncomputable def hp762045 := @BSN.binarySplit_of_base2 (BSN.sinOddP 354238618) (BSN.sinOddQ 536870912) 0 2 hp762041 hp708848 hp762040 rfl rfl rfl

noncomputable def hp762046 := hp762031 hd4911 hd4913 hd4915 hd4917 hd4918 (hp762037 (hp762038 rfl) rfl rfl rfl rfl) (hp762044 (hp762045 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762047 := hp761968 (BSN.cos_quad_nat3 195 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 299121087 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl rfl (hp762046 rfl rfl rfl rfl rfl) hp762030

noncomputable def hp762048 := nat_lit 8058291346317205266106239858181508288456163005495186737228684747385487616

noncomputable def hp762049 := nat_lit 3330805529998922079724545539461719824241192525347437201841894626836736

noncomputable def hp762050 := nat_lit 24168212427891617954159270483465601425720006631434865337282370452902789376

noncomputable def hp762051 := BSN.cos_dyadic_bound_f 490138322 536870912 3 2 536870912 268435456 hp762048 hp708868 hp762049 hp762050 hp708870

noncomputable def hp762052 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 490138322) (BSN.cosEvenQ 536870912) 0 2 hp762048 hp708868 hp762049 rfl rfl rfl

noncomputable def hp762053 := hp762051 hp762049 328248815 rfl rfl rfl rfl rfl rfl rfl rfl (hp762052 rfl)

noncomputable def hp762054 := @BSN.binarySplit_of_base2 (BSN.cosOddP 490138322) (BSN.cosOddQ 536870912) 0 2 hp762050 hp708870 hp762049 rfl rfl rfl

noncomputable def hp762055 := nat_lit 2545560753886555850658753824260694596793957908969759553284015105983447040

noncomputable def hp762056 := nat_lit 102661908795957742685831958011532706644658296023262992653186435710976

noncomputable def hp762057 := nat_lit 6666778617088643296332387716560276700554369838631999261374791547155972096

noncomputable def hp762058 := BSN.sin_dyadic_bound_f 317267924 536870912 3 2 536870912 268435456 hp762055 hp708845 hp762056 hp762057 hp708848

noncomputable def hp762059 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 317267924) (BSN.sinEvenQ 536870912) 0 2 hp762055 hp708845 hp762056 rfl rfl rfl

noncomputable def hp762060 := hp762058 hp762056 299121087 rfl rfl rfl rfl rfl rfl rfl rfl (hp762059 rfl)

noncomputable def hp762061 := @BSN.binarySplit_of_base2 (BSN.sinOddP 317267924) (BSN.sinOddQ 536870912) 0 2 hp762057 hp708848 hp762056 rfl rfl rfl

noncomputable def hp762062 := hp762047 hd4920 hd4922 hd4924 hd4926 hd4918 (hp762053 (hp762054 rfl) rfl rfl rfl rfl) (hp762060 (hp762061 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762063 := hp761964 (BSN.cos_quad_nat1 9 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 433682330 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl rfl (hp762062 rfl rfl rfl rfl rfl) hp762030

noncomputable def hp762064 := nat_lit 17760441471772011051403116415924199278015295330384902103370350207265288483637557273766939686613812699725824000000

noncomputable def hp762065 := nat_lit 2137494564197937076413294534180526766144024558506782052288210237978726249134295826415427588096000000000000

noncomputable def hp762066 := nat_lit 107680431829605610991799565046011581189562948956932496371522762910839061157498022470491425725175225386899865600000

noncomputable def hp762067 := BSN.cos_dyadic_bound_f 599090020 536870912 4 3 536870912 268435456 hp762064 hp716712 hp762065 hp762066 hp716714

noncomputable def hp762068 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 599090020) (BSN.cosEvenQ 536870912) 0 3 hp762064 hp716712 hp762065 rfl rfl rfl

noncomputable def hp762069 := hp762067 hp762065 235888335 rfl rfl rfl rfl rfl rfl rfl rfl (hp762068 rfl)

noncomputable def hp762070 := @BSN.binarySplit_of_base3 (BSN.cosOddP 599090020) (BSN.cosOddQ 536870912) 0 3 hp762066 hp716714 hp762065 rfl rfl rfl

noncomputable def hp762071 := nat_lit 16327169415907183993540830531397924040641275134082542610799605344559431680

noncomputable def hp762072 := nat_lit 4221576056297644267189117489873443968231914670093576342736633862291456

noncomputable def hp762073 := nat_lit 42754799251856238082841011868201434530492868917893174380872630876164325376

noncomputable def hp762074 := BSN.sin_dyadic_bound_f 504875536 536870912 3 2 536870912 268435456 hp762071 hp708845 hp762072 hp762073 hp708848

noncomputable def hp762075 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 504875536) (BSN.sinEvenQ 536870912) 0 2 hp762071 hp708845 hp762072 rfl rfl rfl

noncomputable def hp762076 := hp762074 hp762072 433682330 rfl rfl rfl rfl rfl rfl rfl rfl (hp762075 rfl)

noncomputable def hp762077 := @BSN.binarySplit_of_base2 (BSN.sinOddP 504875536) (BSN.sinOddQ 536870912) 0 2 hp762073 hp708848 hp762072 rfl rfl rfl

noncomputable def hp762078 := hp762063 hd4928 hd4930 hd4932 hd4934 hd4918 (hp762069 (hp762070 rfl) rfl rfl rfl rfl) (hp762076 (hp762077 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762079 := hp761959 (BSN.cos_quad_nat1 129 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133834572 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl rfl (hp762078 rfl rfl rfl rfl rfl) hp762030

noncomputable def hp762080 := nat_lit 137760755741060885260987606046161

noncomputable def hp762081 := BSN.cos_dyadic_bound_f 108338141 536870912 2 1 536870912 268435456 hp762080 hp708767 hp762080 hp762080 hp708768

noncomputable def hp762082 := @BSN.binarySplit_of_base (BSN.cosEvenP 108338141) (BSN.cosEvenQ 536870912) 0 1 hp762080 hp708767 hp762080 rfl rfl rfl

noncomputable def hp762083 := hp762081 hp762080 525976880 rfl rfl rfl rfl rfl rfl rfl rfl (hp762082 rfl)

noncomputable def hp762084 := @BSN.binarySplit_of_base (BSN.cosOddP 108338141) (BSN.cosOddQ 536870912) 0 1 hp762080 hp708768 hp762080 rfl rfl rfl

noncomputable def hp762085 := nat_lit 334726665643511319280030519500625

noncomputable def hp762086 := BSN.sin_dyadic_bound_f 135260995 536870912 2 1 536870912 268435456 hp762085 hp708890 hp762085 hp762085 hp708891

noncomputable def hp762087 := @BSN.binarySplit_of_base (BSN.sinEvenP 135260995) (BSN.sinEvenQ 536870912) 0 1 hp762085 hp708890 hp762085 rfl rfl rfl

noncomputable def hp762088 := hp762086 hp762085 133834572 rfl rfl rfl rfl rfl rfl rfl rfl (hp762087 rfl)

noncomputable def hp762089 := @BSN.binarySplit_of_base (BSN.sinOddP 135260995) (BSN.sinOddQ 536870912) 0 1 hp762085 hp708891 hp762085 rfl rfl rfl

noncomputable def hp762090 := hp762079 hd4936 hd4938 hd4940 hd4942 hd4918 (hp762083 (hp762084 rfl) rfl rfl rfl rfl) (hp762088 (hp762089 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762091 := hp761954 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535668450 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl rfl (hp762090 rfl rfl rfl rfl rfl) hp762030

noncomputable def hp762092 := nat_lit 1571035903419288337255005483600595150503298541745454007409078294455073505

noncomputable def hp762093 := nat_lit 39104616622560860924852897133479299951103477193673963026781244832481

noncomputable def hp762094 := nat_lit 4114554530052175784750183647596675951499194394179780261559828363462130401

noncomputable def hp762095 := BSN.sin_dyadic_bound_f 281208539 536870912 3 2 536870912 268435456 hp762092 hp708845 hp762093 hp762094 hp708848

noncomputable def hp762096 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 281208539) (BSN.sinEvenQ 536870912) 0 2 hp762092 hp708845 hp762093 rfl rfl rfl

noncomputable def hp762097 := hp762095 hp762093 268525159 rfl rfl rfl rfl rfl rfl rfl rfl (hp762096 rfl)

noncomputable def hp762098 := @BSN.binarySplit_of_base2 (BSN.sinOddP 281208539) (BSN.sinOddQ 536870912) 0 2 hp762094 hp708848 hp762093 rfl rfl rfl

noncomputable def hp762099 := nat_lit 152438667017941691649326664356720181495547606635762914294435674508638604474674760628672446677830692005063793040625

noncomputable def hp762100 := nat_lit 76720030499842931414101031365128967077681180425315243245161077538878275097240061578714628117410039306640625

noncomputable def hp762101 := nat_lit 761397439049980371231941790702613239082815545965013191159502040135026651743620363518271077518412527121417738640625

noncomputable def hp762102 := BSN.sin_dyadic_bound_f 807375805 536870912 4 3 536870912 268435456 hp762099 hp642702 hp762100 hp762101 hp642705

noncomputable def hp762103 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 807375805) (BSN.sinEvenQ 536870912) 0 3 hp762099 hp642702 hp762100 rfl rfl rfl

noncomputable def hp762104 := hp762102 hp762100 535668450 rfl rfl rfl rfl rfl rfl rfl rfl (hp762103 rfl)

noncomputable def hp762105 := @BSN.binarySplit_of_base3 (BSN.sinOddP 807375805) (BSN.sinOddQ 536870912) 0 3 hp762101 hp642705 hp762100 rfl rfl rfl

noncomputable def hp762106 := hp762091 hd4944 hd4946 hd4961 hd4963 hd4918 (hp762097 (hp762098 rfl) rfl rfl rfl rfl) (hp762104 (hp762105 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762107 := @hp761949 105223 134217728 (hp762106 rfl rfl rfl rfl rfl) (hp762106 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp762108 := @hp761947 Bool.false 276600839 268435456 105223 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 867289 1000)) (Enclosure.sfrac Bool.false 867289 1000) 11) hp762107

noncomputable def hp762109 := @Enclosure.Real.IsNear.mulLit_tf hp761937 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1))) 9789351 33554432 1

noncomputable def hp762110 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp761936 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762111 := @hp762110 1 1 0 1 9789351 33554432 1 33554432 9789351 33554432 1

noncomputable def hp762112 := @Enclosure.Real.IsNear.of_eq (hp761936 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762113 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 867289 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762114 := @hp762112 (@Inv.inv Real Real.instInv (Real.sqrt hp761938)) Bool.false 9789351 33554432 1 33554432 (hp762113 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 867289 1000) 867289 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000))))

noncomputable def hp762115 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp761938)) Bool.false 19578702 67108864 2 67108864 9789351 33554432

noncomputable def hp762116 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp761938) Bool.false 230025443 67108864 7 67108864 230025443 67108864 7 67108864

noncomputable def hp762117 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 867289 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762118 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 867289 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762119 := @hp762118 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 867289 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9263259693323

noncomputable def hp762120 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 867289 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 867289 1000 0

noncomputable def hp762121 := @hp762120 1 10680707 67108864 1 67108864 9263259693323 67108864000 867289 67108864000 (Enclosure.Real.IsNear.const Bool.false 867289 1000) hd4949

noncomputable def hp762122 := @hp762119 67108864000 867289 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 867289 1000) 867289 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000))) (hp762121 rfl)

noncomputable def hp762123 := @hp762117 9263259693323 67108864000 867289 67108864000 394222899 394222937 33554432 hp762122 rfl rfl rfl

noncomputable def hp762124 := @Enclosure.Real.IsNear.recentre' hp761938 Bool.false 788445836 67108864 38 67108864 197111459 16777216 19 33554432 (hp762123 rfl rfl rfl)

noncomputable def hp762125 := @Enclosure.Real.IsNear.sqrt_image hp761938 197111459 16777216 19 33554432 115012718 115012725 33554432 (hp762124 rfl) rfl rfl

noncomputable def hp762126 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp761938) 230025443 67108864 7 67108864 9789350 9789352 33554432 (hp762116 (hp762125 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp762127 := @hp762111 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp762114 (@hp762115 1 33554432 (hp762126 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp762128 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762129 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp762130 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1))) (hp762128 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762129 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp762131 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 867289 1000) 867289 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl

noncomputable def hp762132 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762133 := @hp762132 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762129 (Enclosure.sfrac Bool.false 1 16)))) 4301564731

noncomputable def hp762134 := @hp762133 33554432 2022763 33554432 32637 8388608 410527429 45675970560000 140390168125647 281474976710656 1063101408588583963 766315624094760960000

noncomputable def hp762135 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762136 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762137 := @hp762135 (@Neg.neg Real Real.instNeg hp762136) Bool.true 4301564731 33554432 2022763 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762138 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762139 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp762140 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp762141 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 315719581) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp762142 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1))) Bool.false 11108395225339335205065

noncomputable def hp762143 := nat_lit 102547086597530361253352129

noncomputable def hp762144 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp762145 := @Enclosure.Real.IsNear.subLit_ff_p hp761938 (Enclosure.sfrac Bool.false 11 1) 197111459 16777216 19 33554432 11 1 0

noncomputable def hp762146 := @hp762144 500000000000000 12562083 16777216 19 33554432 11108395225339335205065 2361183241434822606848 hp762143 hp682117 hd4948 (@hp762145 1 12562083 12562083 16777216 19 33554432 (hp762124 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762147 := @hp762141 315719581 67108864 15 4194304 Bool.true 523484 67108864 1 10890000 (@hp762142 2361183241434822606848 hp762143 hp682117 315719581 67108864 15 4194304 (hp762146 rfl) rfl) (Enclosure.sfrac_false_div 315719581 67108864)

noncomputable def hp762148 := nat_lit 15116367005954704662331392

noncomputable def hp762149 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 315719581) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp762148) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp762150 := BSN.sin_reduce_arg_pos_rat_q2 315719581 67108864 226375608064910080 72057594037927936 0 hp762148 hp617687 rfl rfl rfl rfl

noncomputable def hp762151 := nat_lit 5430199343169735176636509124905098141605475330776971184690665996405819603520455926437197267252374878695842012307605719757898192607600105369281

noncomputable def hp762152 := nat_lit 9656317196523849493798097543706855309107222683383426658697325774745557011333316828902484825374241460872396004446384817709621479994961601

noncomputable def hp762153 := nat_lit 32865418426892213783078757055685834713267168810789233086559830745313932743140844498716325270121246003619614207902260945274128395165319929933505

noncomputable def hp762154 := BSN.cos_dyadic_bound_f 214816495343 137438953472 4 3 67108864 21801270 hp762151 hp740177 hp762152 hp762153 hp740180

noncomputable def hp762155 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 214816495343) (BSN.cosEvenQ 137438953472) 0 3 hp762151 hp740177 hp762152 rfl rfl rfl

noncomputable def hp762156 := hp762154 hp762152 523484 rfl rfl rfl rfl rfl rfl rfl rfl (hp762155 rfl)

noncomputable def hp762157 := @BSN.binarySplit_of_base3 (BSN.cosOddP 214816495343) (BSN.cosOddQ 137438953472) 0 3 hp762153 hp740180 hp762152 rfl rfl rfl

noncomputable def hp762158 := @BSN.cos_arg_round Bool.false 523484 67108864 hp762148 hp617687 214816495343 137438953472 21801270 21780000 (hp762156 (hp762157 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762159 := hp762149 523484 67108864 0 1000000000000000 21780000 10890000 hp762150 BSN.pi_near_15 hp762158 rfl rfl

noncomputable def hp762160 := @hp762139 130871 16777216 10471519 2854748160000 (@hp762140 523484 67108864 167544304 45675970560000 130871 16777216 10471519 2854748160000 (hp762147 (hp762159 rfl rfl) rfl rfl) rfl)

noncomputable def hp762161 := @hp762138 130871 16777216 10471519 2854748160000 4299541968 4303587494 33554432 hp762160 rfl rfl rfl

noncomputable def hp762162 := @Enclosure.Real.IsNear.recentre' hp762136 Bool.false 8603129462 67108864 4045526 67108864 4301564731 33554432 2022763 33554432 (hp762161 rfl rfl rfl)

noncomputable def hp762163 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762129 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp762164 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762129 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 26418863)) (@Nat.cast Real Real.instNatCast 16777216)) Bool.true

noncomputable def hp762165 := nat_lit 62379776623384710241423147525

noncomputable def hp762166 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762129 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp762165

noncomputable def hp762167 := nat_lit 42968656211413173478567992141553499

noncomputable def hp762168 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762129 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp762169 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp762170 := @hp762169 (Enclosure.sfrac Bool.false 1 16) 52950850602039 281474976710656 1592252877 1125899906842624 1 16 0

noncomputable def hp762171 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)) 157805929298889

noncomputable def hp762172 := @hp762171 281474976710656 954718669 1125899906842624 12562083 16777216 19 33554432 888367857934138343424 52950850602039 281474976710656 1592252877

noncomputable def hp762173 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)) 12562083 16777216 19

noncomputable def hp762174 := @hp762173 33554432 12562083 16777216 19 33554432 157805929298889 281474976710656 954718669 1125899906842624 (@hp762145 1 12562083 12562083 16777216 19 33554432 (hp762124 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762175 := hp762174 (@hp762145 1 12562083 12562083 16777216 19 33554432 (hp762124 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762176 := @hp762172 1125899906842624 (hp762175 rfl) (@hp762145 1 12562083 12562083 16777216 19 33554432 (hp762124 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762177 := @hp762168 500000000000000 70543036646455 281474976710656 1592252877 1125899906842624 hp762165 hp631146 hp762167 hp682143 hd4948 (@hp762170 1 1128688586343280 70543036646455 281474976710656 1592252877 1125899906842624 (hp762176 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp762178 := @hp762164 26418863 16777216 597 67108864 Bool.true 130548 33554432 1 10890000 (@hp762166 hp631146 hp762167 hp682143 26418863 16777216 597 67108864 (hp762177 rfl) rfl) (Enclosure.sfrac_true_div 26418863 16777216)

noncomputable def hp762179 := nat_lit 61253197942765636576925810386762240092325952305223748804917001835505308675719466096832029786561

noncomputable def hp762180 := nat_lit 115603098112176533993805396489544009784308472088875564880016149579792190402087216825106881

noncomputable def hp762181 := nat_lit 370698773852797935678506710566280328162219156148191038602207812021010112553692006384956429173185

noncomputable def hp762182 := BSN.cos_dyadic_bound_t 26418863 16777216 4 3 33554432 10890000 hp762179 hp633087 hp762180 hp762181 hp633090

noncomputable def hp762183 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 26418863) (BSN.cosEvenQ 16777216) 0 3 hp762179 hp633087 hp762180 rfl rfl rfl

noncomputable def hp762184 := hp762182 hp762180 130548 rfl rfl rfl rfl rfl rfl rfl rfl (hp762183 rfl)

noncomputable def hp762185 := @BSN.binarySplit_of_base3 (BSN.cosOddP 26418863) (BSN.cosOddQ 16777216) 0 3 hp762181 hp633090 hp762180 rfl rfl rfl

noncomputable def hp762186 := hp762178 (BSN.cos_neg_of_bound 26418863 16777216 Bool.true 130548 33554432 1 10890000 (hp762184 (hp762185 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp762187 := hp762134 (hp762137 (@Enclosure.Real.IsNear.neg hp762136 Bool.false 4301564731 33554432 2022763 33554432 (hp762162 rfl))) (@hp762163 130548 33554432 6568438864 730815528960000 32637 8388608 410527429 45675970560000 (hp762186 rfl) rfl)

noncomputable def hp762188 := @hp762109 33554432 140390168125647 281474976710656 1063101408588583963 766315624094760960000 1374328632730970585097 9444732965739290427392 hp761943 hp752398 (hp762127 rfl) (@hp762130 Bool.false 140390168125647 281474976710656 1063101408588583963 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp761938 (Enclosure.sfrac Bool.false 11 1)) (hp762131 rfl (hp761941 rfl rfl))) (hp762187 rfl))

noncomputable def hp762189 := @hp761935 hp761933 hp752398 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 867289 1000))) (@hp761940 hp761933 hp752398 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 867289 1000) 11 (hp761941 rfl rfl)) (@hp761945 hp761933 hp752398 hp762108 (hp762188 rfl) rfl rfl))

theorem hd5057 : hp761934 hp752398 := hp762189

noncomputable def hp762190 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 868564 1000)) Bool.true 10885507039153897382031 18889465931478580854784 609813783743004399890237

noncomputable def hp762191 := nat_lit 714257930534033838571520000

noncomputable def hp762192 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 868564 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 868564 1000)) Bool.true 10885507039153897382031 18889465931478580854784

noncomputable def hp762193 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 868564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762194 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp762193 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762195 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 868564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762196 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp762194 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp762197 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 868564 1000)) hp762196 Bool.true 10885507039153897382031 18889465931478580854784

noncomputable def hp762198 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 868564 1000) 868564 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl

noncomputable def hp762199 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp762194 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp762200 := nat_lit 2922056045846486297922697691136

noncomputable def hp762201 := @hp762199 194424609 268435456 105379 134217728 2795908533409452351345 18889465931478580854784 49025074357714016530237 hp762191 hp762200 10885507039153897382031 18889465931478580854784

noncomputable def hp762202 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) 11)

noncomputable def hp762203 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) 11) hp762202

noncomputable def hp762204 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) 11)

noncomputable def hp762205 := @hp762204 194424609 536870912 210758 536870912 194424609 536870912 210758 536870912 208761834298146816 194424609 268435456

noncomputable def hp762206 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp762207 := hp762206 BSN.quadSignPos 9 10 11 868564 1000 187 239 536870912 268435456 9007199254740992

noncomputable def hp762208 := hp762207 Bool.false 915840443588 3957 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp762209 := hp762208 Bool.true 407503341 180930 Bool.true 170639747 Bool.true 762047824 28296951008113761 1 Bool.false 167781132

noncomputable def hp762210 := hp762209 Bool.false Bool.false 530731885 Bool.false Bool.true 194424609 210758 BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 167781132 536870912) BSN.abs_quadSignPos

noncomputable def hp762211 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp762212 := hp762211 BSN.quadSignPos 7 8 9 868564 1000 63 128 536870912 268435456 9007199254740992

noncomputable def hp762213 := hp762212 Bool.false 915840443588 3957 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp762214 := hp762213 Bool.true 605251288 147766 Bool.true 688340123 Bool.true 795886674 28296951008113761 1 Bool.false 514658068

noncomputable def hp762215 := hp762214 Bool.false Bool.false 47366516 Bool.false Bool.true 407503341 180930 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 514658068 536870912) BSN.abs_quadSignPos

noncomputable def hp762216 := hp762211 BSN.quadSignNeg 5 6 7 868564 1000 95 10 536870912 268435456 9007199254740992

noncomputable def hp762217 := hp762216 Bool.false 915840443588 3957 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp762218 := hp762217 Bool.true 488251756 109808 Bool.false 216009420 Bool.false 16277201 28296951008113761 1 Bool.false 210228311

noncomputable def hp762219 := hp762218 Bool.false Bool.false 536624179 Bool.true Bool.true 605251288 147766 BSN.abs_quadSignPos (BSN.cos_quad_nat3 95 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 210228311 536870912) BSN.abs_quadSignNeg

noncomputable def hp762220 := hp762211 BSN.quadSignPos 3 4 5 868564 1000 319 196 536870912 268435456 9007199254740992

noncomputable def hp762221 := hp762220 Bool.false 915840443588 3957 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp762222 := hp762221 Bool.true 903170141 64904 Bool.false 384602819 Bool.false 58988339 28296951008113761 1 Bool.false 352540443

noncomputable def hp762223 := hp762222 Bool.false Bool.false 533633518 Bool.false Bool.true 488251756 109808 BSN.abs_quadSignPos (BSN.cos_quad_nat3 319 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 352540443 536870912) BSN.abs_quadSignPos

noncomputable def hp762224 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp762225 := hp762224 BSN.quadSignNeg 1 2 3 868564 1000 702 478 536870912 268435456 9007199254740992

noncomputable def hp762226 := hp762225 Bool.false 915840443588 3957 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp762227 := hp762226 Bool.true 536870664 4018 Bool.false 614220483 Bool.false 445624478 28296951008113761 1 Bool.false 222204720

noncomputable def hp762228 := hp762227 Bool.true Bool.false 362305209 Bool.true Bool.true 903170141 64904 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 702 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 222204720 536870912) BSN.abs_quadSignNeg

noncomputable def hp762229 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) 1) Bool.true

noncomputable def hp762230 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)))

noncomputable def hp762231 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000))) Bool.true 67108833 67108864

noncomputable def hp762232 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14310006931) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 14310006931 8388608

noncomputable def hp762233 := nat_lit 905969701837886708787689731106512797511268638566468347

noncomputable def hp762234 := nat_lit 531084626667291876809746560832467649472420118528000

noncomputable def hp762235 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) Bool.false hp762233 hp762234 3652132757262914427

noncomputable def hp762236 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 868564 4000) (Real.log (Enclosure.sfrac Bool.false 3017614688384 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1737128))))))

noncomputable def hp762237 := nat_lit 237274313961488455426751402475520000

noncomputable def hp762238 := nat_lit 1236527754616206225030465425999061319680

noncomputable def hp762239 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp762236 (Enclosure.sfrac Bool.false 868564 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 868564 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp762237 hp762238)) Bool.false

noncomputable def hp762240 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 868564 1000) 868564 1000 3017614688384 16000000 1737128

noncomputable def hp762241 := hp762240 4000 2000 hp762237 hp762238 (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl rfl rfl rfl

noncomputable def hp762242 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp762236 (Enclosure.sfrac Bool.false 868564 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 868564 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp762237 hp762238) 7682627335995944081379 4503599627370496000

noncomputable def hp762243 := nat_lit 9499780860743638935537605474847427631631760239534731134238720

noncomputable def hp762244 := @hp762242 3652132757262914427 495616000000000000000000 hp762237 hp762238 0 1 hp762243 hp762233 hp762234 3652132757262914427 495616000000000000000000

noncomputable def hp762245 := @Enclosure.Real.IsNear.subLit_ff_p (hp762236 (Enclosure.sfrac Bool.false 868564 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 868564 2000) (Real.log Real.pi)) 1984305392309702755527 900719925474099200 152181473337081 60500000000000000000

noncomputable def hp762246 := nat_lit 25778619652701705795443412172800

noncomputable def hp762247 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 868564 4000) (Real.log (Enclosure.sfrac Bool.false 3017614688384 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1737128))))))

noncomputable def hp762248 := @hp762247 (Enclosure.sfrac Bool.false 868564 2000) 11877359214922227521507 4503599627370496000 152181473337081 60500000000000000000 868564 2000 0

noncomputable def hp762249 := nat_lit 19843053923097027555270000

noncomputable def hp762250 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 868564 4000) (Real.log (Enclosure.sfrac Bool.false 3017614688384 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1737128))))) 11879127126222826119507

noncomputable def hp762251 := nat_lit 26745435267234635389779942642848628736

noncomputable def hp762252 := @hp762250 4503599627370496000 2714266519931333 1089000000000000000000 883955650299299 2251799813685248 200000001089 8712000000000000000 hp762251 11877359214922227521507 4503599627370496000 152181473337081

noncomputable def hp762253 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 868564 4000) (Real.log (Enclosure.sfrac Bool.false 3017614688384 16000000)) 868564 4000 0 1 54706974390938727 4503599627370496

noncomputable def hp762254 := nat_lit 117482332936095675602436096

noncomputable def hp762255 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3017614688384) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp762254 hp617687

noncomputable def hp762256 := BSN.log_rat_reduce_isNear 3017614688384 16000000 17 6035229376768 4194304000000 97680024 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp762257 := nat_lit 127374582623884853600963642815571339021507243802540418142230509809323853146029043079854372474474056575490087638323828740291318251520

noncomputable def hp762258 := nat_lit 1402415830138132375078926766856524678292554940606101329807786619161338195123540777266571079340664557742605280542834179392724271104

noncomputable def hp762259 := nat_lit 412566248555711920577199023369884296177253859494136307423416079953369088946665436409712089150034743072587931347818192568320

noncomputable def hp762260 := BSN.log_dyadic_bound 920462688384 5114766688384 6 5 hp762257 268435456 87120000 hp762258 hp762259 97680024 6035229376768

noncomputable def hp762261 := hp762260 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp762262 := @BSN.binarySplit_of_base5 (BSN.artanhP 920462688384) (BSN.artanhQ 5114766688384) 0 5 hp762258 hp762257 hp762259 rfl rfl rfl

noncomputable def hp762263 := hp762256 rfl rfl rfl rfl (hp762261 (hp762262 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp762264 := @hp762253 12500018513 1089000000000000000 11879127126222826119507 4503599627370496000 2714266519931333 1089000000000000000000 (Enclosure.Real.IsNear.const Bool.false 868564 4000) (BSN.isNear_log_sfrac 3017614688384 16000000 54706974390938727 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp762255 1000001481040000 87120000000000000000000 54706974390938727 4503599627370496 12500018513 1089000000000000000 (hp762263 rfl rfl rfl) rfl)) rfl

noncomputable def hp762265 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1737128)))) 1 4

noncomputable def hp762266 := @hp762265 0 1 883955650299299 562949953421312 200000001089 2178000000000000000 883955650299299 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp762267 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1737128))) 884279719003555 562949953421312 1

noncomputable def hp762268 := @hp762267 2000000000000000 19316 33554432 1 10890000 29660629758983607943168 883955650299299 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp762269 := BSN.arctan_dyadic_bound_f 1000 1737128 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp762270 := hp762269 1 19316 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1737128) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1737128) 0 0 rfl)

noncomputable def hp762271 := hp762266 (hp762268 (hp762270 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp762272 := @hp762245 8340551054301 16777216000 651423 134217728000 hp762246 7682627335995944081379 4503599627370496000 3652132757262914427 495616000000000000000000 (@hp762248 1 hp762249 1984305392309702755527 900719925474099200 152181473337081 60500000000000000000 (@hp762252 60500000000000000000 hp762264 hp762271 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 868564 2000) rfl rfl)

noncomputable def hp762273 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 868564 2000) (Real.log Real.pi) 868564 2000 0 1 38410761 33554432

noncomputable def hp762274 := hp762272 (@hp762273 3 268435456 8340551054301 16777216000 651423 134217728000 (Enclosure.Real.IsNear.const Bool.false 868564 2000) hd4909 rfl) rfl

noncomputable def hp762275 := @hp762235 495616000000000000000000 14310006931 8388608 31 4194304 (@hp762239 hp762233 hp762234 3652132757262914427 495616000000000000000000 (hp762241 rfl rfl rfl rfl rfl) (hp762244 (hp762274 rfl) (Enclosure.Real.IsNear.const Bool.true hp762237 hp762238) rfl rfl)) rfl

noncomputable def hp762276 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14310006931) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1147043334313100705792) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp762277 := BSN.sin_reduce_arg_pos_rat_q2 14310006931 8388608 226375608064910080 72057594037927936 271 1147043334313100705792 hp630689 rfl rfl rfl rfl

noncomputable def hp762278 := BSN.cos_dyadic_bound_f 130403729 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp762279 := hp762278 1 67108833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 130403729) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp762280 := hp762279 (@BSN.binarySplit_of_le (BSN.cosOddP 130403729) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp762281 := @BSN.cos_arg_round Bool.false 67108833 67108864 1147043334313100705792 hp630689 130403729 137438953472 21801270 21780000 hp762280 rfl

noncomputable def hp762282 := hp762276 67108833 67108864 271 1000000000000000 21780000 10890000 hp762277 BSN.pi_near_15 hp762281 rfl rfl

noncomputable def hp762283 := @hp762232 31 4194304 Bool.true 67108833 67108864 1 10890000 hp762275 (Enclosure.sfrac_false_div 14310006931 8388608) (hp762282 rfl rfl) rfl

noncomputable def hp762284 := @hp762229 67108833 67108864 21361519 2854748160000 536870664 536870912 4018 536870912 (@hp762230 Bool.true 67108833 67108864 21361519 2854748160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000)) (@hp762231 341784304 45675970560000 67108833 67108864 21361519 2854748160000 (hp762283 rfl) rfl))

noncomputable def hp762285 := @hp762235 495616000000000000000000 915840443588 536870912 3957 536870912 (@hp762239 hp762233 hp762234 3652132757262914427 495616000000000000000000 (hp762241 rfl rfl rfl rfl rfl) (hp762244 (hp762274 rfl) (Enclosure.Real.IsNear.const Bool.true hp762237 hp762238) rfl rfl)) rfl

noncomputable def hp762286 := hp762228 (BSN.cos_quad_nat2 478 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 362305209 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl rfl (hp762284 rfl) hp762285

noncomputable def hp762287 := nat_lit 19625675875806007814199438682252485693933082109941486530501116618097785934017579276881635908029608055513933453041

noncomputable def hp762288 := nat_lit 2883311354321353632663730434563863892165350234748040532377770351104497274565344235540481577771400784811761

noncomputable def hp762289 := nat_lit 118981556163680241987317025135775258239721695679871384223162831103143321345264841909061463187524876916078855100145

noncomputable def hp762290 := BSN.cos_dyadic_bound_f 614220483 536870912 4 3 536870912 268435456 hp762287 hp716712 hp762288 hp762289 hp716714

noncomputable def hp762291 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 614220483) (BSN.cosEvenQ 536870912) 0 3 hp762287 hp716712 hp762288 rfl rfl rfl

noncomputable def hp762292 := hp762290 hp762288 222204720 rfl rfl rfl rfl rfl rfl rfl rfl (hp762291 rfl)

noncomputable def hp762293 := @BSN.binarySplit_of_base3 (BSN.cosOddP 614220483) (BSN.cosOddQ 536870912) 0 3 hp762289 hp716714 hp762288 rfl rfl rfl

noncomputable def hp762294 := nat_lit 5505384083529327924461780094522407628284258930543580424099117865992028416

noncomputable def hp762295 := nat_lit 1555078466858042787204752518988954198783051992297910396991084915425536

noncomputable def hp762296 := nat_lit 16513042093654267687810930778529244976455210687646145451503371428145234176

noncomputable def hp762297 := BSN.cos_dyadic_bound_f 445624478 536870912 3 2 536870912 268435456 hp762294 hp708868 hp762295 hp762296 hp708870

noncomputable def hp762298 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 445624478) (BSN.cosEvenQ 536870912) 0 2 hp762294 hp708868 hp762295 rfl rfl rfl

noncomputable def hp762299 := hp762297 hp762295 362305209 rfl rfl rfl rfl rfl rfl rfl rfl (hp762298 rfl)

noncomputable def hp762300 := @BSN.binarySplit_of_base2 (BSN.cosOddP 445624478) (BSN.cosOddQ 536870912) 0 2 hp762296 hp708870 hp762295 rfl rfl rfl

noncomputable def hp762301 := hp762286 hd4911 hd4913 hd4915 hd4917 hd4918 (hp762292 (hp762293 rfl) rfl rfl rfl rfl) (hp762299 (hp762300 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762302 := hp762223 (BSN.cos_quad_nat0 196 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 533633518 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl rfl (hp762301 rfl rfl rfl rfl rfl) hp762285

noncomputable def hp762303 := nat_lit 5497293939146279033846276295676264863105305011857400312778779377091169185

noncomputable def hp762304 := nat_lit 478739988571027297735780231854539501906615763139032101121363630836641

noncomputable def hp762305 := nat_lit 14396899499687330092067722844491024434653664319819537624352130446503136161

noncomputable def hp762306 := BSN.sin_dyadic_bound_f 384602819 536870912 3 2 536870912 268435456 hp762303 hp708845 hp762304 hp762305 hp708848

noncomputable def hp762307 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 384602819) (BSN.sinEvenQ 536870912) 0 2 hp762303 hp708845 hp762304 rfl rfl rfl

noncomputable def hp762308 := hp762306 hp762304 352540443 rfl rfl rfl rfl rfl rfl rfl rfl (hp762307 rfl)

noncomputable def hp762309 := @BSN.binarySplit_of_base2 (BSN.sinOddP 384602819) (BSN.sinOddQ 536870912) 0 2 hp762305 hp708848 hp762304 rfl rfl rfl

noncomputable def hp762310 := nat_lit 12107784141605549049590640324241

noncomputable def hp762311 := BSN.cos_dyadic_bound_f 58988339 536870912 2 1 536870912 268435456 hp762310 hp708767 hp762310 hp762310 hp708768

noncomputable def hp762312 := @BSN.binarySplit_of_base (BSN.cosEvenP 58988339) (BSN.cosEvenQ 536870912) 0 1 hp762310 hp708767 hp762310 rfl rfl rfl

noncomputable def hp762313 := hp762311 hp762310 533633518 rfl rfl rfl rfl rfl rfl rfl rfl (hp762312 rfl)

noncomputable def hp762314 := @BSN.binarySplit_of_base (BSN.cosOddP 58988339) (BSN.cosOddQ 536870912) 0 1 hp762310 hp708768 hp762310 rfl rfl rfl

noncomputable def hp762315 := hp762302 hd4920 hd4922 hd4924 hd4926 hd4918 (hp762308 (hp762309 rfl) rfl rfl rfl rfl) (hp762313 (hp762314 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762316 := hp762219 (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536624179 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl rfl (hp762315 rfl rfl rfl rfl rfl) hp762285

noncomputable def hp762317 := nat_lit 2177162088426515093185380684960000

noncomputable def hp762318 := BSN.sin_dyadic_bound_f 216009420 536870912 2 1 536870912 268435456 hp762317 hp708890 hp762317 hp762317 hp708891

noncomputable def hp762319 := @BSN.binarySplit_of_base (BSN.sinEvenP 216009420) (BSN.sinEvenQ 536870912) 0 1 hp762317 hp708890 hp762317 rfl rfl rfl

noncomputable def hp762320 := hp762318 hp762317 210228311 rfl rfl rfl rfl rfl rfl rfl rfl (hp762319 rfl)

noncomputable def hp762321 := @BSN.binarySplit_of_base (BSN.sinOddP 216009420) (BSN.sinOddQ 536870912) 0 1 hp762317 hp708891 hp762317 rfl rfl rfl

noncomputable def hp762322 := nat_lit 70197057149232922203696148801

noncomputable def hp762323 := BSN.cos_dyadic_bound_f 16277201 536870912 2 1 536870912 268435456 hp762322 hp708767 hp762322 hp762322 hp708768

noncomputable def hp762324 := @BSN.binarySplit_of_base (BSN.cosEvenP 16277201) (BSN.cosEvenQ 536870912) 0 1 hp762322 hp708767 hp762322 rfl rfl rfl

noncomputable def hp762325 := hp762323 hp762322 536624179 rfl rfl rfl rfl rfl rfl rfl rfl (hp762324 rfl)

noncomputable def hp762326 := @BSN.binarySplit_of_base (BSN.cosOddP 16277201) (BSN.cosOddQ 536870912) 0 1 hp762322 hp708768 hp762322 rfl rfl rfl

noncomputable def hp762327 := hp762316 hd4928 hd4930 hd4932 hd4934 hd4918 (hp762320 (hp762321 rfl) rfl rfl rfl rfl) (hp762325 (hp762326 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762328 := hp762215 (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 47366516 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl rfl (hp762327 rfl rfl rfl rfl rfl) hp762285

noncomputable def hp762329 := nat_lit 80474518181019073018402431846394512484407317489300851858948875492083207313274517725931890187552185719075095693521

noncomputable def hp762330 := nat_lit 11314543101850172700246217740656662515897709980809482537095769882346123192582215277437573012586533943232721

noncomputable def hp762331 := nat_lit 402150466544644151070429672570947452770606268385128929776184683000334446297673176459831220648811706698926963280081

noncomputable def hp762332 := BSN.sin_dyadic_bound_f 688340123 536870912 4 3 536870912 268435456 hp762329 hp642702 hp762330 hp762331 hp642705

noncomputable def hp762333 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 688340123) (BSN.sinEvenQ 536870912) 0 3 hp762329 hp642702 hp762330 rfl rfl rfl

noncomputable def hp762334 := hp762332 hp762330 514658068 rfl rfl rfl rfl rfl rfl rfl rfl (hp762333 rfl)

noncomputable def hp762335 := @BSN.binarySplit_of_base3 (BSN.sinOddP 688340123) (BSN.sinOddQ 536870912) 0 3 hp762331 hp642705 hp762330 rfl rfl rfl

noncomputable def hp762336 := nat_lit 55428981430457292862138102761171473233175149686737258921215780016143415230314068661542764858306437616050366713856

noncomputable def hp762337 := nat_lit 64597364164084037497091829419902180818295793084713593630518110712106959280316662467532139601038005412171776

noncomputable def hp762338 := nat_lit 335626191271496419719575375370362531836993905905167946818893255703643501062845053912022812730146465184218127667200

noncomputable def hp762339 := BSN.cos_dyadic_bound_f 795886674 536870912 4 3 536870912 268435456 hp762336 hp716712 hp762337 hp762338 hp716714

noncomputable def hp762340 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 795886674) (BSN.cosEvenQ 536870912) 0 3 hp762336 hp716712 hp762337 rfl rfl rfl

noncomputable def hp762341 := hp762339 hp762337 47366516 rfl rfl rfl rfl rfl rfl rfl rfl (hp762340 rfl)

noncomputable def hp762342 := @BSN.binarySplit_of_base3 (BSN.cosOddP 795886674) (BSN.cosOddQ 536870912) 0 3 hp762338 hp716714 hp762337 rfl rfl rfl

noncomputable def hp762343 := hp762328 hd4936 hd4938 hd4940 hd4942 hd4918 (hp762334 (hp762335 rfl) rfl rfl rfl rfl) (hp762341 (hp762342 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762344 := hp762210 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 530731885 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl rfl (hp762343 rfl rfl rfl rfl rfl) hp762285

noncomputable def hp762345 := nat_lit 847853454755350995277356788032081

noncomputable def hp762346 := BSN.sin_dyadic_bound_f 170639747 536870912 2 1 536870912 268435456 hp762345 hp708890 hp762345 hp762345 hp708891

noncomputable def hp762347 := @BSN.binarySplit_of_base (BSN.sinEvenP 170639747) (BSN.sinEvenQ 536870912) 0 1 hp762345 hp708890 hp762345 rfl rfl rfl

noncomputable def hp762348 := hp762346 hp762345 167781132 rfl rfl rfl rfl rfl rfl rfl rfl (hp762347 rfl)

noncomputable def hp762349 := @BSN.binarySplit_of_base (BSN.sinOddP 170639747) (BSN.sinOddQ 536870912) 0 1 hp762345 hp708891 hp762345 rfl rfl rfl

noncomputable def hp762350 := nat_lit 120939925877696736414915662430673141681540238859188865950305765378070868747871368717032793447618474869950435557376

noncomputable def hp762351 := nat_lit 38351886170270872646636055991365760500813811740912798813181114462827903719501188702843251686796158593662976

noncomputable def hp762352 := nat_lit 604198357025379683415990313693692669888882412737823449045660957040589125871795269675010126907192753433228959809536

noncomputable def hp762353 := BSN.sin_dyadic_bound_f 762047824 536870912 4 3 536870912 268435456 hp762350 hp642702 hp762351 hp762352 hp642705

noncomputable def hp762354 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 762047824) (BSN.sinEvenQ 536870912) 0 3 hp762350 hp642702 hp762351 rfl rfl rfl

noncomputable def hp762355 := hp762353 hp762351 530731885 rfl rfl rfl rfl rfl rfl rfl rfl (hp762354 rfl)

noncomputable def hp762356 := @BSN.binarySplit_of_base3 (BSN.sinOddP 762047824) (BSN.sinOddQ 536870912) 0 3 hp762352 hp642705 hp762351 rfl rfl rfl

noncomputable def hp762357 := hp762344 hd4944 hd4946 hd4961 hd4963 hd4918 (hp762348 (hp762349 rfl) rfl rfl rfl rfl) (hp762355 (hp762356 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762358 := @hp762205 105379 134217728 (hp762357 rfl rfl rfl rfl rfl) (hp762357 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp762359 := @hp762203 Bool.true 194424609 268435456 105379 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 868564 1000)) (Enclosure.sfrac Bool.false 868564 1000) 11) hp762358

noncomputable def hp762360 := @Enclosure.Real.IsNear.mulLit_tf hp762194 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1))) 19571513 67108864 1

noncomputable def hp762361 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp762193 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762362 := @hp762361 1 1 0 1 19571513 67108864 1 67108864 19571513 67108864 1

noncomputable def hp762363 := @Enclosure.Real.IsNear.of_eq (hp762193 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762364 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 868564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762365 := @hp762363 (@Inv.inv Real Real.instInv (Real.sqrt hp762195)) Bool.false 19571513 67108864 1 67108864 (hp762364 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 868564 1000) 868564 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000))))

noncomputable def hp762366 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp762195)) Bool.false 19571513 67108864 1 67108864 19571513 67108864

noncomputable def hp762367 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp762195) Bool.false 230109936 67108864 6 67108864 14381871 4194304 3 33554432

noncomputable def hp762368 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 868564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762369 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 868564 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762370 := @hp762369 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 868564 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2319219398687

noncomputable def hp762371 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 868564 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 868564 1000 0

noncomputable def hp762372 := @hp762371 1 10680707 67108864 1 67108864 2319219398687 16777216000 217141 16777216000 (Enclosure.Real.IsNear.const Bool.false 868564 1000) hd4949

noncomputable def hp762373 := @hp762370 16777216000 217141 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 868564 1000) 868564 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000))) (hp762372 rfl)

noncomputable def hp762374 := @hp762368 2319219398687 16777216000 217141 16777216000 394512565 394512603 33554432 hp762373 rfl rfl rfl

noncomputable def hp762375 := @Enclosure.Real.IsNear.recentre' hp762195 Bool.false 789025168 67108864 38 67108864 49314073 4194304 19 33554432 (hp762374 rfl rfl rfl)

noncomputable def hp762376 := @Enclosure.Real.IsNear.sqrt_image hp762195 49314073 4194304 19 33554432 115054965 115054971 33554432 (hp762375 rfl) rfl rfl

noncomputable def hp762377 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp762195) 14381871 4194304 3 33554432 9785756 9785757 33554432 (hp762367 (hp762376 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp762378 := @hp762362 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp762365 (@hp762366 1 67108864 (hp762377 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp762379 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762380 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp762381 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1))) (hp762379 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762380 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp762382 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 868564 1000) 868564 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl

noncomputable def hp762383 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762384 := @hp762383 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762380 (Enclosure.sfrac Bool.false 1 16)))) 1445574655

noncomputable def hp762385 := @hp762384 67108864 114221 67108864 98823 4194304 206965277 22837985280000 142856024131065 281474976710656 30055726469174471 127719270682460160000

noncomputable def hp762386 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762387 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)))) 3115439

noncomputable def hp762388 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp762389 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 319359631) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp762390 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1))) Bool.false 2809117027470444271595

noncomputable def hp762391 := nat_lit 512735432990140018260286917

noncomputable def hp762392 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp762393 := @Enclosure.Real.IsNear.subLit_ff_p hp762195 (Enclosure.sfrac Bool.false 11 1) 49314073 4194304 19 33554432 11 1 0

noncomputable def hp762394 := @hp762392 500000000000000 3176729 4194304 19 33554432 2809117027470444271595 590295810358705651712 hp762391 hp682805 hd4948 (@hp762393 1 3176729 3176729 4194304 19 33554432 (hp762375 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762395 := @hp762389 319359631 67108864 15 4194304 Bool.false 3115439 67108864 1 10890000 (@hp762390 590295810358705651712 hp762391 hp682805 319359631 67108864 15 4194304 (hp762394 rfl) rfl) (Enclosure.sfrac_false_div 319359631 67108864)

noncomputable def hp762396 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 319359631) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 449143601764870098255872) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp762397 := BSN.sin_reduce_arg_pos_rat_q3 319359631 67108864 226375608064910080 72057594037927936 0 449143601764870098255872 hp617687 rfl rfl rfl rfl

noncomputable def hp762398 := BSN.sin_dyadic_bound_f 6382714470 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp762399 := hp762398 1 3115439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 6382714470) (BSN.sinEvenQ 137438953472) 0 0 rfl)

noncomputable def hp762400 := hp762399 (@BSN.binarySplit_of_le (BSN.sinOddP 6382714470) (BSN.sinOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp762401 := @BSN.sin_arg_round Bool.false 3115439 67108864 449143601764870098255872 hp617687 6382714470 137438953472 21801270 21780000 hp762400 rfl

noncomputable def hp762402 := hp762396 3115439 67108864 0 1000000000000000 21780000 10890000 hp762397 BSN.pi_near_15 hp762401 rfl rfl

noncomputable def hp762403 := @hp762387 67108864 10471519 2854748160000 722730217 722844438 33554432 (@hp762388 3115439 67108864 167544304 45675970560000 3115439 67108864 10471519 2854748160000 (hp762395 (hp762402 rfl rfl) rfl rfl) rfl)

noncomputable def hp762404 := @hp762386 Bool.false 1445574655 67108864 114221 67108864 1445574655 67108864 114221 67108864 (hp762403 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp762405 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762380 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp762406 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762380 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 103833041)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp762407 := nat_lit 3830763092479139968449025805

noncomputable def hp762408 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762380 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp762407

noncomputable def hp762409 := nat_lit 43265700255109488559844992140118383

noncomputable def hp762410 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762380 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp762411 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp762412 := @hp762411 (Enclosure.sfrac Bool.false 1 16) 3232560012175 17592186044416 1603260185 1125899906842624 1 16 0

noncomputable def hp762413 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)) 10091607139441

noncomputable def hp762414 := @hp762413 17592186044416 965725977 1125899906842624 3176729 4194304 19 33554432 13558339389305651200 3232560012175 17592186044416 1603260185

noncomputable def hp762415 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)) 3176729 4194304 19

noncomputable def hp762416 := @hp762415 33554432 3176729 4194304 19 33554432 10091607139441 17592186044416 965725977 1125899906842624 (@hp762393 1 3176729 3176729 4194304 19 33554432 (hp762375 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762417 := hp762416 (@hp762393 1 3176729 3176729 4194304 19 33554432 (hp762375 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762418 := @hp762414 1125899906842624 (hp762417 rfl) (@hp762393 1 3176729 3176729 4194304 19 33554432 (hp762375 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762419 := @hp762410 500000000000000 4332071639951 17592186044416 1603260185 1125899906842624 hp762407 hp630709 hp762409 hp682143 hd4948 (@hp762412 1 69313146239216 4332071639951 17592186044416 1603260185 1125899906842624 (hp762418 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp762420 := @hp762406 103833041 67108864 301 33554432 Bool.false 790584 33554432 1 10890000 (@hp762408 hp630709 hp762409 hp682143 103833041 67108864 301 33554432 (hp762419 rfl) rfl) (Enclosure.sfrac_true_div 103833041 67108864)

noncomputable def hp762421 := nat_lit 957605854568478279370320739122491614354756003482297240786543986595907656030632992103850254446850996161

noncomputable def hp762422 := nat_lit 1570460012280787082236344853822461521891563143803569657492963333603892274007858826698115132422081

noncomputable def hp762423 := nat_lit 5796300784560984244051291820594623694159995613097918554672851451010844564375657096072785963494051411905

noncomputable def hp762424 := BSN.cos_dyadic_bound_f 103833041 67108864 4 3 33554432 10890000 hp762421 hp745658 hp762422 hp762423 hp745661

noncomputable def hp762425 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 103833041) (BSN.cosEvenQ 67108864) 0 3 hp762421 hp745658 hp762422 rfl rfl rfl

noncomputable def hp762426 := hp762424 hp762422 790584 rfl rfl rfl rfl rfl rfl rfl rfl (hp762425 rfl)

noncomputable def hp762427 := @BSN.binarySplit_of_base3 (BSN.cosOddP 103833041) (BSN.cosOddQ 67108864) 0 3 hp762423 hp745661 hp762422 rfl rfl rfl

noncomputable def hp762428 := hp762420 (BSN.cos_neg_of_bound 103833041 67108864 Bool.false 790584 33554432 1 10890000 (hp762426 (hp762427 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp762429 := hp762385 hp762404 (@hp762405 790584 33554432 3311444432 365407764480000 98823 4194304 206965277 22837985280000 (hp762428 rfl) rfl)

noncomputable def hp762430 := @hp762360 67108864 142856024131065 281474976710656 30055726469174471 127719270682460160000 2795908533409452351345 18889465931478580854784 49025074357714016530237 hp762191 (hp762378 rfl) (@hp762381 Bool.false 142856024131065 281474976710656 30055726469174471 127719270682460160000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762195 (Enclosure.sfrac Bool.false 11 1)) (hp762382 rfl (hp762198 rfl rfl))) (hp762429 rfl))

noncomputable def hp762431 := @hp762192 609813783743004399890237 hp762191 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 868564 1000))) (@hp762197 609813783743004399890237 hp762191 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 868564 1000) 11 (hp762198 rfl rfl)) (@hp762201 609813783743004399890237 hp762191 hp762359 (hp762430 rfl) rfl rfl))

theorem hd5058 : hp762190 hp762191 := hp762431

noncomputable def hp762432 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 869838 1000)) Bool.false 69069943403023471068459 9444732965739290427392 292220567895345409944501

noncomputable def hp762433 := nat_lit 357128965267016919285760000

noncomputable def hp762434 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 869838 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 869838 1000)) Bool.false 69069943403023471068459 9444732965739290427392

noncomputable def hp762435 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 869838 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762436 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp762435 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762437 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 869838 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762438 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp762436 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp762439 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 869838 1000)) hp762438 Bool.false 69069943403023471068459 9444732965739290427392

noncomputable def hp762440 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 869838 1000) 869838 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl

noncomputable def hp762441 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp762436 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp762442 := nat_lit 4635205438321199308741149720576

noncomputable def hp762443 := @hp762441 480663543 67108864 52765 67108864 1422563617230271661355 9444732965739290427392 11424429663678312344501 hp762433 hp762442 69069943403023471068459 9444732965739290427392

noncomputable def hp762444 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) 11)

noncomputable def hp762445 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) 11) hp762444

noncomputable def hp762446 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) 11)

noncomputable def hp762447 := @hp762446 1922654172 536870912 211060 536870912 1922654172 536870912 211060 536870912 2064434197564489728 480663543 67108864

noncomputable def hp762448 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp762449 := hp762448 BSN.quadSignPos 9 10 11 869838 1000 187 239 536870912 268435456 9007199254740992

noncomputable def hp762450 := hp762449 Bool.false 917526334789 3963 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp762451 := hp762450 Bool.false 1746467822 181189 Bool.true 59655824 Bool.true 716253544 28296951008113761 1 Bool.false 59533136

noncomputable def hp762452 := hp762451 Bool.false Bool.false 521905155 Bool.false Bool.false 1922654172 211060 BSN.abs_quadSignPos (BSN.cos_quad_nat3 187 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59533136 536870912) BSN.abs_quadSignPos

noncomputable def hp762453 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp762454 := hp762453 BSN.quadSignPos 7 8 9 869838 1000 63 128 536870912 268435456 9007199254740992

noncomputable def hp762455 := hp762454 Bool.false 917526334789 3963 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp762456 := hp762455 Bool.false 1536996459 147976 Bool.true 424731917 Bool.true 612838931 28296951008113761 1 Bool.false 381792817

noncomputable def hp762457 := hp762456 Bool.false Bool.false 223461648 Bool.false Bool.false 1746467822 181189 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 381792817 536870912) BSN.abs_quadSignPos

noncomputable def hp762458 := hp762453 BSN.quadSignNeg 5 6 7 869838 1000 95 10 536870912 268435456 9007199254740992

noncomputable def hp762459 := hp762458 Bool.false 917526334789 3963 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp762460 := hp762459 Bool.false 1484642433 109963 Bool.false 676384560 Bool.false 371217365 28296951008113761 1 Bool.false 511127345

noncomputable def hp762461 := hp762460 Bool.false Bool.false 413564888 Bool.true Bool.false 1536996459 147976 BSN.abs_quadSignPos (BSN.cos_quad_nat3 95 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 511127345 536870912) BSN.abs_quadSignNeg

noncomputable def hp762462 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp762463 := hp762462 BSN.quadSignPos 3 4 5 869838 1000 320 196 536870912 268435456 9007199254740992

noncomputable def hp762464 := hp762463 Bool.false 917526334789 3963 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp762465 := hp762464 Bool.false 1164568682 64993 Bool.false 278990517 Bool.false 644066610 28296951008113761 1 Bool.false 465997457

noncomputable def hp762466 := hp762465 Bool.false Bool.false 194705681 Bool.false Bool.false 1484642433 109963 BSN.abs_quadSignPos (BSN.cos_quad_nat0 320 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 465997457 536870912) BSN.abs_quadSignPos

noncomputable def hp762467 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp762468 := hp762467 BSN.quadSignPos 1 2 3 869838 1000 704 479 536870912 268435456 9007199254740992

noncomputable def hp762469 := hp762468 Bool.false 917526334789 3963 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp762470 := hp762469 Bool.false 536870856 4018 Bool.false 139387658 Bool.false 536779091 28296951008113761 1 Bool.false 518877735

noncomputable def hp762471 := hp762470 Bool.false Bool.false 451711677 Bool.false Bool.false 1164568682 64993 BSN.abs_quadSignPos (BSN.cos_quad_nat0 704 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 518877735 536870912) BSN.abs_quadSignPos

noncomputable def hp762472 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) 1) Bool.false

noncomputable def hp762473 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)))

noncomputable def hp762474 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000))) Bool.false 67108857 67108864

noncomputable def hp762475 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14336348981) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false 14336348981 8388608

noncomputable def hp762476 := nat_lit 104181150562240605558354302544757883635767005569185902717

noncomputable def hp762477 := nat_lit 60959372167111338758709022114961004859994409009152000

noncomputable def hp762478 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) Bool.false hp762476 hp762477 65834513570002487537

noncomputable def hp762479 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 869838 4000) (Real.log (Enclosure.sfrac Bool.false 3026473584976 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1739676))))))

noncomputable def hp762480 := nat_lit 239019582355289971306833647600640000

noncomputable def hp762481 := nat_lit 1247450085211317056810869869501968977920

noncomputable def hp762482 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp762479 (Enclosure.sfrac Bool.false 869838 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 869838 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp762480 hp762481)) Bool.false

noncomputable def hp762483 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 869838 1000) 869838 1000 3026473584976 16000000 1739676

noncomputable def hp762484 := hp762483 4000 2000 hp762480 hp762481 (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl rfl rfl rfl

noncomputable def hp762485 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp762479 (Enclosure.sfrac Bool.false 869838 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 869838 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp762480 hp762481) 15393539230290144291857 9007199254740992000

noncomputable def hp762486 := nat_lit 19202669671632188416515865045049773111744574466512345588797440

noncomputable def hp762487 := @hp762485 65834513570002487537 hp739631 hp762480 hp762481 0 1 hp762486 hp762476 hp762477 65834513570002487537 hp739631

noncomputable def hp762488 := @Enclosure.Real.IsNear.subLit_ff_p (hp762479 (Enclosure.sfrac Bool.false 869838 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 869838 2000) (Real.log Real.pi)) 19877906467457229548561 9007199254740992000 5486495551927697 2178000000000000000000

noncomputable def hp762489 := nat_lit 516521465342102986911303860224000

noncomputable def hp762490 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 869838 4000) (Real.log (Enclosure.sfrac Bool.false 3026473584976 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1739676))))))

noncomputable def hp762491 := @hp762490 (Enclosure.sfrac Bool.false 869838 2000) 23795308560129927048209 9007199254740992000 5486495551927697 2178000000000000000000 869838 2000 0

noncomputable def hp762492 := nat_lit 39755812934914459097122000

noncomputable def hp762493 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 869838 4000) (Real.log (Enclosure.sfrac Bool.false 3026473584976 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1739676))))) 23798844384677281300209

noncomputable def hp762494 := nat_lit 53582271382283556583072580434848120832

noncomputable def hp762495 := @hp762493 9007199254740992000 1812165183885149 726000000000000000000 883956136838563 2251799813685248 200000001089 8712000000000000000 hp762494 23795308560129927048209 9007199254740992000 5486495551927697

noncomputable def hp762496 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 869838 4000) (Real.log (Enclosure.sfrac Bool.false 3026473584976 16000000)) 869838 4000 0 1 54720176365431911 4503599627370496

noncomputable def hp762497 := nat_lit 117510683960441101329891328

noncomputable def hp762498 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3026473584976) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp762497 hp617687

noncomputable def hp762499 := BSN.log_rat_reduce_isNear 3026473584976 16000000 17 6052947169952 4194304000000 98466923 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp762500 := nat_lit 129598015138920122168930824000014557457186505682731480582897467944751935571108941018657452860497635385292552711884353608508527083520

noncomputable def hp762501 := nat_lit 1449927074270988479514642457523307729999444936415749297267387767029229303252366987423953262163675029560025327652299698466407317504

noncomputable def hp762502 := nat_lit 454037844252590044921218643582418859829005341651737612358155073412134527225698054753474948628390943892905036205298884280320

noncomputable def hp762503 := BSN.log_dyadic_bound 929321584976 5123625584976 6 5 hp762500 268435456 87120000 hp762501 hp762502 98466923 6052947169952

noncomputable def hp762504 := hp762503 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp762505 := @BSN.binarySplit_of_base5 (BSN.artanhP 929321584976) (BSN.artanhQ 5123625584976) 0 5 hp762501 hp762500 hp762502 rfl rfl rfl

noncomputable def hp762506 := hp762499 rfl rfl rfl rfl (hp762504 (hp762505 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp762507 := @hp762496 12500018513 1089000000000000000 23798844384677281300209 9007199254740992000 1812165183885149 726000000000000000000 (Enclosure.Real.IsNear.const Bool.false 869838 4000) (BSN.isNear_log_sfrac 3026473584976 16000000 54720176365431911 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp762498 1000001481040000 87120000000000000000000 54720176365431911 4503599627370496 12500018513 1089000000000000000 (hp762506 rfl rfl rfl) rfl)) rfl

noncomputable def hp762508 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1739676)))) 1 4

noncomputable def hp762509 := @hp762508 0 1 883956136838563 562949953421312 200000001089 2178000000000000000 883956136838563 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp762510 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1739676))) 884279719003555 562949953421312 1

noncomputable def hp762511 := @hp762510 2000000000000000 19287 33554432 1 10890000 29660646084532257161216 883956136838563 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp762512 := BSN.arctan_dyadic_bound_f 1000 1739676 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp762513 := hp762512 1 19287 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1739676) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1739676) 0 0 rfl)

noncomputable def hp762514 := hp762509 (hp762511 (hp762513 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp762515 := @hp762488 16705569763359 33554432000 1304757 268435456000 hp762489 15393539230290144291857 9007199254740992000 65834513570002487537 hp739631 (@hp762491 1 hp762492 19877906467457229548561 9007199254740992000 5486495551927697 2178000000000000000000 (@hp762495 2178000000000000000000 hp762507 hp762514 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 869838 2000) rfl rfl)

noncomputable def hp762516 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 869838 2000) (Real.log Real.pi) 869838 2000 0 1 38410761 33554432

noncomputable def hp762517 := hp762515 (@hp762516 3 268435456 16705569763359 33554432000 1304757 268435456000 (Enclosure.Real.IsNear.const Bool.false 869838 2000) hd4909 rfl) rfl

noncomputable def hp762518 := @hp762478 hp739631 14336348981 8388608 31 4194304 (@hp762482 hp762476 hp762477 65834513570002487537 hp739631 (hp762484 rfl rfl rfl rfl rfl) (hp762487 (hp762517 rfl) (Enclosure.Real.IsNear.const Bool.true hp762480 hp762481) rfl rfl)) rfl

noncomputable def hp762519 := nat_lit 1898460296569743057354752

noncomputable def hp762520 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 14336348981) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp762519) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp762521 := BSN.sin_reduce_arg_pos_rat_q3 14336348981 8388608 226375608064910080 72057594037927936 271 hp762519 hp630689 rfl rfl rfl rfl

noncomputable def hp762522 := nat_lit 14364728893228835553214963191889715815879195596082406954989825689043644090771836135688842614235271751709884169932265409640987188994531825816801

noncomputable def hp762523 := nat_lit 10217401623520247672131562968037444662465912468619527793806308766614878071146529114193936937962462676136086035009332947379138641749349601

noncomputable def hp762524 := nat_lit 71734491529650909740524147767352479137678694959743466978899953671463708192881223884149080051309684210192014991207668848314876684849717415515361

noncomputable def hp762525 := BSN.sin_dyadic_bound_f 215829947657 137438953472 4 3 67108864 21801270 hp762522 hp737934 hp762523 hp762524 hp737937

noncomputable def hp762526 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215829947657) (BSN.sinEvenQ 137438953472) 0 3 hp762522 hp737934 hp762523 rfl rfl rfl

noncomputable def hp762527 := hp762525 hp762523 67108857 rfl rfl rfl rfl rfl rfl rfl rfl (hp762526 rfl)

noncomputable def hp762528 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215829947657) (BSN.sinOddQ 137438953472) 0 3 hp762524 hp737937 hp762523 rfl rfl rfl

noncomputable def hp762529 := @BSN.sin_arg_round Bool.false 67108857 67108864 hp762519 hp630689 215829947657 137438953472 21801270 21780000 (hp762527 (hp762528 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762530 := hp762520 67108857 67108864 271 1000000000000000 21780000 10890000 hp762521 BSN.pi_near_15 hp762529 rfl rfl

noncomputable def hp762531 := @hp762475 31 4194304 Bool.false 67108857 67108864 1 10890000 hp762518 (Enclosure.sfrac_false_div 14336348981 8388608) (hp762530 rfl rfl) rfl

noncomputable def hp762532 := @hp762472 67108857 67108864 21361519 2854748160000 536870856 536870912 4018 536870912 (@hp762473 Bool.false 67108857 67108864 21361519 2854748160000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000)) (@hp762474 341784304 45675970560000 67108857 67108864 21361519 2854748160000 (hp762531 rfl) rfl))

noncomputable def hp762533 := @hp762478 hp739631 917526334789 536870912 3963 536870912 (@hp762482 hp762476 hp762477 65834513570002487537 hp739631 (hp762484 rfl rfl rfl rfl rfl) (hp762487 (hp762517 rfl) (Enclosure.Real.IsNear.const Bool.true hp762480 hp762481) rfl rfl)) rfl

noncomputable def hp762534 := hp762471 (BSN.cos_quad_nat3 479 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 451711677 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl rfl (hp762532 rfl) hp762533

noncomputable def hp762535 := nat_lit 377482901386014850765243028801296

noncomputable def hp762536 := BSN.cos_dyadic_bound_f 139387658 536870912 2 1 536870912 268435456 hp762535 hp708767 hp762535 hp762535 hp708768

noncomputable def hp762537 := @BSN.binarySplit_of_base (BSN.cosEvenP 139387658) (BSN.cosEvenQ 536870912) 0 1 hp762535 hp708767 hp762535 rfl rfl rfl

noncomputable def hp762538 := hp762536 hp762535 518877735 rfl rfl rfl rfl rfl rfl rfl rfl (hp762537 rfl)

noncomputable def hp762539 := @BSN.binarySplit_of_base (BSN.cosOddP 139387658) (BSN.cosOddQ 536870912) 0 1 hp762535 hp708768 hp762535 rfl rfl rfl

noncomputable def hp762540 := nat_lit 20863498741938466310625774716283033241297199966601317266885694328672577825

noncomputable def hp762541 := nat_lit 6892308755505005138081333969894812714538972344669660867102560747743521

noncomputable def hp762542 := nat_lit 54631337728996594138558230668599543078050079671588270533772938143408023841

noncomputable def hp762543 := BSN.sin_dyadic_bound_f 536779091 536870912 3 2 536870912 268435456 hp762540 hp708845 hp762541 hp762542 hp708848

noncomputable def hp762544 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 536779091) (BSN.sinEvenQ 536870912) 0 2 hp762540 hp708845 hp762541 rfl rfl rfl

noncomputable def hp762545 := hp762543 hp762541 451711677 rfl rfl rfl rfl rfl rfl rfl rfl (hp762544 rfl)

noncomputable def hp762546 := @BSN.binarySplit_of_base2 (BSN.sinOddP 536779091) (BSN.sinOddQ 536870912) 0 2 hp762542 hp708848 hp762541 rfl rfl rfl

noncomputable def hp762547 := hp762534 hd4911 hd4913 hd4915 hd4917 hd4918 (hp762538 (hp762539 rfl) rfl rfl rfl rfl) (hp762545 (hp762546 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762548 := hp762466 (BSN.cos_quad_nat0 196 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 194705681 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl rfl (hp762547 rfl rfl rfl rfl rfl) hp762533

noncomputable def hp762549 := nat_lit 845600822792538720072782419555796035044402902423419533002244781652359521

noncomputable def hp762550 := nat_lit 36704180625653822700040283346891038116696193795981881457078235609441

noncomputable def hp762551 := nat_lit 2536729060016364852572947178100694323056975314882666635243820188485859681

noncomputable def hp762552 := BSN.cos_dyadic_bound_f 278990517 536870912 3 2 536870912 268435456 hp762549 hp708868 hp762550 hp762551 hp708870

noncomputable def hp762553 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 278990517) (BSN.cosEvenQ 536870912) 0 2 hp762549 hp708868 hp762550 rfl rfl rfl

noncomputable def hp762554 := hp762552 hp762550 465997457 rfl rfl rfl rfl rfl rfl rfl rfl (hp762553 rfl)

noncomputable def hp762555 := @BSN.binarySplit_of_base2 (BSN.cosOddP 278990517) (BSN.cosOddQ 536870912) 0 2 hp762551 hp708870 hp762550 rfl rfl rfl

noncomputable def hp762556 := nat_lit 23732477013877163073123482133619670886955159499633927380838289177007442778515629162911639449304680514844224000000

noncomputable def hp762557 := nat_lit 5095295996070635562918252505610854366407014940610014746475240173470972822095760577846999869521000000000000

noncomputable def hp762558 := nat_lit 143858805860954166215612853648703153511895665531690886008060026172694175194491530687579516908011827519524825600000

noncomputable def hp762559 := BSN.cos_dyadic_bound_f 644066610 536870912 4 3 536870912 268435456 hp762556 hp716712 hp762557 hp762558 hp716714

noncomputable def hp762560 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 644066610) (BSN.cosEvenQ 536870912) 0 3 hp762556 hp716712 hp762557 rfl rfl rfl

noncomputable def hp762561 := hp762559 hp762557 194705681 rfl rfl rfl rfl rfl rfl rfl rfl (hp762560 rfl)

noncomputable def hp762562 := @BSN.binarySplit_of_base3 (BSN.cosOddP 644066610) (BSN.cosOddQ 536870912) 0 3 hp762558 hp716714 hp762557 rfl rfl rfl

noncomputable def hp762563 := hp762548 hd4920 hd4922 hd4924 hd4926 hd4918 (hp762554 (hp762555 rfl) rfl rfl rfl rfl) (hp762561 (hp762562 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762564 := hp762461 (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 413564888 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl rfl (hp762563 rfl rfl rfl rfl rfl) hp762533

noncomputable def hp762565 := nat_lit 75023018259142482326127294719425501303681528938863804111911543551172335380281450026924864119435307436631654400000

noncomputable def hp762566 := nat_lit 9169047518818437100499357152493014945370714421896319969713763500616843573956064079353779060736000000000000

noncomputable def hp762567 := nat_lit 374922021204172946135458407941552330416443519823478299902378999997015593160594441451298448373772789347254272000000

noncomputable def hp762568 := BSN.sin_dyadic_bound_f 676384560 536870912 4 3 536870912 268435456 hp762565 hp642702 hp762566 hp762567 hp642705

noncomputable def hp762569 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 676384560) (BSN.sinEvenQ 536870912) 0 3 hp762565 hp642702 hp762566 rfl rfl rfl

noncomputable def hp762570 := hp762568 hp762566 511127345 rfl rfl rfl rfl rfl rfl rfl rfl (hp762569 rfl)

noncomputable def hp762571 := @BSN.binarySplit_of_base3 (BSN.sinOddP 676384560) (BSN.sinOddQ 536870912) 0 3 hp762567 hp642705 hp762566 rfl rfl rfl

noncomputable def hp762572 := nat_lit 2650702567267219487467829932367734498941919368934905908152639185695190625

noncomputable def hp762573 := nat_lit 360600454201413133429162150463065296211394129541315637383239250390625

noncomputable def hp762574 := nat_lit 7951386500893255636136631472802277366233335318545635093183151078584790625

noncomputable def hp762575 := BSN.cos_dyadic_bound_f 371217365 536870912 3 2 536870912 268435456 hp762572 hp708868 hp762573 hp762574 hp708870

noncomputable def hp762576 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 371217365) (BSN.cosEvenQ 536870912) 0 2 hp762572 hp708868 hp762573 rfl rfl rfl

noncomputable def hp762577 := hp762575 hp762573 413564888 rfl rfl rfl rfl rfl rfl rfl rfl (hp762576 rfl)

noncomputable def hp762578 := @BSN.binarySplit_of_base2 (BSN.cosOddP 371217365) (BSN.cosOddQ 536870912) 0 2 hp762574 hp708870 hp762573 rfl rfl rfl

noncomputable def hp762579 := hp762564 hd4928 hd4930 hd4932 hd4934 hd4918 (hp762570 (hp762571 rfl) rfl rfl rfl rfl) (hp762577 (hp762578 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762580 := hp762457 (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 223461648 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl rfl (hp762579 rfl rfl rfl rfl rfl) hp762533

noncomputable def hp762581 := nat_lit 8176682401456559767791117653615701283398869394045703355708534452834916385

noncomputable def hp762582 := nat_lit 1059056627773980360047125880462276739634164241925558445345879760427041

noncomputable def hp762583 := nat_lit 21413405912131736756965231841377516817990012147061343598896554047336470561

noncomputable def hp762584 := BSN.sin_dyadic_bound_f 424731917 536870912 3 2 536870912 268435456 hp762581 hp708845 hp762582 hp762583 hp708848

noncomputable def hp762585 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 424731917) (BSN.sinEvenQ 536870912) 0 2 hp762581 hp708845 hp762582 rfl rfl rfl

noncomputable def hp762586 := hp762584 hp762582 381792817 rfl rfl rfl rfl rfl rfl rfl rfl (hp762585 rfl)

noncomputable def hp762587 := @BSN.binarySplit_of_base2 (BSN.sinOddP 424731917) (BSN.sinOddQ 536870912) 0 2 hp762583 hp708848 hp762582 rfl rfl rfl

noncomputable def hp762588 := nat_lit 19449518683333437246274497580293530031032453264148246039491667091276919138468347781254477115745964254350311137841

noncomputable def hp762589 := nat_lit 2806442548992342501942147240453517214731992264920225226893690882704201037293229751520779026838279685120561

noncomputable def hp762590 := nat_lit 117914313245938237186233531074095769641318395113158106065128834786007069507347046499845084488737525390180755677745

noncomputable def hp762591 := BSN.cos_dyadic_bound_f 612838931 536870912 4 3 536870912 268435456 hp762588 hp716712 hp762589 hp762590 hp716714

noncomputable def hp762592 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 612838931) (BSN.cosEvenQ 536870912) 0 3 hp762588 hp716712 hp762589 rfl rfl rfl

noncomputable def hp762593 := hp762591 hp762589 223461648 rfl rfl rfl rfl rfl rfl rfl rfl (hp762592 rfl)

noncomputable def hp762594 := @BSN.binarySplit_of_base3 (BSN.cosOddP 612838931) (BSN.cosOddQ 536870912) 0 3 hp762590 hp716714 hp762589 rfl rfl rfl

noncomputable def hp762595 := hp762580 hd4936 hd4938 hd4940 hd4942 hd4918 (hp762586 (hp762587 rfl) rfl rfl rfl rfl) (hp762593 (hp762594 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762596 := hp762452 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 521905155 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl rfl (hp762595 rfl rfl rfl rfl rfl) hp762533

noncomputable def hp762597 := nat_lit 12665180838978599271987979288576

noncomputable def hp762598 := BSN.sin_dyadic_bound_f 59655824 536870912 2 1 536870912 268435456 hp762597 hp708890 hp762597 hp762597 hp708891

noncomputable def hp762599 := @BSN.binarySplit_of_base (BSN.sinEvenP 59655824) (BSN.sinEvenQ 536870912) 0 1 hp762597 hp708890 hp762597 rfl rfl rfl

noncomputable def hp762600 := hp762598 hp762597 59533136 rfl rfl rfl rfl rfl rfl rfl rfl (hp762599 rfl)

noncomputable def hp762601 := @BSN.binarySplit_of_base (BSN.sinOddP 59655824) (BSN.sinOddQ 536870912) 0 1 hp762597 hp708891 hp762597 rfl rfl rfl

noncomputable def hp762602 := nat_lit 94358281634307959189378239792803101171398050177242109438886189969137499184139622537492324047258456728899038478336

noncomputable def hp762603 := nat_lit 18230618638667441965221633820794560489238724391424362791666323554491561418768490713274859441893068542836736

noncomputable def hp762604 := nat_lit 471486112230367819484678568242789697213588283163969756346572545279211286447216698574510358371990909271274942365696

noncomputable def hp762605 := BSN.sin_dyadic_bound_f 716253544 536870912 4 3 536870912 268435456 hp762602 hp642702 hp762603 hp762604 hp642705

noncomputable def hp762606 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 716253544) (BSN.sinEvenQ 536870912) 0 3 hp762602 hp642702 hp762603 rfl rfl rfl

noncomputable def hp762607 := hp762605 hp762603 521905155 rfl rfl rfl rfl rfl rfl rfl rfl (hp762606 rfl)

noncomputable def hp762608 := @BSN.binarySplit_of_base3 (BSN.sinOddP 716253544) (BSN.sinOddQ 536870912) 0 3 hp762604 hp642705 hp762603 rfl rfl rfl

noncomputable def hp762609 := hp762596 hd4944 hd4946 hd4961 hd4963 hd4918 (hp762600 (hp762601 rfl) rfl rfl rfl rfl) (hp762607 (hp762608 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762610 := @hp762447 52765 67108864 (hp762609 rfl rfl rfl rfl rfl) (hp762609 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp762611 := @hp762445 Bool.false 480663543 67108864 52765 67108864 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 869838 1000)) (Enclosure.sfrac Bool.false 869838 1000) 11) hp762610

noncomputable def hp762612 := @Enclosure.Real.IsNear.mulLit_tf hp762436 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1))) 19564343 67108864 1

noncomputable def hp762613 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp762435 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762614 := @hp762613 1 1 0 1 19564343 67108864 1 67108864 19564343 67108864 1

noncomputable def hp762615 := @Enclosure.Real.IsNear.of_eq (hp762435 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762616 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 869838 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762617 := @hp762615 (@Inv.inv Real Real.instInv (Real.sqrt hp762437)) Bool.false 19564343 67108864 1 67108864 (hp762616 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 869838 1000) 869838 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000))))

noncomputable def hp762618 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp762437)) Bool.false 19564343 67108864 1 67108864 19564343 67108864

noncomputable def hp762619 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp762437) Bool.false 230194271 67108864 7 67108864 230194271 67108864 7 67108864

noncomputable def hp762620 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 869838 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762621 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 869838 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762622 := @hp762621 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 869838 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4645242407733

noncomputable def hp762623 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 869838 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 869838 1000 0

noncomputable def hp762624 := @hp762623 1 10680707 67108864 1 67108864 4645242407733 33554432000 434919 33554432000 (Enclosure.Real.IsNear.const Bool.false 869838 1000) hd4949

noncomputable def hp762625 := @hp762622 33554432000 434919 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 869838 1000) 869838 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000))) (hp762624 rfl)

noncomputable def hp762626 := @hp762620 4645242407733 33554432000 434919 33554432000 394801793 394801831 33554432 hp762625 rfl rfl rfl

noncomputable def hp762627 := @Enclosure.Real.IsNear.recentre' hp762437 Bool.false 789603624 67108864 38 67108864 98700453 8388608 19 33554432 (hp762626 rfl rfl rfl)

noncomputable def hp762628 := @Enclosure.Real.IsNear.sqrt_image hp762437 98700453 8388608 19 33554432 115097132 115097139 33554432 (hp762627 rfl) rfl rfl

noncomputable def hp762629 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp762437) 230194271 67108864 7 67108864 9782171 9782172 33554432 (hp762619 (hp762628 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp762630 := @hp762614 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp762617 (@hp762618 1 67108864 (hp762629 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp762631 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762632 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp762633 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1))) (hp762631 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762632 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp762634 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 869838 1000) 869838 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl

noncomputable def hp762635 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762636 := @hp762635 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762632 (Enclosure.sfrac Bool.false 1 16)))) 668217219

noncomputable def hp762637 := @hp762636 67108864 24407 67108864 108815 2097152 208326527 22837985280000 72712056685485 140737488355328 84067319324431451 766315624094760960000

noncomputable def hp762638 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762639 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)))) 1684931

noncomputable def hp762640 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp762641 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 322994177) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp762642 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1))) Bool.false 5682173668582878594575

noncomputable def hp762643 := nat_lit 512735432992624467862461893

noncomputable def hp762644 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp762645 := @Enclosure.Real.IsNear.subLit_ff_p hp762437 (Enclosure.sfrac Bool.false 11 1) 98700453 8388608 19 33554432 11 1 0

noncomputable def hp762646 := @hp762644 500000000000000 6425765 8388608 19 33554432 5682173668582878594575 1180591620717411303424 hp762643 hp682805 hd4948 (@hp762645 1 6425765 6425765 8388608 19 33554432 (hp762627 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762647 := @hp762641 322994177 67108864 15 4194304 Bool.false 6739724 67108864 1 10890000 (@hp762642 1180591620717411303424 hp762643 hp682805 322994177 67108864 15 4194304 (hp762646 rfl) rfl) (Enclosure.sfrac_false_div 322994177 67108864)

noncomputable def hp762648 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 322994177) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 972936882125219754409984) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp762649 := BSN.sin_reduce_arg_pos_rat_q3 322994177 67108864 226375608064910080 72057594037927936 0 972936882125219754409984 hp617687 rfl rfl rfl rfl

noncomputable def hp762650 := nat_lit 36544284691100366808035788239935335491856

noncomputable def hp762651 := BSN.sin_dyadic_bound_f 13826264678 137438953472 2 1 67108864 21801270 hp762650 hp749778 hp762650 hp762650 hp749779

noncomputable def hp762652 := @BSN.binarySplit_of_base (BSN.sinEvenP 13826264678) (BSN.sinEvenQ 137438953472) 0 1 hp762650 hp749778 hp762650 rfl rfl rfl

noncomputable def hp762653 := hp762651 hp762650 6739724 rfl rfl rfl rfl rfl rfl rfl rfl (hp762652 rfl)

noncomputable def hp762654 := @BSN.binarySplit_of_base (BSN.sinOddP 13826264678) (BSN.sinOddQ 137438953472) 0 1 hp762650 hp749779 hp762650 rfl rfl rfl

noncomputable def hp762655 := @BSN.sin_arg_round Bool.false 6739724 67108864 972936882125219754409984 hp617687 13826264678 137438953472 21801270 21780000 (hp762653 (hp762654 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762656 := hp762648 6739724 67108864 0 1000000000000000 21780000 10890000 hp762649 BSN.pi_near_15 hp762655 rfl rfl

noncomputable def hp762657 := @hp762639 16777216 10471519 2854748160000 334096406 334120813 33554432 (@hp762640 6739724 67108864 167544304 45675970560000 1684931 16777216 10471519 2854748160000 (hp762647 (hp762656 rfl rfl) rfl rfl) rfl)

noncomputable def hp762658 := @hp762638 Bool.false 668217219 67108864 24407 67108864 668217219 67108864 24407 67108864 (hp762657 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp762659 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762632 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp762660 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762632 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 12741339)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true

noncomputable def hp762661 := nat_lit 15042318143165833724334351445

noncomputable def hp762662 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762632 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp762661

noncomputable def hp762663 := nat_lit 43562295142565321177883267390641511

noncomputable def hp762664 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762632 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp762665 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp762666 := @hp762665 (Enclosure.sfrac Bool.false 1 16) 12612767849895 70368744177664 1614250849 1125899906842624 1 16 0

noncomputable def hp762667 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)) 41290455835225

noncomputable def hp762668 := @hp762667 70368744177664 976716641 1125899906842624 6425765 8388608 19 33554432 105803565287771996160 12612767849895 70368744177664 1614250849

noncomputable def hp762669 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)) 6425765 8388608 19

noncomputable def hp762670 := @hp762669 33554432 6425765 8388608 19 33554432 41290455835225 70368744177664 976716641 1125899906842624 (@hp762645 1 6425765 6425765 8388608 19 33554432 (hp762627 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762671 := hp762670 (@hp762645 1 6425765 6425765 8388608 19 33554432 (hp762627 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762672 := @hp762668 1125899906842624 (hp762671 rfl) (@hp762645 1 6425765 6425765 8388608 19 33554432 (hp762627 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762673 := @hp762664 500000000000000 17010814360999 70368744177664 1614250849 1125899906842624 hp762661 hp619387 hp762663 hp682143 hd4948 (@hp762666 1 272173029775984 17010814360999 70368744177664 1614250849 1125899906842624 (hp762672 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp762674 := @hp762660 12741339 8388608 303 33554432 Bool.false 1741040 33554432 1 10890000 (@hp762662 hp619387 hp762663 hp682143 12741339 8388608 303 33554432 (hp762673 rfl) rfl) (Enclosure.sfrac_true_div 12741339 8388608)

noncomputable def hp762675 := nat_lit 12938368380256001734369495203638419397462337777195334357983713345841971974602060876201486801

noncomputable def hp762676 := nat_lit 18305468567196008266882877685311789372966829539598868955799045483175899709954540333521

noncomputable def hp762677 := nat_lit 78327420093219051829912660762726953887189546903280925168346921622616765332849443933245041105

noncomputable def hp762678 := BSN.cos_dyadic_bound_f 12741339 8388608 4 3 33554432 10890000 hp762675 hp633059 hp762676 hp762677 hp633062

noncomputable def hp762679 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 12741339) (BSN.cosEvenQ 8388608) 0 3 hp762675 hp633059 hp762676 rfl rfl rfl

noncomputable def hp762680 := hp762678 hp762676 1741040 rfl rfl rfl rfl rfl rfl rfl rfl (hp762679 rfl)

noncomputable def hp762681 := @BSN.binarySplit_of_base3 (BSN.cosOddP 12741339) (BSN.cosOddQ 8388608) 0 3 hp762677 hp633062 hp762676 rfl rfl rfl

noncomputable def hp762682 := hp762674 (BSN.cos_neg_of_bound 12741339 8388608 Bool.false 1741040 33554432 1 10890000 (hp762680 (hp762681 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp762683 := hp762637 hp762658 (@hp762659 1741040 33554432 3333224432 365407764480000 108815 2097152 208326527 22837985280000 (hp762682 rfl) rfl)

noncomputable def hp762684 := @hp762612 67108864 72712056685485 140737488355328 84067319324431451 766315624094760960000 1422563617230271661355 9444732965739290427392 11424429663678312344501 hp762433 (hp762630 rfl) (@hp762633 Bool.false 72712056685485 140737488355328 84067319324431451 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762437 (Enclosure.sfrac Bool.false 11 1)) (hp762634 rfl (hp762440 rfl rfl))) (hp762683 rfl))

noncomputable def hp762685 := @hp762434 292220567895345409944501 hp762433 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 869838 1000))) (@hp762439 292220567895345409944501 hp762433 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 869838 1000) 11 (hp762440 rfl rfl)) (@hp762443 292220567895345409944501 hp762433 hp762611 (hp762684 rfl) rfl rfl))

theorem hd5059 : hp762432 hp762433 := hp762685

noncomputable def hp762686 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 871112 1000)) Bool.true 65514246868862362231561 37778931862957161709568 461956554045444868163437

noncomputable def hp762687 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 871112 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 871112 1000)) Bool.true 65514246868862362231561 37778931862957161709568

noncomputable def hp762688 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 871112 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762689 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp762688 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762690 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 871112 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762691 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp762689 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp762692 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 871112 1000)) hp762691 Bool.true 65514246868862362231561 37778931862957161709568

noncomputable def hp762693 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 871112 1000) 871112 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl

noncomputable def hp762694 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp762689 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp762695 := nat_lit 4396586683184910101716563656704

noncomputable def hp762696 := @hp762694 126666593 67108864 211373 268435456 5792705760523922398455 37778931862957161709568 12016464012717344835437 hp751106 hp762695 65514246868862362231561 37778931862957161709568

noncomputable def hp762697 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) 11)

noncomputable def hp762698 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) 11) hp762697

noncomputable def hp762699 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) 11)

noncomputable def hp762700 := @hp762699 506666372 536870912 211373 536870912 506666372 536870912 211373 536870912 544028874430742528 126666593 67108864

noncomputable def hp762701 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp762702 := hp762701 BSN.quadSignPos 9 10 11 871112 1000 186 239 536870912 268435456 9007199254740992

noncomputable def hp762703 := hp762702 Bool.false 919212726742 3969 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp762704 := hp762703 Bool.true 643808979 181458 Bool.true 791486006 Bool.true 669958511 28296951008113761 1 Bool.false 51748382

noncomputable def hp762705 := hp762704 Bool.true Bool.false 509124754 Bool.false Bool.true 506666372 211373 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 51748382 536870912) BSN.abs_quadSignPos

noncomputable def hp762706 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp762707 := hp762706 BSN.quadSignPos 7 8 9 871112 1000 63 128 536870912 268435456 9007199254740992

noncomputable def hp762708 := hp762707 Bool.false 919212726742 3969 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp762709 := hp762708 Bool.true 824484194 148196 Bool.true 160622960 Bool.true 429290435 28296951008113761 1 Bool.false 158237413

noncomputable def hp762710 := hp762709 Bool.false Bool.false 374189525 Bool.false Bool.true 643808979 181458 BSN.abs_quadSignPos (BSN.cos_quad_nat3 63 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 158237413 536870912) BSN.abs_quadSignPos

noncomputable def hp762711 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp762712 := hp762711 BSN.quadSignNeg 5 6 7 871112 1000 96 10 536870912 268435456 9007199254740992

noncomputable def hp762713 := hp762712 Bool.false 919212726742 3969 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp762714 := hp762713 Bool.true 967875707 110127 Bool.false 293945596 Bool.false 726658281 28296951008113761 1 Bool.false 458391159

noncomputable def hp762715 := hp762714 Bool.false Bool.false 115740752 Bool.true Bool.true 824484194 148196 BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 458391159 536870912) BSN.abs_quadSignNeg

noncomputable def hp762716 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp762717 := hp762716 BSN.quadSignNeg 3 4 5 871112 1000 321 197 536870912 268435456 9007199254740992

noncomputable def hp762718 := hp762717 Bool.false 919212726742 3969 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp762719 := hp762718 Bool.true 724205316 65091 Bool.false 173878967 Bool.false 386330778 28296951008113761 1 Bool.false 170855034

noncomputable def hp762720 := hp762719 Bool.true Bool.false 353841821 Bool.true Bool.true 967875707 110127 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 321 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 170855034 536870912) BSN.abs_quadSignNeg

noncomputable def hp762721 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp762722 := hp762721 BSN.quadSignPos 1 2 3 871112 1000 705 480 536870912 268435456 9007199254740992

noncomputable def hp762723 := hp762722 Bool.false 919212726742 3969 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp762724 := hp762723 Bool.true 536870704 4026 Bool.false 508370441 Bool.false 628434457 28296951008113761 1 Bool.false 435733240

noncomputable def hp762725 := hp762724 Bool.true Bool.false 209188986 Bool.false Bool.true 724205316 65091 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 705 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 435733240 536870912) BSN.abs_quadSignPos

noncomputable def hp762726 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) 1) Bool.true

noncomputable def hp762727 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)))

noncomputable def hp762728 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000))) Bool.true 67108838 67108864

noncomputable def hp762729 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 57450795421) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 57450795421 33554432

noncomputable def hp762730 := nat_lit 740342869736039516293066659851556779418862893642818879

noncomputable def hp762731 := nat_lit 432401053754244801169692725032207814426084612505600

noncomputable def hp762732 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) Bool.false hp762730 hp762731 16482659377318128847

noncomputable def hp762733 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 871112 4000) (Real.log (Enclosure.sfrac Bool.false 3035345466176 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1742224))))))

noncomputable def hp762734 := nat_lit 240775105516000506404402766479360000

noncomputable def hp762735 := nat_lit 1258452695777653719908827697602705489920

noncomputable def hp762736 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp762733 (Enclosure.sfrac Bool.false 871112 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 871112 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp762734 hp762735)) Bool.false

noncomputable def hp762737 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 871112 1000) 871112 1000 3035345466176 16000000 1742224

noncomputable def hp762738 := hp762737 4000 2000 hp762734 hp762735 (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl rfl rfl rfl

noncomputable def hp762739 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp762733 (Enclosure.sfrac Bool.false 871112 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 871112 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp762734 hp762735) 771091609491326175339 450359962737049600

noncomputable def hp762740 := nat_lit 970382206220421714795648332400632501919891971955515561082880

noncomputable def hp762741 := @hp762739 16482659377318128847 hp741637 hp762734 hp762735 0 1 hp762740 hp762730 hp762731 16482659377318128847 hp741637

noncomputable def hp762742 := @Enclosure.Real.IsNear.subLit_ff_p (hp762733 (Enclosure.sfrac Bool.false 871112 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 871112 2000) (Real.log Real.pi)) 4978191853263888656919 2251799813685248000 2747229031860239 1089000000000000000000

noncomputable def hp762743 := nat_lit 32341926220559073425290690560000

noncomputable def hp762744 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 871112 4000) (Real.log (Enclosure.sfrac Bool.false 3035345466176 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1742224))))))

noncomputable def hp762745 := @hp762744 (Enclosure.sfrac Bool.false 871112 2000) 5958976772913380534807 2251799813685248000 2747229031860239 1089000000000000000000 871112 2000 0

noncomputable def hp762746 := nat_lit 9956383706527777313838000

noncomputable def hp762747 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 871112 4000) (Real.log (Enclosure.sfrac Bool.false 3035345466176 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1742224))))) 5959860729519981145807

noncomputable def hp762748 := nat_lit 13418422787001070669161590775806427136

noncomputable def hp762749 := @hp762747 2251799813685248000 123737683260187 49500000000000000000 883956606600611 2251799813685248 200000001089 8712000000000000000 hp762748 5958976772913380534807 2251799813685248000 2747229031860239

noncomputable def hp762750 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 871112 4000) (Real.log (Enclosure.sfrac Bool.false 3035345466176 16000000)) 871112 4000 0 1 54733359012572263 4503599627370496

noncomputable def hp762751 := nat_lit 117538993479612361210855424

noncomputable def hp762752 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3035345466176) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp762751 hp617687

noncomputable def hp762753 := BSN.log_rat_reduce_isNear 3035345466176 16000000 17 6070690932352 4194304000000 99252670 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp762754 := nat_lit 131859653465338565817096271346921939735858561350567082258123343214585162517309548236548728456671291050720071519151427168648057323520

noncomputable def hp762755 := nat_lit 1498814428280527939751118619245457436088859190233682184526296630107676043014860265669868126730473887443635284544117899703042965504

noncomputable def hp762756 := nat_lit 499293427629370485763427028185892006140700561343064534830352121407167258368133705017101434951823397419792498946344296120320

noncomputable def hp762757 := BSN.log_dyadic_bound 938193466176 5132497466176 6 5 hp762754 268435456 87120000 hp762755 hp762756 99252670 6070690932352

noncomputable def hp762758 := hp762757 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp762759 := @BSN.binarySplit_of_base5 (BSN.artanhP 938193466176) (BSN.artanhQ 5132497466176) 0 5 hp762755 hp762754 hp762756 rfl rfl rfl

noncomputable def hp762760 := hp762753 rfl rfl rfl rfl (hp762758 (hp762759 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp762761 := @hp762750 12500018513 1089000000000000000 5959860729519981145807 2251799813685248000 123737683260187 49500000000000000000 (Enclosure.Real.IsNear.const Bool.false 871112 4000) (BSN.isNear_log_sfrac 3035345466176 16000000 54733359012572263 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp762752 1000001481040000 87120000000000000000000 54733359012572263 4503599627370496 12500018513 1089000000000000000 (hp762760 rfl rfl rfl) rfl)) rfl

noncomputable def hp762762 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1742224)))) 1 4

noncomputable def hp762763 := @hp762762 0 1 883956606600611 562949953421312 200000001089 2178000000000000000 883956606600611 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp762764 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1742224))) 884279719003555 562949953421312 1

noncomputable def hp762765 := @hp762764 2000000000000000 19259 33554432 1 10890000 29660661847130952957952 883956606600611 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp762766 := BSN.arctan_dyadic_bound_f 1000 1742224 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp762767 := hp762766 1 19259 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1742224) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1742224) 0 0 rfl)

noncomputable def hp762768 := hp762763 (hp762765 (hp762767 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp762769 := @hp762742 4182509354529 8388608000 326667 67108864000 hp762743 771091609491326175339 450359962737049600 16482659377318128847 hp741637 (@hp762745 1 hp762746 4978191853263888656919 2251799813685248000 2747229031860239 1089000000000000000000 (@hp762749 1089000000000000000000 hp762761 hp762768 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 871112 2000) rfl rfl)

noncomputable def hp762770 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 871112 2000) (Real.log Real.pi) 871112 2000 0 1 38410761 33554432

noncomputable def hp762771 := hp762769 (@hp762770 3 268435456 4182509354529 8388608000 326667 67108864000 (Enclosure.Real.IsNear.const Bool.false 871112 2000) hd4909 rfl) rfl

noncomputable def hp762772 := @hp762732 hp741637 57450795421 33554432 497 67108864 (@hp762736 hp762730 hp762731 16482659377318128847 hp741637 (hp762738 rfl rfl rfl rfl rfl) (hp762741 (hp762771 rfl) (Enclosure.Real.IsNear.const Bool.true hp762734 hp762735) rfl rfl)) rfl

noncomputable def hp762773 := nat_lit 7591699624989225251766272

noncomputable def hp762774 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 57450795421) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp762773) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp762775 := BSN.sin_reduce_arg_pos_rat_q1 57450795421 33554432 226375608064910080 72057594037927936 272 hp762773 hp619237 rfl rfl rfl rfl

noncomputable def hp762776 := nat_lit 14348499095510117370987488554664490680634295068714719547941046042971461259948890978745214112531923919360607551108410578152480741501158006194176

noncomputable def hp762777 := nat_lit 10182877934172417893475511287646776918202650566686725677084669728936418408971127565092003717194686715208681276016022498346045011683966976

noncomputable def hp762778 := nat_lit 71653543526853443722740579356545949891022964593472585993701040036110111366182330684325361651033609932468921231088619737587106445144402465652736

noncomputable def hp762779 := BSN.sin_dyadic_bound_f 215769080824 137438953472 4 3 67108864 21801270 hp762776 hp737934 hp762777 hp762778 hp737937

noncomputable def hp762780 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215769080824) (BSN.sinEvenQ 137438953472) 0 3 hp762776 hp737934 hp762777 rfl rfl rfl

noncomputable def hp762781 := hp762779 hp762777 67108838 rfl rfl rfl rfl rfl rfl rfl rfl (hp762780 rfl)

noncomputable def hp762782 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215769080824) (BSN.sinOddQ 137438953472) 0 3 hp762778 hp737937 hp762777 rfl rfl rfl

noncomputable def hp762783 := @BSN.sin_arg_round Bool.false 67108838 67108864 hp762773 hp619237 215769080824 137438953472 21801270 21780000 (hp762781 (hp762782 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762784 := hp762774 67108838 67108864 272 1000000000000000 21780000 10890000 hp762775 BSN.pi_near_15 hp762783 rfl rfl

noncomputable def hp762785 := @hp762729 497 67108864 Bool.true 67108838 67108864 1 10890000 hp762772 (Enclosure.sfrac_false_div 57450795421 33554432) (hp762784 rfl rfl) rfl

noncomputable def hp762786 := @hp762726 33554419 33554432 342464929 45675970560000 536870704 536870912 4026 536870912 (@hp762727 Bool.true 33554419 33554432 342464929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000)) (@hp762728 5479438864 730815528960000 33554419 33554432 342464929 45675970560000 (hp762785 rfl) rfl))

noncomputable def hp762787 := @hp762732 hp741637 919212726742 536870912 3969 536870912 (@hp762736 hp762730 hp762731 16482659377318128847 hp741637 (hp762738 rfl rfl rfl rfl rfl) (hp762741 (hp762771 rfl) (Enclosure.Real.IsNear.const Bool.true hp762734 hp762735) rfl rfl)) rfl

noncomputable def hp762788 := hp762725 (BSN.cos_quad_nat0 480 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 209188986 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl rfl (hp762786 rfl) hp762787

noncomputable def hp762789 := nat_lit 16784093677653977747819183914542475206981622462933913815526262811734460225

noncomputable def hp762790 := nat_lit 4461103773703341112189563837306283868705478494306928186449628465088321

noncomputable def hp762791 := nat_lit 43951117844888707739630508101398462987259678532978991633124055584646776641

noncomputable def hp762792 := BSN.sin_dyadic_bound_f 508370441 536870912 3 2 536870912 268435456 hp762789 hp708845 hp762790 hp762791 hp708848

noncomputable def hp762793 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 508370441) (BSN.sinEvenQ 536870912) 0 2 hp762789 hp708845 hp762790 rfl rfl rfl

noncomputable def hp762794 := hp762792 hp762790 435733240 rfl rfl rfl rfl rfl rfl rfl rfl (hp762793 rfl)

noncomputable def hp762795 := @BSN.binarySplit_of_base2 (BSN.sinOddP 508370441) (BSN.sinOddQ 536870912) 0 2 hp762791 hp708848 hp762790 rfl rfl rfl

noncomputable def hp762796 := nat_lit 21508484339378747434326102651885275939113500601524157345469209148743526722548125970954559343699412825064430040481

noncomputable def hp762797 := nat_lit 3794196963526675083109299041657425058097887695376979089791732218294201377566091989620358006846780084778401

noncomputable def hp762798 := nat_lit 130387682303463905641971895384097110372870664659084743364410544762050864814239217317126789507375392197514235409825

noncomputable def hp762799 := BSN.cos_dyadic_bound_f 628434457 536870912 4 3 536870912 268435456 hp762796 hp716712 hp762797 hp762798 hp716714

noncomputable def hp762800 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 628434457) (BSN.cosEvenQ 536870912) 0 3 hp762796 hp716712 hp762797 rfl rfl rfl

noncomputable def hp762801 := hp762799 hp762797 209188986 rfl rfl rfl rfl rfl rfl rfl rfl (hp762800 rfl)

noncomputable def hp762802 := @BSN.binarySplit_of_base3 (BSN.cosOddP 628434457) (BSN.cosOddQ 536870912) 0 3 hp762798 hp716714 hp762797 rfl rfl rfl

noncomputable def hp762803 := hp762788 hd4911 hd4913 hd4915 hd4917 hd4918 (hp762794 (hp762795 rfl) rfl rfl rfl rfl) (hp762801 (hp762802 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762804 := hp762720 (BSN.cos_quad_nat1 197 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 353841821 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl rfl (hp762803 rfl rfl rfl rfl rfl) hp762787

noncomputable def hp762805 := nat_lit 914088416847429677584049536693921

noncomputable def hp762806 := BSN.sin_dyadic_bound_f 173878967 536870912 2 1 536870912 268435456 hp762805 hp708890 hp762805 hp762805 hp708891

noncomputable def hp762807 := @BSN.binarySplit_of_base (BSN.sinEvenP 173878967) (BSN.sinEvenQ 536870912) 0 1 hp762805 hp708890 hp762805 rfl rfl rfl

noncomputable def hp762808 := hp762806 hp762805 170855034 rfl rfl rfl rfl rfl rfl rfl rfl (hp762807 rfl)

noncomputable def hp762809 := @BSN.binarySplit_of_base (BSN.sinOddP 173878967) (BSN.sinOddQ 536870912) 0 1 hp762805 hp708891 hp762805 rfl rfl rfl

noncomputable def hp762810 := nat_lit 5596764404014193451976611149547194746214176349539755901646294210353701120

noncomputable def hp762811 := nat_lit 496220234191215395974193278594046022614972030277001582465108728750336

noncomputable def hp762812 := nat_lit 14657389082515149454059547173982072070333847151221769358892493708222669056

noncomputable def hp762813 := BSN.sin_dyadic_bound_f 386330778 536870912 3 2 536870912 268435456 hp762810 hp708845 hp762811 hp762812 hp708848

noncomputable def hp762814 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 386330778) (BSN.sinEvenQ 536870912) 0 2 hp762810 hp708845 hp762811 rfl rfl rfl

noncomputable def hp762815 := hp762813 hp762811 353841821 rfl rfl rfl rfl rfl rfl rfl rfl (hp762814 rfl)

noncomputable def hp762816 := @BSN.binarySplit_of_base2 (BSN.sinOddP 386330778) (BSN.sinOddQ 536870912) 0 2 hp762812 hp708848 hp762811 rfl rfl rfl

noncomputable def hp762817 := hp762804 hd4920 hd4922 hd4924 hd4926 hd4918 (hp762808 (hp762809 rfl) rfl rfl rfl rfl) (hp762815 (hp762816 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762818 := hp762715 (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 115740752 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl rfl (hp762817 rfl rfl rfl rfl rfl) hp762787

noncomputable def hp762819 := nat_lit 1042029082682996649919855384426334046157604670387279772980416626745737216

noncomputable def hp762820 := nat_lit 55735982674413968651218325904945615010572022407432928265960738062336

noncomputable def hp762821 := nat_lit 3125975776083641121822263716627192247242792867117024453084717958761086976

noncomputable def hp762822 := BSN.cos_dyadic_bound_f 293945596 536870912 3 2 536870912 268435456 hp762819 hp708868 hp762820 hp762821 hp708870

noncomputable def hp762823 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 293945596) (BSN.cosEvenQ 536870912) 0 2 hp762819 hp708868 hp762820 rfl rfl rfl

noncomputable def hp762824 := hp762822 hp762820 458391159 rfl rfl rfl rfl rfl rfl rfl rfl (hp762823 rfl)

noncomputable def hp762825 := @BSN.binarySplit_of_base2 (BSN.cosOddP 293945596) (BSN.cosOddQ 536870912) 0 2 hp762821 hp708870 hp762820 rfl rfl rfl

noncomputable def hp762826 := nat_lit 38483325836544829115003193525694270245021250457620104815915224978931688030983306104863958125147801945905396275041

noncomputable def hp762827 := nat_lit 21675180644799627080780897159395682888240266425450480285061201235182368488540422665847930531757110918993761

noncomputable def hp762828 := nat_lit 233155089641309160184748309044616442186016070347719051680724025991555435469785583929850930344637817528284239714145

noncomputable def hp762829 := BSN.cos_dyadic_bound_f 726658281 536870912 4 3 536870912 268435456 hp762826 hp716712 hp762827 hp762828 hp716714

noncomputable def hp762830 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 726658281) (BSN.cosEvenQ 536870912) 0 3 hp762826 hp716712 hp762827 rfl rfl rfl

noncomputable def hp762831 := hp762829 hp762827 115740752 rfl rfl rfl rfl rfl rfl rfl rfl (hp762830 rfl)

noncomputable def hp762832 := @BSN.binarySplit_of_base3 (BSN.cosOddP 726658281) (BSN.cosOddQ 536870912) 0 3 hp762828 hp716714 hp762827 rfl rfl rfl

noncomputable def hp762833 := hp762818 hd4928 hd4930 hd4932 hd4934 hd4918 (hp762824 (hp762825 rfl) rfl rfl rfl rfl) (hp762831 (hp762832 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762834 := hp762710 (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 374189525 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl rfl (hp762833 rfl rfl rfl rfl rfl) hp762787

noncomputable def hp762835 := nat_lit 665626340474815682283198914560000

noncomputable def hp762836 := BSN.sin_dyadic_bound_f 160622960 536870912 2 1 536870912 268435456 hp762835 hp708890 hp762835 hp762835 hp708891

noncomputable def hp762837 := @BSN.binarySplit_of_base (BSN.sinEvenP 160622960) (BSN.sinEvenQ 536870912) 0 1 hp762835 hp708890 hp762835 rfl rfl rfl

noncomputable def hp762838 := hp762836 hp762835 158237413 rfl rfl rfl rfl rfl rfl rfl rfl (hp762837 rfl)

noncomputable def hp762839 := @BSN.binarySplit_of_base (BSN.sinOddP 160622960) (BSN.sinOddQ 536870912) 0 1 hp762835 hp708891 hp762835 rfl rfl rfl

noncomputable def hp762840 := nat_lit 4741320311143097170595242870641455275923059235547474941387503832716190625

noncomputable def hp762841 := nat_lit 1153479011911616211436942556907717657644540638570745211963261375390625

noncomputable def hp762842 := nat_lit 14221653975405468279362854726810550392453888625365283333738584975397790625

noncomputable def hp762843 := BSN.cos_dyadic_bound_f 429290435 536870912 3 2 536870912 268435456 hp762840 hp708868 hp762841 hp762842 hp708870

noncomputable def hp762844 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 429290435) (BSN.cosEvenQ 536870912) 0 2 hp762840 hp708868 hp762841 rfl rfl rfl

noncomputable def hp762845 := hp762843 hp762841 374189525 rfl rfl rfl rfl rfl rfl rfl rfl (hp762844 rfl)

noncomputable def hp762846 := @BSN.binarySplit_of_base2 (BSN.cosOddP 429290435) (BSN.cosOddQ 536870912) 0 2 hp762842 hp708870 hp762841 rfl rfl rfl

noncomputable def hp762847 := hp762834 hd4936 hd4938 hd4940 hd4942 hd4918 (hp762838 (hp762839 rfl) rfl rfl rfl rfl) (hp762845 (hp762846 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762848 := hp762705 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 509124754 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl rfl (hp762847 rfl rfl rfl rfl rfl) hp762787

noncomputable def hp762849 := nat_lit 54209774180221287350407460041527562051642485573922813935081740052544919324006095030984300499646512941180023279616

noncomputable def hp762850 := nat_lit 60439225135401256209161877824270834011757402267342487308043286219389444732962407210189899068164870895374336

noncomputable def hp762851 := nat_lit 328257570687597439336084667052645183532057412744587681490802094062400149997414563112139479869044310760841183825920

noncomputable def hp762852 := BSN.cos_dyadic_bound_f 791486006 536870912 4 3 536870912 268435456 hp762849 hp716712 hp762850 hp762851 hp716714

noncomputable def hp762853 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 791486006) (BSN.cosEvenQ 536870912) 0 3 hp762849 hp716712 hp762850 rfl rfl rfl

noncomputable def hp762854 := hp762852 hp762850 51748382 rfl rfl rfl rfl rfl rfl rfl rfl (hp762853 rfl)

noncomputable def hp762855 := @BSN.binarySplit_of_base3 (BSN.cosOddP 791486006) (BSN.cosOddQ 536870912) 0 3 hp762851 hp716714 hp762850 rfl rfl rfl

noncomputable def hp762856 := nat_lit 72210088546780790034085493706945203844583497887584943575872811386780052973255573564807235941459316856433348579521

noncomputable def hp762857 := nat_lit 8176640506598674132750814116248386195584354845064009140231485800279412993288277466287313394257607672598721

noncomputable def hp762858 := nat_lit 360871569359998986951975421003225693472618773196151774677505526235258351454324252217522826564730411785711781286081

noncomputable def hp762859 := BSN.sin_dyadic_bound_f 669958511 536870912 4 3 536870912 268435456 hp762856 hp642702 hp762857 hp762858 hp642705

noncomputable def hp762860 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 669958511) (BSN.sinEvenQ 536870912) 0 3 hp762856 hp642702 hp762857 rfl rfl rfl

noncomputable def hp762861 := hp762859 hp762857 509124754 rfl rfl rfl rfl rfl rfl rfl rfl (hp762860 rfl)

noncomputable def hp762862 := @BSN.binarySplit_of_base3 (BSN.sinOddP 669958511) (BSN.sinOddQ 536870912) 0 3 hp762858 hp642705 hp762857 rfl rfl rfl

noncomputable def hp762863 := hp762848 hd4944 hd4946 hd4961 hd4963 hd4918 (hp762854 (hp762855 rfl) rfl rfl rfl rfl) (hp762861 (hp762862 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762864 := @hp762700 211373 268435456 (hp762863 rfl rfl rfl rfl rfl) (hp762863 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp762865 := @hp762698 Bool.true 126666593 67108864 211373 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 871112 1000)) (Enclosure.sfrac Bool.false 871112 1000) 11) hp762864

noncomputable def hp762866 := @Enclosure.Real.IsNear.mulLit_tf hp762689 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1))) 9778593 33554432 1

noncomputable def hp762867 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp762688 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762868 := @hp762867 1 1 0 1 9778593 33554432 1 33554432 9778593 33554432 1

noncomputable def hp762869 := @Enclosure.Real.IsNear.of_eq (hp762688 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762870 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 871112 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762871 := @hp762869 (@Inv.inv Real Real.instInv (Real.sqrt hp762690)) Bool.false 9778593 33554432 1 33554432 (hp762870 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 871112 1000) 871112 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000))))

noncomputable def hp762872 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp762690)) Bool.false 19557186 67108864 2 67108864 9778593 33554432

noncomputable def hp762873 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp762690) Bool.false 230278512 67108864 6 67108864 14392407 4194304 3 33554432

noncomputable def hp762874 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 871112 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762875 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 871112 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762876 := @hp762875 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 871112 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 1163011504523

noncomputable def hp762877 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 871112 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 871112 1000 0

noncomputable def hp762878 := @hp762877 1 10680707 67108864 1 67108864 1163011504523 8388608000 108889 8388608000 (Enclosure.Real.IsNear.const Bool.false 871112 1000) hd4949

noncomputable def hp762879 := @hp762876 8388608000 108889 8388608000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 871112 1000) 871112 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000))) (hp762878 rfl)

noncomputable def hp762880 := @hp762874 1163011504523 8388608000 108889 8388608000 395090808 395090846 33554432 hp762879 rfl rfl rfl

noncomputable def hp762881 := @Enclosure.Real.IsNear.recentre' hp762690 Bool.false 790181654 67108864 38 67108864 395090827 33554432 19 33554432 (hp762880 rfl rfl rfl)

noncomputable def hp762882 := @Enclosure.Real.IsNear.sqrt_image hp762690 395090827 33554432 19 33554432 115139253 115139259 33554432 (hp762881 rfl) rfl rfl

noncomputable def hp762883 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp762690) 14392407 4194304 3 33554432 9778592 9778594 33554432 (hp762873 (hp762882 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp762884 := @hp762868 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp762871 (@hp762872 1 33554432 (hp762883 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp762885 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762886 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp762887 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1))) (hp762885 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762886 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp762888 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 871112 1000) 871112 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl

noncomputable def hp762889 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762890 := @hp762889 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762886 (Enclosure.sfrac Bool.false 1 16)))) 435483793

noncomputable def hp762891 := @hp762890 67108864 10367 67108864 1360295 16777216 209687777 22837985280000 592386426198935 1125899906842624 1227937694112373 17029236090994688000

noncomputable def hp762892 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp762893 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)))) 10341601

noncomputable def hp762894 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp762895 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 326626047) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp762896 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1))) Bool.false 22984264777319326826625

noncomputable def hp762897 := nat_lit 512735432995107087808568773

noncomputable def hp762898 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp762899 := @Enclosure.Real.IsNear.subLit_ff_p hp762690 (Enclosure.sfrac Bool.false 11 1) 395090827 33554432 19 33554432 11 1 0

noncomputable def hp762900 := @hp762898 500000000000000 25992075 33554432 19 33554432 22984264777319326826625 4722366482869645213696 hp762897 hp682805 hd4948 (@hp762899 1 25992075 25992075 33554432 19 33554432 (hp762881 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762901 := @hp762895 326626047 67108864 15 4194304 Bool.false 10341601 67108864 1 10890000 (@hp762896 4722366482869645213696 hp762897 hp682805 326626047 67108864 15 4194304 (hp762900 rfl) rfl) (Enclosure.sfrac_false_div 326626047 67108864)

noncomputable def hp762902 := nat_lit 1496344510242278420250624

noncomputable def hp762903 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 326626047) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp762902) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp762904 := BSN.sin_reduce_arg_pos_rat_q3 326626047 67108864 226375608064910080 72057594037927936 0 hp762902 hp617687 rfl rfl rfl rfl

noncomputable def hp762905 := nat_lit 204459444414539838405898187193998989912336

noncomputable def hp762906 := BSN.sin_dyadic_bound_f 21264334438 137438953472 2 1 67108864 21801270 hp762905 hp749778 hp762905 hp762905 hp749779

noncomputable def hp762907 := @BSN.binarySplit_of_base (BSN.sinEvenP 21264334438) (BSN.sinEvenQ 137438953472) 0 1 hp762905 hp749778 hp762905 rfl rfl rfl

noncomputable def hp762908 := hp762906 hp762905 10341601 rfl rfl rfl rfl rfl rfl rfl rfl (hp762907 rfl)

noncomputable def hp762909 := @BSN.binarySplit_of_base (BSN.sinOddP 21264334438) (BSN.sinOddQ 137438953472) 0 1 hp762905 hp749779 hp762905 rfl rfl rfl

noncomputable def hp762910 := @BSN.sin_arg_round Bool.false 10341601 67108864 hp762902 hp617687 21264334438 137438953472 21801270 21780000 (hp762908 (hp762909 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp762911 := hp762903 10341601 67108864 0 1000000000000000 21780000 10890000 hp762904 BSN.pi_near_15 hp762910 rfl rfl

noncomputable def hp762912 := @hp762893 67108864 10471519 2854748160000 217736713 217747080 33554432 (@hp762894 10341601 67108864 167544304 45675970560000 10341601 67108864 10471519 2854748160000 (hp762901 (hp762911 rfl rfl) rfl rfl) rfl)

noncomputable def hp762913 := @hp762892 Bool.false 435483793 67108864 10367 67108864 435483793 67108864 10367 67108864 (hp762912 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp762914 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762886 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp762915 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762886 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 24991799)) (@Nat.cast Real Real.instNatCast 16777216)) Bool.true

noncomputable def hp762916 := nat_lit 236040868956672021344582950645

noncomputable def hp762917 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762886 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp762916

noncomputable def hp762918 := nat_lit 43858671604725389569073641516210061

noncomputable def hp762919 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp762886 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp762920 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp762921 := @hp762920 (Enclosure.sfrac Bool.false 1 16) 196561350320775 1125899906842624 1625233419 1125899906842624 1 16 0

noncomputable def hp762922 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)) 675587962805625

noncomputable def hp762923 := @hp762922 1125899906842624 987699211 1125899906842624 25992075 33554432 19 33554432 6595504463166622924800 196561350320775 1125899906842624 1625233419

noncomputable def hp762924 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)) 25992075 33554432 19

noncomputable def hp762925 := @hp762924 33554432 25992075 33554432 19 33554432 675587962805625 1125899906842624 987699211 1125899906842624 (@hp762899 1 25992075 25992075 33554432 19 33554432 (hp762881 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762926 := hp762925 (@hp762899 1 25992075 25992075 33554432 19 33554432 (hp762881 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762927 := @hp762923 1125899906842624 (hp762926 rfl) (@hp762899 1 25992075 25992075 33554432 19 33554432 (hp762881 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp762928 := @hp762919 500000000000000 266930094498439 1125899906842624 1625233419 1125899906842624 hp762916 hp682141 hp762918 hp682143 hd4948 (@hp762921 1 4270881511975024 266930094498439 1125899906842624 1625233419 1125899906842624 (hp762927 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp762929 := @hp762915 24991799 16777216 305 33554432 Bool.false 2720590 33554432 1 10890000 (@hp762917 hp682141 hp762918 hp682143 24991799 16777216 305 33554432 (hp762928 rfl) rfl) (Enclosure.sfrac_true_div 24991799 16777216)

noncomputable def hp762930 := nat_lit 49016974984256732333197677148098731335385823125395237408263804370214270313578270071001357184481

noncomputable def hp762931 := nat_lit 59370435149405757834525482322979772384644592428160316470606052887105140770844397097938401

noncomputable def hp762932 := nat_lit 296790005375554373185871495607938758203923647609197064196889178002512283999743886790454837997025

noncomputable def hp762933 := BSN.cos_dyadic_bound_f 24991799 16777216 4 3 33554432 10890000 hp762930 hp633087 hp762931 hp762932 hp633090

noncomputable def hp762934 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 24991799) (BSN.cosEvenQ 16777216) 0 3 hp762930 hp633087 hp762931 rfl rfl rfl

noncomputable def hp762935 := hp762933 hp762931 2720590 rfl rfl rfl rfl rfl rfl rfl rfl (hp762934 rfl)

noncomputable def hp762936 := @BSN.binarySplit_of_base3 (BSN.cosOddP 24991799) (BSN.cosOddQ 16777216) 0 3 hp762932 hp633090 hp762931 rfl rfl rfl

noncomputable def hp762937 := hp762929 (BSN.cos_neg_of_bound 24991799 16777216 Bool.false 2720590 33554432 1 10890000 (hp762935 (hp762936 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp762938 := hp762891 hp762913 (@hp762914 2720590 33554432 3355004432 365407764480000 1360295 16777216 209687777 22837985280000 (hp762937 rfl) rfl)

noncomputable def hp762939 := @hp762866 33554432 592386426198935 1125899906842624 1227937694112373 17029236090994688000 5792705760523922398455 37778931862957161709568 12016464012717344835437 hp751106 (hp762884 rfl) (@hp762887 Bool.false 592386426198935 1125899906842624 1227937694112373 17029236090994688000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762690 (Enclosure.sfrac Bool.false 11 1)) (hp762888 rfl (hp762693 rfl rfl))) (hp762938 rfl))

noncomputable def hp762940 := @hp762687 461956554045444868163437 hp751106 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 871112 1000))) (@hp762692 461956554045444868163437 hp751106 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 871112 1000) 11 (hp762693 rfl rfl)) (@hp762696 461956554045444868163437 hp751106 hp762865 (hp762939 rfl) rfl rfl))

theorem hd5060 : hp762686 hp751106 := hp762940

noncomputable def hp762941 := nat_lit 13788224904091929016556747

noncomputable def hp762942 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 872386 1000)) Bool.false 41282108026741643214671 75557863725914323419136 hp762941

noncomputable def hp762943 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 872386 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 872386 1000)) Bool.false 41282108026741643214671 75557863725914323419136

noncomputable def hp762944 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 872386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762945 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp762944 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp762946 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 872386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp762947 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp762945 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp762948 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 872386 1000)) hp762947 Bool.false 41282108026741643214671 75557863725914323419136

noncomputable def hp762949 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 872386 1000) 872386 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl

noncomputable def hp762950 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp762945 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp762951 := nat_lit 11081581492799653190519515774976

noncomputable def hp762952 := @hp762950 104746933 268435456 211685 268435456 11798467500053998796623 75557863725914323419136 270097996883639531756747 hp741590 hp762951 41282108026741643214671 75557863725914323419136

noncomputable def hp762953 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) 11)

noncomputable def hp762954 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) 11) hp762953

noncomputable def hp762955 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) 11)

noncomputable def hp762956 := @hp762955 104746933 536870912 211685 536870912 104746933 536870912 211685 536870912 112471162897825792 104746933 268435456

noncomputable def hp762957 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp762958 := hp762957 BSN.quadSignPos 9 10 11 872386 1000 186 239 536870912 268435456 9007199254740992

noncomputable def hp762959 := hp762958 Bool.false 920899618987 3975 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp762960 := hp762959 Bool.false 7296691 181726 Bool.true 679501038 Bool.true 623163186 28296951008113761 1 Bool.false 161283712

noncomputable def hp762961 := hp762960 Bool.true Bool.false 492361701 Bool.false Bool.false 104746933 211685 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 161283712 536870912) BSN.abs_quadSignPos

noncomputable def hp762962 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp762963 := hp762962 BSN.quadSignPos 7 8 9 872386 1000 62 128 536870912 268435456 9007199254740992

noncomputable def hp762964 := hp762963 Bool.false 920899618987 3975 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp762965 := hp762964 Bool.true 116776440 148415 Bool.true 739328566 Bool.true 245241648 28296951008113761 1 Bool.false 103337323

noncomputable def hp762966 := hp762965 Bool.true Bool.false 481825188 Bool.false Bool.false 7296691 181726 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 103337323 536870912) BSN.abs_quadSignPos

noncomputable def hp762967 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp762968 := hp762967 BSN.quadSignPos 5 6 7 872386 1000 96 11 536870912 268435456 9007199254740992

noncomputable def hp762969 := hp762968 Bool.false 920899618987 3975 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp762970 := hp762969 Bool.true 240015174 110290 Bool.false 755321780 Bool.false 239284632 28296951008113761 1 Bool.false 87599643

noncomputable def hp762971 := hp762970 Bool.false Bool.false 231440610 Bool.false Bool.true 116776440 148415 BSN.abs_quadSignPos (BSN.cos_quad_nat0 96 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 87599643 536870912) BSN.abs_quadSignPos

noncomputable def hp762972 := hp762962 BSN.quadSignNeg 3 4 5 872386 1000 322 198 536870912 268435456 9007199254740992

noncomputable def hp762973 := hp762972 Bool.false 920899618987 3975 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp762974 := hp762973 Bool.false 259377262 65188 Bool.false 69267709 Bool.false 129095237 28296951008113761 1 Bool.false 532408607

noncomputable def hp762975 := hp762974 Bool.true Bool.false 521424522 Bool.true Bool.true 240015174 110290 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 322 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 532408607 536870912) BSN.abs_quadSignNeg

noncomputable def hp762976 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp762977 := hp762976 BSN.quadSignNeg 1 2 3 872386 1000 707 481 536870912 268435456 9007199254740992

noncomputable def hp762978 := hp762977 Bool.false 920899618987 3975 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp762979 := hp762978 Bool.false 536870872 4034 Bool.false 34538660 Bool.false 720590114 28296951008113761 1 Bool.false 34514840

noncomputable def hp762980 := hp762979 Bool.false Bool.false 522904900 Bool.true Bool.false 259377262 65188 BSN.abs_quadSignPos (BSN.cos_quad_nat3 707 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 34514840 536870912) BSN.abs_quadSignNeg

noncomputable def hp762981 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) 1) Bool.false

noncomputable def hp762982 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)))

noncomputable def hp762983 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000))) Bool.false 67108859 67108864

noncomputable def hp762984 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 115112452373) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 115112452373 67108864

noncomputable def hp762985 := nat_lit 957739230661207916825364977288597723277845293815897322307

noncomputable def hp762986 := nat_lit 558347862917436365062644517277034455844526932099072000

noncomputable def hp762987 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) Bool.false hp762985 hp762986 22008920482847514413

noncomputable def hp762988 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 872386 4000) (Real.log (Enclosure.sfrac Bool.false 3044230331984 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1744772))))))

noncomputable def hp762989 := nat_lit 242540928568249243215426138004480000

noncomputable def hp762990 := nat_lit 1269536057674114010893946481876433735680

noncomputable def hp762991 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp762988 (Enclosure.sfrac Bool.false 872386 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 872386 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp762989 hp762990)) Bool.false

noncomputable def hp762992 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 872386 1000) 872386 1000 3044230331984 16000000 1744772

noncomputable def hp762993 := hp762992 4000 2000 hp762989 hp762990 (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl rfl rfl rfl

noncomputable def hp762994 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp762988 (Enclosure.sfrac Bool.false 872386 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 872386 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp762989 hp762990) 15450133542871762396327 9007199254740992000

noncomputable def hp762995 := nat_lit 19614499443941538136583474734870481372730271617349577160847360

noncomputable def hp762996 := @hp762994 22008920482847514413 hp740893 hp762989 hp762990 0 1 hp762995 hp762985 hp762986 22008920482847514413 hp740893

noncomputable def hp762997 := @Enclosure.Real.IsNear.subLit_ff_p (hp762988 (Enclosure.sfrac Bool.false 872386 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 872386 2000) (Real.log Real.pi)) 3989527350432547876283 1801439850948198400 1834140191837753 726000000000000000000

noncomputable def hp762998 := nat_lit 103684091071041927209542274252800

noncomputable def hp762999 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 872386 4000) (Real.log (Enclosure.sfrac Bool.false 3044230331984 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1744772))))))

noncomputable def hp763000 := @hp762999 (Enclosure.sfrac Bool.false 872386 2000) 23876514016685976904871 9007199254740992000 1834140191837753 726000000000000000000 872386 2000 0

noncomputable def hp763001 := nat_lit 39895273504325478762830000

noncomputable def hp763002 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 872386 4000) (Real.log (Enclosure.sfrac Bool.false 3044230331984 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1744772))))) 23880049844991427540871

noncomputable def hp763003 := nat_lit 53765129814226695151016868891232043008

noncomputable def hp763004 := @hp763002 9007199254740992000 5452420575241009 2178000000000000000000 883957076362659 2251799813685248 200000001089 8712000000000000000 hp763003 23876514016685976904871 9007199254740992000 1834140191837753

noncomputable def hp763005 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 872386 4000) (Real.log (Enclosure.sfrac Bool.false 3044230331984 16000000)) 872386 4000 0 1 54746522399468647 4503599627370496

noncomputable def hp763006 := nat_lit 117567261637724643321184256

noncomputable def hp763007 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3044230331984) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp763006 hp617687

noncomputable def hp763008 := BSN.log_rat_reduce_isNear 3044230331984 16000000 17 6088460663968 4194304000000 100037269 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp763009 := nat_lit 134160139629713081843584328538341481542977589026414005996714873260040801421478284299180050337629215444430478671481966417199780331520

noncomputable def hp763010 := nat_lit 1549112840213492251999885411983454047330283620657169671169005026283354740501800546856610118470392729171449770788202635193539887104

noncomputable def hp763011 := nat_lit 548644227777287675500799685037699975255819693785604345793541253371173729160018308227589212163828102235682620408598961848320

noncomputable def hp763012 := BSN.log_dyadic_bound 947078331984 5141382331984 6 5 hp763009 268435456 87120000 hp763010 hp763011 100037269 6088460663968

noncomputable def hp763013 := hp763012 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp763014 := @BSN.binarySplit_of_base5 (BSN.artanhP 947078331984) (BSN.artanhQ 5141382331984) 0 5 hp763010 hp763009 hp763011 rfl rfl rfl

noncomputable def hp763015 := hp763008 rfl rfl rfl rfl (hp763013 (hp763014 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp763016 := @hp763005 12500018513 1089000000000000000 23880049844991427540871 9007199254740992000 5452420575241009 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 872386 4000) (BSN.isNear_log_sfrac 3044230331984 16000000 54746522399468647 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp763007 1000001481040000 87120000000000000000000 54746522399468647 4503599627370496 12500018513 1089000000000000000 (hp763015 rfl rfl rfl) rfl)) rfl

noncomputable def hp763017 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1744772)))) 1 4

noncomputable def hp763018 := @hp763017 0 1 883957076362659 562949953421312 200000001089 2178000000000000000 883957076362659 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp763019 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1744772))) 884279719003555 562949953421312 1

noncomputable def hp763020 := @hp763019 2000000000000000 19231 33554432 1 10890000 29660677609729648754688 883957076362659 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp763021 := BSN.arctan_dyadic_bound_f 1000 1744772 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp763022 := hp763021 1 19231 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1744772) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1744772) 0 0 rfl)

noncomputable def hp763023 := hp763018 (hp763020 (hp763022 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp763024 := @hp762997 16754505072873 33554432000 1308579 268435456000 hp762998 15450133542871762396327 9007199254740992000 22008920482847514413 hp740893 (@hp763000 1 hp763001 3989527350432547876283 1801439850948198400 1834140191837753 726000000000000000000 (@hp763004 726000000000000000000 hp763016 hp763023 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 872386 2000) rfl rfl)

noncomputable def hp763025 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 872386 2000) (Real.log Real.pi) 872386 2000 0 1 38410761 33554432

noncomputable def hp763026 := hp763024 (@hp763025 3 268435456 16754505072873 33554432000 1308579 268435456000 (Enclosure.Real.IsNear.const Bool.false 872386 2000) hd4909 rfl) rfl

noncomputable def hp763027 := @hp762987 hp740893 115112452373 67108864 249 33554432 (@hp762991 hp762985 hp762986 22008920482847514413 hp740893 (hp762993 rfl rfl rfl rfl rfl) (hp762996 (hp763026 rfl) (Enclosure.Real.IsNear.const Bool.true hp762989 hp762990) rfl rfl)) rfl

noncomputable def hp763028 := nat_lit 15188128658915656346894336

noncomputable def hp763029 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 115112452373) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp763028) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp763030 := BSN.sin_reduce_arg_pos_rat_q3 115112452373 67108864 226375608064910080 72057594037927936 272 hp763028 hp617687 rfl rfl rfl rfl

noncomputable def hp763031 := nat_lit 14366420775415975924355352423553794103203125831848091330167891021448389739482386328633355558027461620740048374730066904209948907923473147808161

noncomputable def hp763032 := nat_lit 10221005035898252590040275820248122912968537151380264538632802382890636501440460594424534776798163947001110773940231812385779718111545761

noncomputable def hp763033 := nat_lit 71742929975728791334311630184176514521530657318771004288414749040671570853454297126316854410162205048671839217706615156137806205190589370517921

noncomputable def hp763034 := BSN.sin_dyadic_bound_f 215836289767 137438953472 4 3 67108864 21801270 hp763031 hp737934 hp763032 hp763033 hp737937

noncomputable def hp763035 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215836289767) (BSN.sinEvenQ 137438953472) 0 3 hp763031 hp737934 hp763032 rfl rfl rfl

noncomputable def hp763036 := hp763034 hp763032 67108859 rfl rfl rfl rfl rfl rfl rfl rfl (hp763035 rfl)

noncomputable def hp763037 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215836289767) (BSN.sinOddQ 137438953472) 0 3 hp763033 hp737937 hp763032 rfl rfl rfl

noncomputable def hp763038 := @BSN.sin_arg_round Bool.false 67108859 67108864 hp763028 hp617687 215836289767 137438953472 21801270 21780000 (hp763036 (hp763037 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763039 := hp763029 67108859 67108864 272 1000000000000000 21780000 10890000 hp763030 BSN.pi_near_15 hp763038 rfl rfl

noncomputable def hp763040 := @hp762984 249 33554432 Bool.false 67108859 67108864 1 10890000 hp763027 (Enclosure.sfrac_false_div 115112452373 67108864) (hp763039 rfl rfl) rfl

noncomputable def hp763041 := @hp762981 67108859 67108864 171572777 22837985280000 536870872 536870912 4034 536870912 (@hp762982 Bool.false 67108859 67108864 171572777 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000)) (@hp762983 2745164432 365407764480000 67108859 67108864 171572777 22837985280000 (hp763040 rfl) rfl))

noncomputable def hp763042 := @hp762987 hp740893 920899618987 536870912 3975 536870912 (@hp762991 hp762985 hp762986 22008920482847514413 hp740893 (hp762993 rfl rfl rfl rfl rfl) (hp762996 (hp763026 rfl) (Enclosure.Real.IsNear.const Bool.true hp762989 hp762990) rfl rfl)) rfl

noncomputable def hp763043 := hp762980 (BSN.cos_quad_nat1 481 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 522904900 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl rfl (hp763041 rfl) hp763042

noncomputable def hp763044 := nat_lit 1423055823100498309655539360000

noncomputable def hp763045 := BSN.sin_dyadic_bound_f 34538660 536870912 2 1 536870912 268435456 hp763044 hp708890 hp763044 hp763044 hp708891

noncomputable def hp763046 := @BSN.binarySplit_of_base (BSN.sinEvenP 34538660) (BSN.sinEvenQ 536870912) 0 1 hp763044 hp708890 hp763044 rfl rfl rfl

noncomputable def hp763047 := hp763045 hp763044 34514840 rfl rfl rfl rfl rfl rfl rfl rfl (hp763046 rfl)

noncomputable def hp763048 := @BSN.binarySplit_of_base (BSN.sinOddP 34538660) (BSN.sinOddQ 536870912) 0 1 hp763044 hp708891 hp763044 rfl rfl rfl

noncomputable def hp763049 := nat_lit 96666767867721033730514431558432768280768258614134667269461366703792546824426657352073330272705352749407816912896

noncomputable def hp763050 := nat_lit 19600159037459977294766912343852034696758168432493390109704826633403235708697059822227981631456349749252096

noncomputable def hp763051 := nat_lit 483013436989417937894484524829834576313330634082195706973548395944451667688237159913181149438749376445049815699456

noncomputable def hp763052 := BSN.sin_dyadic_bound_f 720590114 536870912 4 3 536870912 268435456 hp763049 hp642702 hp763050 hp763051 hp642705

noncomputable def hp763053 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 720590114) (BSN.sinEvenQ 536870912) 0 3 hp763049 hp642702 hp763050 rfl rfl rfl

noncomputable def hp763054 := hp763052 hp763050 522904900 rfl rfl rfl rfl rfl rfl rfl rfl (hp763053 rfl)

noncomputable def hp763055 := @BSN.binarySplit_of_base3 (BSN.sinOddP 720590114) (BSN.sinOddQ 536870912) 0 3 hp763051 hp642705 hp763050 rfl rfl rfl

noncomputable def hp763056 := hp763043 hd4911 hd4913 hd4915 hd4917 hd4918 (hp763047 (hp763048 rfl) rfl rfl rfl rfl) (hp763054 (hp763055 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763057 := hp762975 (BSN.cos_quad_nat2 198 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 521424522 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl rfl (hp763056 rfl rfl rfl rfl rfl) hp763042

noncomputable def hp763058 := nat_lit 23020952835243466347296431559761

noncomputable def hp763059 := BSN.cos_dyadic_bound_f 69267709 536870912 2 1 536870912 268435456 hp763058 hp708767 hp763058 hp763058 hp708768

noncomputable def hp763060 := @BSN.binarySplit_of_base (BSN.cosEvenP 69267709) (BSN.cosEvenQ 536870912) 0 1 hp763058 hp708767 hp763058 rfl rfl rfl

noncomputable def hp763061 := hp763059 hp763058 532408607 rfl rfl rfl rfl rfl rfl rfl rfl (hp763060 rfl)

noncomputable def hp763062 := @BSN.binarySplit_of_base (BSN.cosOddP 69267709) (BSN.cosOddQ 536870912) 0 1 hp763058 hp708768 hp763058 rfl rfl rfl

noncomputable def hp763063 := nat_lit 277741563938802719419272433096561

noncomputable def hp763064 := BSN.cos_dyadic_bound_f 129095237 536870912 2 1 536870912 268435456 hp763063 hp708767 hp763063 hp763063 hp708768

noncomputable def hp763065 := @BSN.binarySplit_of_base (BSN.cosEvenP 129095237) (BSN.cosEvenQ 536870912) 0 1 hp763063 hp708767 hp763063 rfl rfl rfl

noncomputable def hp763066 := hp763064 hp763063 521424522 rfl rfl rfl rfl rfl rfl rfl rfl (hp763065 rfl)

noncomputable def hp763067 := @BSN.binarySplit_of_base (BSN.cosOddP 129095237) (BSN.cosOddQ 536870912) 0 1 hp763063 hp708768 hp763063 rfl rfl rfl

noncomputable def hp763068 := hp763057 hd4920 hd4922 hd4924 hd4926 hd4918 (hp763061 (hp763062 rfl) rfl rfl rfl rfl) (hp763066 (hp763067 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763069 := hp762971 (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 231440610 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl rfl (hp763068 rfl rfl rfl rfl rfl) hp763042

noncomputable def hp763070 := nat_lit 44939134295397754672471797503338807029452595185232514161168691148684430927653776525856447214514150771523584000000

noncomputable def hp763071 := nat_lit 34481336847683703329222887848644658924233961629361082555499894226184795064564729874543376470016000000000000

noncomputable def hp763072 := nat_lit 272207699458930849822481356078069133342856090490441354199387624055713605185477061549455372078529414111795609600000

noncomputable def hp763073 := BSN.cos_dyadic_bound_f 755321780 536870912 4 3 536870912 268435456 hp763070 hp716712 hp763071 hp763072 hp716714

noncomputable def hp763074 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 755321780) (BSN.cosEvenQ 536870912) 0 3 hp763070 hp716712 hp763071 rfl rfl rfl

noncomputable def hp763075 := hp763073 hp763071 87599643 rfl rfl rfl rfl rfl rfl rfl rfl (hp763074 rfl)

noncomputable def hp763076 := @BSN.binarySplit_of_base3 (BSN.cosOddP 755321780) (BSN.cosOddQ 536870912) 0 3 hp763072 hp716714 hp763071 rfl rfl rfl

noncomputable def hp763077 := nat_lit 823618663595954479741450190245399838923307484840134813565369159662960640

noncomputable def hp763078 := nat_lit 10747772284776353975630976774601351872779488134330130642240511410176

noncomputable def hp763079 := nat_lit 2157079098739038761416409000489840699753249388743373691507307981146423296

noncomputable def hp763080 := BSN.sin_dyadic_bound_f 239284632 536870912 3 2 536870912 268435456 hp763077 hp708845 hp763078 hp763079 hp708848

noncomputable def hp763081 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 239284632) (BSN.sinEvenQ 536870912) 0 2 hp763077 hp708845 hp763078 rfl rfl rfl

noncomputable def hp763082 := hp763080 hp763078 231440610 rfl rfl rfl rfl rfl rfl rfl rfl (hp763081 rfl)

noncomputable def hp763083 := @BSN.binarySplit_of_base2 (BSN.sinOddP 239284632) (BSN.sinOddQ 536870912) 0 2 hp763079 hp708848 hp763078 rfl rfl rfl

noncomputable def hp763084 := hp763069 hd4928 hd4930 hd4932 hd4934 hd4918 (hp763075 (hp763076 rfl) rfl rfl rfl rfl) (hp763082 (hp763083 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763085 := hp762966 (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 481825188 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl rfl (hp763084 rfl rfl rfl rfl rfl) hp763042

noncomputable def hp763086 := nat_lit 41244273298657654997266763898174306052612891196680752218054967755446978474965223620230944256826297627921060007936

noncomputable def hp763087 := nat_lit 26671647345871785219904290821184975778770581090808245094364033674432883794819057349151037284212828843872256

noncomputable def hp763088 := nat_lit 249858790974014907083531010930014547094252253213753742682667918403088200990502512797359464794277821438545464463360

noncomputable def hp763089 := BSN.cos_dyadic_bound_f 739328566 536870912 4 3 536870912 268435456 hp763086 hp716712 hp763087 hp763088 hp716714

noncomputable def hp763090 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 739328566) (BSN.cosEvenQ 536870912) 0 3 hp763086 hp716712 hp763087 rfl rfl rfl

noncomputable def hp763091 := hp763089 hp763087 103337323 rfl rfl rfl rfl rfl rfl rfl rfl (hp763090 rfl)

noncomputable def hp763092 := @BSN.binarySplit_of_base3 (BSN.cosOddP 739328566) (BSN.cosOddQ 536870912) 0 3 hp763088 hp716714 hp763087 rfl rfl rfl

noncomputable def hp763093 := nat_lit 504866945733293219801256368219479738453335232788817394740750485433614336

noncomputable def hp763094 := nat_lit 13084399839918224161831928161602200910144437981562182740995427270656

noncomputable def hp763095 := nat_lit 1514574668400199822955445440802116010958185409490489059856769465446301696

noncomputable def hp763096 := BSN.cos_dyadic_bound_f 245241648 536870912 3 2 536870912 268435456 hp763093 hp708868 hp763094 hp763095 hp708870

noncomputable def hp763097 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 245241648) (BSN.cosEvenQ 536870912) 0 2 hp763093 hp708868 hp763094 rfl rfl rfl

noncomputable def hp763098 := hp763096 hp763094 481825188 rfl rfl rfl rfl rfl rfl rfl rfl (hp763097 rfl)

noncomputable def hp763099 := @BSN.binarySplit_of_base2 (BSN.cosOddP 245241648) (BSN.cosOddQ 536870912) 0 2 hp763095 hp708870 hp763094 rfl rfl rfl

noncomputable def hp763100 := hp763085 hd4936 hd4938 hd4940 hd4942 hd4918 (hp763091 (hp763092 rfl) rfl rfl rfl rfl) (hp763098 (hp763099 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763101 := hp762961 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 492361701 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl rfl (hp763100 rfl rfl rfl rfl rfl) hp763042

noncomputable def hp763102 := nat_lit 29410893711250084953729144672718111945431030512107651578762550041511751751511013223915892298212485005073540059136

noncomputable def hp763103 := nat_lit 9689056622679830849048659352411957474519307241837792507155662099827018603364994233681572545001012757139456

noncomputable def hp763104 := nat_lit 178244623331474685615797210025241050525741140585878404537723357173622092388545785209382335433783662974014493429760

noncomputable def hp763105 := BSN.cos_dyadic_bound_f 679501038 536870912 4 3 536870912 268435456 hp763102 hp716712 hp763103 hp763104 hp716714

noncomputable def hp763106 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 679501038) (BSN.cosEvenQ 536870912) 0 3 hp763102 hp716712 hp763103 rfl rfl rfl

noncomputable def hp763107 := hp763105 hp763103 161283712 rfl rfl rfl rfl rfl rfl rfl rfl (hp763106 rfl)

noncomputable def hp763108 := @BSN.binarySplit_of_base3 (BSN.cosOddP 679501038) (BSN.cosOddQ 536870912) 0 3 hp763104 hp716714 hp763103 rfl rfl rfl

noncomputable def hp763109 := nat_lit 54041309411348124498012296919626115991690831021493872969674784604578074330062461430898731168708132245274535530496

noncomputable def hp763110 := nat_lit 3429426254995453057931462465493805680465305172081743528411879258452486465683024560141061167023290702237696

noncomputable def hp763111 := nat_lit 270106326508791827786846114438864884343347978213771657868964907813218156509800525517470118755771777952371416109056

noncomputable def hp763112 := BSN.sin_dyadic_bound_f 623163186 536870912 4 3 536870912 268435456 hp763109 hp642702 hp763110 hp763111 hp642705

noncomputable def hp763113 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 623163186) (BSN.sinEvenQ 536870912) 0 3 hp763109 hp642702 hp763110 rfl rfl rfl

noncomputable def hp763114 := hp763112 hp763110 492361701 rfl rfl rfl rfl rfl rfl rfl rfl (hp763113 rfl)

noncomputable def hp763115 := @BSN.binarySplit_of_base3 (BSN.sinOddP 623163186) (BSN.sinOddQ 536870912) 0 3 hp763111 hp642705 hp763110 rfl rfl rfl

noncomputable def hp763116 := hp763101 hd4944 hd4946 hd4961 hd4963 hd4918 (hp763107 (hp763108 rfl) rfl rfl rfl rfl) (hp763114 (hp763115 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763117 := @hp762956 211685 268435456 (hp763116 rfl rfl rfl rfl rfl) (hp763116 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp763118 := @hp762954 Bool.false 104746933 268435456 211685 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 872386 1000)) (Enclosure.sfrac Bool.false 872386 1000) 11) hp763117

noncomputable def hp763119 := @Enclosure.Real.IsNear.mulLit_tf hp762945 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1))) 9775021 33554432 1

noncomputable def hp763120 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp762944 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763121 := @hp763120 1 1 0 1 9775021 33554432 1 33554432 9775021 33554432 1

noncomputable def hp763122 := @Enclosure.Real.IsNear.of_eq (hp762944 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763123 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 872386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763124 := @hp763122 (@Inv.inv Real Real.instInv (Real.sqrt hp762946)) Bool.false 9775021 33554432 1 33554432 (hp763123 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 872386 1000) 872386 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000))))

noncomputable def hp763125 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp762946)) Bool.false 19550042 67108864 2 67108864 9775021 33554432

noncomputable def hp763126 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp762946) Bool.false 230362662 67108864 6 67108864 115181331 33554432 3 33554432

noncomputable def hp763127 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 872386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763128 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 872386 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763129 := @hp763128 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 872386 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4658849628451

noncomputable def hp763130 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 872386 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 872386 1000 0

noncomputable def hp763131 := @hp763130 1 10680707 67108864 1 67108864 4658849628451 33554432000 436193 33554432000 (Enclosure.Real.IsNear.const Bool.false 872386 1000) hd4949

noncomputable def hp763132 := @hp763129 33554432000 436193 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 872386 1000) 872386 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000))) (hp763131 rfl)

noncomputable def hp763133 := @hp763127 4658849628451 33554432000 436193 33554432000 395379613 395379651 33554432 hp763132 rfl rfl rfl

noncomputable def hp763134 := @Enclosure.Real.IsNear.recentre' hp762946 Bool.false 790759264 67108864 38 67108864 24711227 2097152 19 33554432 (hp763133 rfl rfl rfl)

noncomputable def hp763135 := @Enclosure.Real.IsNear.sqrt_image hp762946 24711227 2097152 19 33554432 115181328 115181334 33554432 (hp763134 rfl) rfl rfl

noncomputable def hp763136 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp762946) 115181331 33554432 3 33554432 9775020 9775022 33554432 (hp763126 (hp763135 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp763137 := @hp763121 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp763124 (@hp763125 1 33554432 (hp763136 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp763138 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763139 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp763140 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1))) (hp763138 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763139 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp763141 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 872386 1000) 872386 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl

noncomputable def hp763142 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763143 := @hp763142 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763139 (Enclosure.sfrac Bool.false 1 16)))) 323752757

noncomputable def hp763144 := @hp763143 67108864 5707 67108864 3728159 33554432 211049027 22837985280000 1207001754784363 2251799813685248 27603432336062551 510877082729840640000

noncomputable def hp763145 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763146 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)))) 6955307

noncomputable def hp763147 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp763148 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 165127639) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp763149 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1))) Bool.false 1452478073847884283025

noncomputable def hp763150 := nat_lit 512735432997587903868411333

noncomputable def hp763151 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp763152 := @Enclosure.Real.IsNear.subLit_ff_p hp762946 (Enclosure.sfrac Bool.false 11 1) 24711227 2097152 19 33554432 11 1 0

noncomputable def hp763153 := @hp763151 500000000000000 1642555 2097152 19 33554432 1452478073847884283025 295147905179352825856 hp763150 hp682805 hd4948 (@hp763152 1 1642555 1642555 2097152 19 33554432 (hp763134 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763154 := @hp763148 165127639 33554432 239 67108864 Bool.false 13910614 67108864 1 10890000 (@hp763149 295147905179352825856 hp763150 hp682805 165127639 33554432 239 67108864 (hp763153 rfl) rfl) (Enclosure.sfrac_false_div 165127639 33554432)

noncomputable def hp763155 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 165127639) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1009685909189002451222528) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp763156 := BSN.sin_reduce_arg_pos_rat_q3 165127639 33554432 226375608064910080 72057594037927936 0 1009685909189002451222528 hp619237 rfl rfl rfl rfl

noncomputable def hp763157 := nat_lit 678181536932959480148903304792532367304976

noncomputable def hp763158 := BSN.sin_dyadic_bound_f 28696999526 137438953472 2 1 67108864 21801270 hp763157 hp749778 hp763157 hp763157 hp749779

noncomputable def hp763159 := @BSN.binarySplit_of_base (BSN.sinEvenP 28696999526) (BSN.sinEvenQ 137438953472) 0 1 hp763157 hp749778 hp763157 rfl rfl rfl

noncomputable def hp763160 := hp763158 hp763157 13910614 rfl rfl rfl rfl rfl rfl rfl rfl (hp763159 rfl)

noncomputable def hp763161 := @BSN.binarySplit_of_base (BSN.sinOddP 28696999526) (BSN.sinOddQ 137438953472) 0 1 hp763157 hp749779 hp763157 rfl rfl rfl

noncomputable def hp763162 := @BSN.sin_arg_round Bool.false 13910614 67108864 1009685909189002451222528 hp619237 28696999526 137438953472 21801270 21780000 (hp763160 (hp763161 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763163 := hp763155 13910614 67108864 0 1000000000000000 21780000 10890000 hp763156 BSN.pi_near_15 hp763162 rfl rfl

noncomputable def hp763164 := @hp763146 33554432 166863679 45675970560000 161873525 161879232 33554432 (@hp763147 13910614 67108864 2669818864 730815528960000 6955307 33554432 166863679 45675970560000 (hp763154 (hp763163 rfl rfl) rfl rfl) rfl)

noncomputable def hp763165 := @hp763145 Bool.false 323752757 67108864 5707 67108864 323752757 67108864 5707 67108864 (hp763164 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp763166 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763139 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp763167 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763139 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 48971305)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp763168 := nat_lit 903361133249752311105501845

noncomputable def hp763169 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763139 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp763168

noncomputable def hp763170 := nat_lit 44154832718002293047410551974019711

noncomputable def hp763171 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763139 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp763172 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp763173 := @hp763172 (Enclosure.sfrac Bool.false 1 16) 746700575335 4398046511104 1636208009 1125899906842624 1 16 0

noncomputable def hp763174 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)) 2697986928025

noncomputable def hp763175 := @hp763174 4398046511104 998673801 1125899906842624 1642555 2097152 19 33554432 1565944604964945920 746700575335 4398046511104 1636208009

noncomputable def hp763176 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)) 1642555 2097152 19

noncomputable def hp763177 := @hp763176 33554432 1642555 2097152 19 33554432 2697986928025 4398046511104 998673801 1125899906842624 (@hp763152 1 1642555 1642555 2097152 19 33554432 (hp763134 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763178 := hp763177 (@hp763152 1 1642555 1642555 2097152 19 33554432 (hp763134 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763179 := @hp763175 1125899906842624 (hp763178 rfl) (@hp763152 1 1642555 1642555 2097152 19 33554432 (hp763134 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763180 := @hp763171 500000000000000 1021578482279 4398046511104 1636208009 1125899906842624 hp763168 hp634261 hp763170 hp682143 hd4948 (@hp763173 1 16345255716464 1021578482279 4398046511104 1636208009 1125899906842624 (hp763179 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp763181 := @hp763167 48971305 33554432 307 33554432 Bool.false 3728159 33554432 1 10890000 (@hp763169 hp634261 hp763170 hp682143 48971305 33554432 307 33554432 (hp763180 rfl) rfl) (Enclosure.sfrac_true_div 48971305 33554432)

noncomputable def hp763182 := nat_lit 184953808969478650231584098594219208815027699659305961979458010348679078414450069993770721234390625

noncomputable def hp763183 := nat_lit 190239251426014051807823164294045519462818465988988925998299791815305829649090134941650390625

noncomputable def hp763184 := nat_lit 1120037453547515466958317939706986783928049712421784485300127333935983003488705563079199799659990625

noncomputable def hp763185 := BSN.cos_dyadic_bound_f 48971305 33554432 4 3 33554432 10890000 hp763182 hp681868 hp763183 hp763184 hp681871

noncomputable def hp763186 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 48971305) (BSN.cosEvenQ 33554432) 0 3 hp763182 hp681868 hp763183 rfl rfl rfl

noncomputable def hp763187 := hp763185 hp763183 3728159 rfl rfl rfl rfl rfl rfl rfl rfl (hp763186 rfl)

noncomputable def hp763188 := @BSN.binarySplit_of_base3 (BSN.cosOddP 48971305) (BSN.cosOddQ 33554432) 0 3 hp763184 hp681871 hp763183 rfl rfl rfl

noncomputable def hp763189 := hp763181 (BSN.cos_neg_of_bound 48971305 33554432 Bool.false 3728159 33554432 1 10890000 (hp763187 (hp763188 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp763190 := hp763144 hp763165 (@hp763166 3728159 33554432 3376784432 365407764480000 3728159 33554432 211049027 22837985280000 (hp763189 rfl) rfl)

noncomputable def hp763191 := @hp763119 33554432 1207001754784363 2251799813685248 27603432336062551 510877082729840640000 11798467500053998796623 75557863725914323419136 270097996883639531756747 hp741590 (hp763137 rfl) (@hp763140 Bool.false 1207001754784363 2251799813685248 27603432336062551 510877082729840640000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp762946 (Enclosure.sfrac Bool.false 11 1)) (hp763141 rfl (hp762949 rfl rfl))) (hp763190 rfl))

noncomputable def hp763192 := @hp762943 hp762941 hp741590 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 872386 1000))) (@hp762948 hp762941 hp741590 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 872386 1000) 11 (hp762949 rfl rfl)) (@hp762952 hp762941 hp741590 hp763118 (hp763191 rfl) rfl rfl))

theorem hd5061 : hp762942 hp741590 := hp763192

noncomputable def hp763193 := nat_lit 1719326039689522770584017

noncomputable def hp763194 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 873660 1000)) Bool.true 5330217008264793987747 9444732965739290427392 hp763193

noncomputable def hp763195 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 873660 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 873660 1000)) Bool.true 5330217008264793987747 9444732965739290427392

noncomputable def hp763196 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 873660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763197 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp763196 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763198 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 873660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763199 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp763197 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp763200 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 873660 1000)) hp763199 Bool.true 5330217008264793987747 9444732965739290427392

noncomputable def hp763201 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 873660 1000) 873660 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl

noncomputable def hp763202 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp763197 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp763203 := nat_lit 1430819233192515742846924357632

noncomputable def hp763204 := @hp763202 194196733 268435456 211989 268435456 1502473104042766198109 9444732965739290427392 27133510145519841944017 hp740342 hp763203 5330217008264793987747 9444732965739290427392

noncomputable def hp763205 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) 11)

noncomputable def hp763206 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) 11) hp763205

noncomputable def hp763207 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) 11)

noncomputable def hp763208 := @hp763207 194196733 536870912 211989 536870912 194196733 536870912 211989 536870912 208517154306260992 194196733 268435456

noncomputable def hp763209 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp763210 := hp763209 BSN.quadSignPos 9 10 11 873660 1000 186 239 536870912 268435456 9007199254740992

noncomputable def hp763211 := hp763210 Bool.false 922587010640 3981 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp763212 := hp763211 Bool.true 252829110 181986 Bool.true 567016663 Bool.true 575868453 28296951008113761 1 Bool.false 264261977

noncomputable def hp763213 := hp763212 Bool.true Bool.false 471621927 Bool.false Bool.true 194196733 211989 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 264261977 536870912) BSN.abs_quadSignPos

noncomputable def hp763214 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp763215 := hp763214 BSN.quadSignPos 7 8 9 873660 1000 62 128 536870912 268435456 9007199254740992

noncomputable def hp763216 := hp763215 Bool.false 922587010640 3981 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp763217 := hp763216 Bool.true 310188386 148627 Bool.true 474219909 Bool.true 60693453 28296951008113761 1 Bool.false 340699141

noncomputable def hp763218 := hp763217 Bool.true Bool.false 533443855 Bool.false Bool.true 252829110 181986 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 340699141 536870912) BSN.abs_quadSignPos

noncomputable def hp763219 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp763220 := hp763219 BSN.quadSignPos 5 6 7 873660 1000 97 11 536870912 268435456 9007199254740992

noncomputable def hp763221 := hp763220 Bool.false 922587010640 3981 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp763222 := hp763221 Bool.true 351313202 110446 Bool.false 373882515 Bool.false 595725248 28296951008113761 1 Bool.false 344385566

noncomputable def hp763223 := hp763222 Bool.true Bool.false 480784952 Bool.false Bool.true 310188386 148627 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 97 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 344385566 536870912) BSN.abs_quadSignPos

noncomputable def hp763224 := hp763214 BSN.quadSignNeg 3 4 5 873660 1000 322 198 536870912 268435456 9007199254740992

noncomputable def hp763225 := hp763224 Bool.false 922587010640 3981 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp763226 := hp763225 Bool.true 277356864 65278 Bool.false 808470715 Bool.false 715673961 28296951008113761 1 Bool.false 34819684

noncomputable def hp763227 := hp763226 Bool.true Bool.false 126441807 Bool.true Bool.true 351313202 110446 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 322 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 34819684 536870912) BSN.abs_quadSignNeg

noncomputable def hp763228 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp763229 := hp763228 BSN.quadSignNeg 1 2 3 873660 1000 708 482 536870912 268435456 9007199254740992

noncomputable def hp763230 := hp763229 Bool.false 922587010640 3981 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp763231 := hp763230 Bool.true 536870616 4034 Bool.false 404521143 Bool.false 813245179 28296951008113761 1 Bool.false 391546821

noncomputable def hp763232 := hp763231 Bool.false Bool.false 30053958 Bool.true Bool.true 277356864 65278 BSN.abs_quadSignPos (BSN.cos_quad_nat0 708 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 391546821 536870912) BSN.abs_quadSignNeg

noncomputable def hp763233 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) 1) Bool.true

noncomputable def hp763234 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)))

noncomputable def hp763235 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000))) Bool.true 67108827 67108864

noncomputable def hp763236 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 57661688165) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 57661688165 33554432

noncomputable def hp763237 := nat_lit 1344350184084388952806450413833850379956107708857

noncomputable def hp763238 := nat_lit 782302916746385338730388361644170936949145600

noncomputable def hp763239 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) Bool.false hp763237 hp763238 6612288538781257109

noncomputable def hp763240 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 873660 4000) (Real.log (Enclosure.sfrac Bool.false 3053128182400 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1747320))))))

noncomputable def hp763241 := nat_lit 244317096768847934328219648000000000

noncomputable def hp763242 := nat_lit 1280700644332222154584723330990080000000

noncomputable def hp763243 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp763240 (Enclosure.sfrac Bool.false 873660 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 873660 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp763241 hp763242)) Bool.false

noncomputable def hp763244 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 873660 1000) 873660 1000 3053128182400 16000000 1747320

noncomputable def hp763245 := hp763244 4000 2000 hp763241 hp763242 (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl rfl rfl rfl

noncomputable def hp763246 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp763240 (Enclosure.sfrac Bool.false 873660 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 873660 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp763241 hp763242) 1547844327460590853349 900719925474099200

noncomputable def hp763247 := nat_lit 1982325007443476574250279522222842416268078183172177920000000

noncomputable def hp763248 := @hp763246 6612288538781257109 892108800000000000000000 hp763241 hp763242 0 1 hp763247 hp763237 hp763238 6612288538781257109 892108800000000000000000

noncomputable def hp763249 := @Enclosure.Real.IsNear.subLit_ff_p (hp763240 (Enclosure.sfrac Bool.false 873660 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 873660 2000) (Real.log Real.pi)) 1998251446995883138277 900719925474099200 137759577182651 54450000000000000000

noncomputable def hp763250 := nat_lit 5193703723236212846852099276800

noncomputable def hp763251 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 873660 4000) (Real.log (Enclosure.sfrac Bool.false 3053128182400 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1747320))))))

noncomputable def hp763252 := @hp763251 (Enclosure.sfrac Bool.false 873660 2000) 2391712932040733891813 900719925474099200 137759577182651 54450000000000000000 873660 2000 0

noncomputable def hp763253 := nat_lit 3996502893991766276554000

noncomputable def hp763254 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 873660 4000) (Real.log (Enclosure.sfrac Bool.false 3053128182400 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1747320))))) 2392066515059183774613

noncomputable def hp763255 := nat_lit 5385658734757922789222324448866074624

noncomputable def hp763256 := @hp763254 900719925474099200 182012769567793 72600000000000000000 883957546124707 2251799813685248 200000001089 8712000000000000000 hp763255 2391712932040733891813 900719925474099200 137759577182651

noncomputable def hp763257 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 873660 4000) (Real.log (Enclosure.sfrac Bool.false 3053128182400 16000000)) 873660 4000 0 1 54759666576452711 4503599627370496

noncomputable def hp763258 := nat_lit 117595488542864338717769728

noncomputable def hp763259 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3053128182400) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp763258 hp617687

noncomputable def hp763260 := BSN.log_rat_reduce_isNear 3053128182400 16000000 17 6106256364800 4194304000000 100820723 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp763261 := nat_lit 136500126149761739626801774531646054638208205309127810277247325269170873330249228774644648609560492930710372352000000000000000000000

noncomputable def hp763262 := nat_lit 1600858060532485653496214631637831985218898213944876547260995312026915254530648446488446352609824922791208550400000000000000000000

noncomputable def hp763263 := nat_lit 602424367887204118298750331833320915769323728630518773315546573310636619327947733174467403896724652032000000000000000000000

noncomputable def hp763264 := BSN.log_dyadic_bound 955976182400 5150280182400 6 5 hp763261 268435456 87120000 hp763262 hp763263 100820723 6106256364800

noncomputable def hp763265 := hp763264 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp763266 := @BSN.binarySplit_of_base5 (BSN.artanhP 955976182400) (BSN.artanhQ 5150280182400) 0 5 hp763262 hp763261 hp763263 rfl rfl rfl

noncomputable def hp763267 := hp763260 rfl rfl rfl rfl (hp763265 (hp763266 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp763268 := @hp763257 12500018513 1089000000000000000 2392066515059183774613 900719925474099200 182012769567793 72600000000000000000 (Enclosure.Real.IsNear.const Bool.false 873660 4000) (BSN.isNear_log_sfrac 3053128182400 16000000 54759666576452711 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp763259 1000001481040000 87120000000000000000000 54759666576452711 4503599627370496 12500018513 1089000000000000000 (hp763267 rfl rfl rfl) rfl)) rfl

noncomputable def hp763269 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1747320)))) 1 4

noncomputable def hp763270 := @hp763269 0 1 883957546124707 562949953421312 200000001089 2178000000000000000 883957546124707 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp763271 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1747320))) 884279719003555 562949953421312 1

noncomputable def hp763272 := @hp763271 2000000000000000 19203 33554432 1 10890000 29660693372328344551424 883957546124707 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp763273 := BSN.arctan_dyadic_bound_f 1000 1747320 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp763274 := hp763273 1 19203 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1747320) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1747320) 0 0 rfl)

noncomputable def hp763275 := hp763270 (hp763272 (hp763274 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp763276 := @hp763249 1677897272763 3355443200 131049 26843545600 hp763250 1547844327460590853349 900719925474099200 6612288538781257109 892108800000000000000000 (@hp763252 1 hp763253 1998251446995883138277 900719925474099200 137759577182651 54450000000000000000 (@hp763256 54450000000000000000 hp763268 hp763275 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 873660 2000) rfl rfl)

noncomputable def hp763277 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 873660 2000) (Real.log Real.pi) 873660 2000 0 1 38410761 33554432

noncomputable def hp763278 := hp763276 (@hp763277 3 268435456 1677897272763 3355443200 131049 26843545600 (Enclosure.Real.IsNear.const Bool.false 873660 2000) hd4909 rfl) rfl

noncomputable def hp763279 := @hp763239 892108800000000000000000 57661688165 33554432 249 33554432 (@hp763243 hp763237 hp763238 6612288538781257109 892108800000000000000000 (hp763245 rfl rfl rfl rfl rfl) (hp763248 (hp763278 rfl) (Enclosure.Real.IsNear.const Bool.true hp763241 hp763242) rfl rfl)) rfl

noncomputable def hp763280 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 57661688165) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 5022354019165918986240) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp763281 := BSN.sin_reduce_arg_pos_rat_q2 57661688165 33554432 226375608064910080 72057594037927936 273 5022354019165918986240 hp619237 rfl rfl rfl rfl

noncomputable def hp763282 := BSN.cos_dyadic_bound_f 142743886 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp763283 := hp763282 1 67108827 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 142743886) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp763284 := hp763283 (@BSN.binarySplit_of_le (BSN.cosOddP 142743886) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp763285 := @BSN.cos_arg_round Bool.false 67108827 67108864 5022354019165918986240 hp619237 142743886 137438953472 21801270 21780000 hp763284 rfl

noncomputable def hp763286 := hp763280 67108827 67108864 273 1000000000000000 21780000 10890000 hp763281 BSN.pi_near_15 hp763285 rfl rfl

noncomputable def hp763287 := @hp763236 249 33554432 Bool.true 67108827 67108864 1 10890000 hp763279 (Enclosure.sfrac_false_div 57661688165 33554432) (hp763286 rfl rfl) rfl

noncomputable def hp763288 := @hp763233 67108827 67108864 171572777 22837985280000 536870616 536870912 4034 536870912 (@hp763234 Bool.true 67108827 67108864 171572777 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000)) (@hp763235 2745164432 365407764480000 67108827 67108864 171572777 22837985280000 (hp763287 rfl) rfl))

noncomputable def hp763289 := @hp763239 892108800000000000000000 922587010640 536870912 3981 536870912 (@hp763243 hp763237 hp763238 6612288538781257109 892108800000000000000000 (hp763245 rfl rfl rfl rfl rfl) (hp763248 (hp763278 rfl) (Enclosure.Real.IsNear.const Bool.true hp763241 hp763242) rfl rfl)) rfl

noncomputable def hp763290 := hp763232 (BSN.cos_quad_nat2 482 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 30053958 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl rfl (hp763288 rfl) hp763289

noncomputable def hp763291 := nat_lit 3737980192134899600113897297257955823563493613220169098102850904431247681

noncomputable def hp763292 := nat_lit 717017582715981103299026217993544793717367849854881245127935323259201

noncomputable def hp763293 := nat_lit 11212506541239266838135093839337880381103046103960797531818296842647224641

noncomputable def hp763294 := BSN.cos_dyadic_bound_f 404521143 536870912 3 2 536870912 268435456 hp763291 hp708868 hp763292 hp763293 hp708870

noncomputable def hp763295 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 404521143) (BSN.cosEvenQ 536870912) 0 2 hp763291 hp708868 hp763292 rfl rfl rfl

noncomputable def hp763296 := hp763294 hp763292 391546821 rfl rfl rfl rfl rfl rfl rfl rfl (hp763295 rfl)

noncomputable def hp763297 := @BSN.binarySplit_of_base2 (BSN.cosOddP 404521143) (BSN.cosOddQ 536870912) 0 2 hp763293 hp708870 hp763292 rfl rfl rfl

noncomputable def hp763298 := nat_lit 60440806726444795105607980011381025186227463610395060655804224747973693938859846257479078716960190860351476119121

noncomputable def hp763299 := nat_lit 83686994108832082377057046511653543724135478757533937416667120490553688720111069591979663335796006812956241

noncomputable def hp763300 := nat_lit 365910096424580899808385499702015251307132524638233793450756278517555831305293785165684357010731858444321561818705

noncomputable def hp763301 := BSN.cos_dyadic_bound_f 813245179 536870912 4 3 536870912 268435456 hp763298 hp716712 hp763299 hp763300 hp716714

noncomputable def hp763302 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 813245179) (BSN.cosEvenQ 536870912) 0 3 hp763298 hp716712 hp763299 rfl rfl rfl

noncomputable def hp763303 := hp763301 hp763299 30053958 rfl rfl rfl rfl rfl rfl rfl rfl (hp763302 rfl)

noncomputable def hp763304 := @BSN.binarySplit_of_base3 (BSN.cosOddP 813245179) (BSN.cosOddQ 536870912) 0 3 hp763300 hp716714 hp763299 rfl rfl rfl

noncomputable def hp763305 := hp763290 hd4911 hd4913 hd4915 hd4917 hd4918 (hp763296 (hp763297 rfl) rfl rfl rfl rfl) (hp763303 (hp763304 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763306 := hp763227 (BSN.cos_quad_nat2 198 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 126441807 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl rfl (hp763305 rfl rfl rfl rfl rfl) hp763289

noncomputable def hp763307 := nat_lit 59029597688470908915481911013000166170102907782683803941947615879915156357500897611422084130699412208888448140625

noncomputable def hp763308 := nat_lit 77977897001649767962025971026955523411136531667458239766453565977934819555078585438643888717104687744140625

noncomputable def hp763309 := nat_lit 357383931123635407445692801784606990105000078670129992711377176889574353101441156036362281982827447222649881740625

noncomputable def hp763310 := BSN.cos_dyadic_bound_f 808470715 536870912 4 3 536870912 268435456 hp763307 hp716712 hp763308 hp763309 hp716714

noncomputable def hp763311 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 808470715) (BSN.cosEvenQ 536870912) 0 3 hp763307 hp716712 hp763308 rfl rfl rfl

noncomputable def hp763312 := hp763310 hp763308 34819684 rfl rfl rfl rfl rfl rfl rfl rfl (hp763311 rfl)

noncomputable def hp763313 := @BSN.binarySplit_of_base3 (BSN.cosOddP 808470715) (BSN.cosOddQ 536870912) 0 3 hp763309 hp716714 hp763308 rfl rfl rfl

noncomputable def hp763314 := nat_lit 36204399115892442541755058164843977144204987154368028748771767123874063750263694287035512975378842688334679989601

noncomputable def hp763315 := nat_lit 18054380628595653516626786188217673619556689600223388639128804319004985023943178860306489502629139685793121

noncomputable def hp763316 := nat_lit 219365218516658438371778214603022285073498662120825394702570051704624907518727498533506012659006071175233872551265

noncomputable def hp763317 := BSN.cos_dyadic_bound_f 715673961 536870912 4 3 536870912 268435456 hp763314 hp716712 hp763315 hp763316 hp716714

noncomputable def hp763318 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 715673961) (BSN.cosEvenQ 536870912) 0 3 hp763314 hp716712 hp763315 rfl rfl rfl

noncomputable def hp763319 := hp763317 hp763315 126441807 rfl rfl rfl rfl rfl rfl rfl rfl (hp763318 rfl)

noncomputable def hp763320 := @BSN.binarySplit_of_base3 (BSN.cosOddP 715673961) (BSN.cosOddQ 536870912) 0 3 hp763316 hp716714 hp763315 rfl rfl rfl

noncomputable def hp763321 := hp763306 hd4920 hd4922 hd4924 hd4926 hd4918 (hp763312 (hp763313 rfl) rfl rfl rfl rfl) (hp763319 (hp763320 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763322 := hp763223 (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 480784952 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl rfl (hp763321 rfl rfl rfl rfl rfl) hp763289

noncomputable def hp763323 := nat_lit 4909482139882031128555479032014984917963632125873180880978954256551630625

noncomputable def hp763324 := nat_lit 381839843369870582234008132248008086662444888640152064694004125390625

noncomputable def hp763325 := nat_lit 12857549292325577927178828118301320867288249704610056346840137522384590625

noncomputable def hp763326 := BSN.sin_dyadic_bound_f 373882515 536870912 3 2 536870912 268435456 hp763323 hp708845 hp763324 hp763325 hp708848

noncomputable def hp763327 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 373882515) (BSN.sinEvenQ 536870912) 0 2 hp763323 hp708845 hp763324 rfl rfl rfl

noncomputable def hp763328 := hp763326 hp763324 344385566 rfl rfl rfl rfl rfl rfl rfl rfl (hp763327 rfl)

noncomputable def hp763329 := @BSN.binarySplit_of_base2 (BSN.sinOddP 373882515) (BSN.sinOddQ 536870912) 0 2 hp763325 hp708848 hp763324 rfl rfl rfl

noncomputable def hp763330 := nat_lit 31656506110093272720805566729591536245398012898113346070382770854643630080

noncomputable def hp763331 := nat_lit 15862369198015660577624009956665341706778501898017294848106639189344256

noncomputable def hp763332 := nat_lit 82884215023923688913555569228047993898993344777700068849819846251093426176

noncomputable def hp763333 := BSN.sin_dyadic_bound_f 595725248 536870912 3 2 536870912 268435456 hp763330 hp708845 hp763331 hp763332 hp708848

noncomputable def hp763334 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 595725248) (BSN.sinEvenQ 536870912) 0 2 hp763330 hp708845 hp763331 rfl rfl rfl

noncomputable def hp763335 := hp763333 hp763331 480784952 rfl rfl rfl rfl rfl rfl rfl rfl (hp763334 rfl)

noncomputable def hp763336 := @BSN.binarySplit_of_base2 (BSN.sinOddP 595725248) (BSN.sinOddQ 536870912) 0 2 hp763332 hp708848 hp763331 rfl rfl rfl

noncomputable def hp763337 := hp763322 hd4928 hd4930 hd4932 hd4934 hd4918 (hp763328 (hp763329 rfl) rfl rfl rfl rfl) (hp763335 (hp763336 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763338 := hp763218 (BSN.cos_quad_nat0 128 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 533443855 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl rfl (hp763337 rfl rfl rfl rfl rfl) hp763289

noncomputable def hp763339 := nat_lit 7060984351353700438740867386083738789696036702238932779298581839572152801

noncomputable def hp763340 := nat_lit 2557633211980534390278385813647648571081022409086416146735669637591521

noncomputable def hp763341 := nat_lit 21177837787637140247442045386623921071945948061898625505602274179441275361

noncomputable def hp763342 := BSN.cos_dyadic_bound_f 474219909 536870912 3 2 536870912 268435456 hp763339 hp708868 hp763340 hp763341 hp708870

noncomputable def hp763343 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 474219909) (BSN.cosEvenQ 536870912) 0 2 hp763339 hp708868 hp763340 rfl rfl rfl

noncomputable def hp763344 := hp763342 hp763340 340699141 rfl rfl rfl rfl rfl rfl rfl rfl (hp763343 rfl)

noncomputable def hp763345 := @BSN.binarySplit_of_base2 (BSN.cosOddP 474219909) (BSN.cosOddQ 536870912) 0 2 hp763341 hp708870 hp763340 rfl rfl rfl

noncomputable def hp763346 := nat_lit 13569610599562171553475061377681

noncomputable def hp763347 := BSN.cos_dyadic_bound_f 60693453 536870912 2 1 536870912 268435456 hp763346 hp708767 hp763346 hp763346 hp708768

noncomputable def hp763348 := @BSN.binarySplit_of_base (BSN.cosEvenP 60693453) (BSN.cosEvenQ 536870912) 0 1 hp763346 hp708767 hp763346 rfl rfl rfl

noncomputable def hp763349 := hp763347 hp763346 533443855 rfl rfl rfl rfl rfl rfl rfl rfl (hp763348 rfl)

noncomputable def hp763350 := @BSN.binarySplit_of_base (BSN.cosOddP 60693453) (BSN.cosOddQ 536870912) 0 1 hp763346 hp708768 hp763346 rfl rfl rfl

noncomputable def hp763351 := hp763338 hd4936 hd4938 hd4940 hd4942 hd4918 (hp763344 (hp763345 rfl) rfl rfl rfl rfl) (hp763349 (hp763350 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763352 := hp763213 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 471621927 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl rfl (hp763351 rfl rfl rfl rfl rfl) hp763289

noncomputable def hp763353 := nat_lit 14249169891040644309723857951450640381978248947371714388700415295592275695414791400587579038799590436275206449761

noncomputable def hp763354 := nat_lit 1104459667659449189928648047106919989036553843059945201419300272783500811156227327214231378377041303530081

noncomputable def hp763355 := nat_lit 86402308178894304823683352522523127928130068069334054209278978412609177380017320102242912651679655456750495820385

noncomputable def hp763356 := BSN.cos_dyadic_bound_f 567016663 536870912 4 3 536870912 268435456 hp763353 hp716712 hp763354 hp763355 hp716714

noncomputable def hp763357 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 567016663) (BSN.cosEvenQ 536870912) 0 3 hp763353 hp716712 hp763354 rfl rfl rfl

noncomputable def hp763358 := hp763356 hp763354 264261977 rfl rfl rfl rfl rfl rfl rfl rfl (hp763357 rfl)

noncomputable def hp763359 := @BSN.binarySplit_of_base3 (BSN.cosOddP 567016663) (BSN.cosOddQ 536870912) 0 3 hp763355 hp716714 hp763354 rfl rfl rfl

noncomputable def hp763360 := nat_lit 27640411762499750816018791740240917758944356620213900640670240536094098145

noncomputable def hp763361 := nat_lit 12094454991038244833399918794229500424042728114170698185016703716737761

noncomputable def hp763362 := nat_lit 72371973117513856883652283260678413034643912445518225309455841026609824481

noncomputable def hp763363 := BSN.sin_dyadic_bound_f 575868453 536870912 3 2 536870912 268435456 hp763360 hp708845 hp763361 hp763362 hp708848

noncomputable def hp763364 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 575868453) (BSN.sinEvenQ 536870912) 0 2 hp763360 hp708845 hp763361 rfl rfl rfl

noncomputable def hp763365 := hp763363 hp763361 471621927 rfl rfl rfl rfl rfl rfl rfl rfl (hp763364 rfl)

noncomputable def hp763366 := @BSN.binarySplit_of_base2 (BSN.sinOddP 575868453) (BSN.sinOddQ 536870912) 0 2 hp763362 hp708848 hp763361 rfl rfl rfl

noncomputable def hp763367 := hp763352 hd4944 hd4946 hd4961 hd4963 hd4918 (hp763358 (hp763359 rfl) rfl rfl rfl rfl) (hp763365 (hp763366 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763368 := @hp763208 211989 268435456 (hp763367 rfl rfl rfl rfl rfl) (hp763367 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp763369 := @hp763206 Bool.true 194196733 268435456 211989 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 873660 1000)) (Enclosure.sfrac Bool.false 873660 1000) 11) hp763368

noncomputable def hp763370 := @Enclosure.Real.IsNear.mulLit_tf hp763197 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1))) 19542911 67108864 1

noncomputable def hp763371 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp763196 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763372 := @hp763371 1 1 0 1 19542911 67108864 1 67108864 19542911 67108864 1

noncomputable def hp763373 := @Enclosure.Real.IsNear.of_eq (hp763196 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763374 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 873660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763375 := @hp763373 (@Inv.inv Real Real.instInv (Real.sqrt hp763198)) Bool.false 19542911 67108864 1 67108864 (hp763374 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 873660 1000) 873660 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000))))

noncomputable def hp763376 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp763198)) Bool.false 19542911 67108864 1 67108864 19542911 67108864

noncomputable def hp763377 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp763198) Bool.false 230446719 67108864 7 67108864 230446719 67108864 7 67108864

noncomputable def hp763378 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 873660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763379 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 873660 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763380 := @hp763379 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 873660 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 466565323881

noncomputable def hp763381 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 873660 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 873660 1000 0

noncomputable def hp763382 := @hp763381 1 10680707 67108864 1 67108864 466565323881 3355443200 43683 3355443200 (Enclosure.Real.IsNear.const Bool.false 873660 1000) hd4949

noncomputable def hp763383 := @hp763380 3355443200 43683 3355443200 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 873660 1000) 873660 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000))) (hp763382 rfl)

noncomputable def hp763384 := @hp763378 466565323881 3355443200 43683 3355443200 395668206 395668244 33554432 hp763383 rfl rfl rfl

noncomputable def hp763385 := @Enclosure.Real.IsNear.recentre' hp763198 Bool.false 791336450 67108864 38 67108864 395668225 33554432 19 33554432 (hp763384 rfl rfl rfl)

noncomputable def hp763386 := @Enclosure.Real.IsNear.sqrt_image hp763198 395668225 33554432 19 33554432 115223356 115223363 33554432 (hp763385 rfl) rfl rfl

noncomputable def hp763387 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp763198) 230446719 67108864 7 67108864 9771455 9771456 33554432 (hp763377 (hp763386 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp763388 := @hp763372 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp763375 (@hp763376 1 67108864 (hp763387 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp763389 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763390 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp763391 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1))) (hp763389 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763390 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp763392 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 873660 1000) 873660 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl

noncomputable def hp763393 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763394 := @hp763393 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763390 (Enclosure.sfrac Bool.false 1 16)))) 16142971

noncomputable def hp763395 := @hp763394 4194304 57 1048576 4762489 33554432 424139929 45675970560000 76880721814819 140737488355328 8325085176177871 191578906023690240000

noncomputable def hp763396 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763397 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)))) 4359095

noncomputable def hp763398 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp763399 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 83470461) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false

noncomputable def hp763400 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1))) Bool.false 23494846118512541476515

noncomputable def hp763401 := nat_lit 512735433000066898862120389

noncomputable def hp763402 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp763403 := @Enclosure.Real.IsNear.subLit_ff_p hp763198 (Enclosure.sfrac Bool.false 11 1) 395668225 33554432 19 33554432 11 1 0

noncomputable def hp763404 := @hp763402 500000000000000 26569473 33554432 19 33554432 23494846118512541476515 4722366482869645213696 hp763401 hp682805 hd4948 (@hp763403 1 26569473 26569473 33554432 19 33554432 (hp763385 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763405 := @hp763399 83470461 16777216 15 4194304 Bool.false 17436380 67108864 1 10890000 (@hp763400 4722366482869645213696 hp763401 hp682805 83470461 16777216 15 4194304 (hp763404 rfl) rfl) (Enclosure.sfrac_false_div 83470461 16777216)

noncomputable def hp763406 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 83470461) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 635503764884377307185152) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp763407 := BSN.sin_reduce_arg_pos_rat_q3 83470461 16777216 226375608064910080 72057594037927936 0 635503764884377307185152 hp619230 rfl rfl rfl rfl

noncomputable def hp763408 := nat_lit 1702916188934994707508567008490880649652496

noncomputable def hp763409 := BSN.sin_dyadic_bound_f 36124206694 137438953472 2 1 67108864 21801270 hp763408 hp749778 hp763408 hp763408 hp749779

noncomputable def hp763410 := @BSN.binarySplit_of_base (BSN.sinEvenP 36124206694) (BSN.sinEvenQ 137438953472) 0 1 hp763408 hp749778 hp763408 rfl rfl rfl

noncomputable def hp763411 := hp763409 hp763408 17436380 rfl rfl rfl rfl rfl rfl rfl rfl (hp763410 rfl)

noncomputable def hp763412 := @BSN.binarySplit_of_base (BSN.sinOddP 36124206694) (BSN.sinOddQ 137438953472) 0 1 hp763408 hp749779 hp763408 rfl rfl rfl

noncomputable def hp763413 := @BSN.sin_arg_round Bool.false 17436380 67108864 635503764884377307185152 hp619230 36124206694 137438953472 21801270 21780000 (hp763411 (hp763412 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763414 := hp763406 17436380 67108864 0 1000000000000000 21780000 10890000 hp763407 BSN.pi_near_15 hp763413 rfl rfl

noncomputable def hp763415 := @hp763397 16777216 10471519 2854748160000 129141944 129145592 33554432 (@hp763398 17436380 67108864 167544304 45675970560000 4359095 16777216 10471519 2854748160000 (hp763405 (hp763414 rfl rfl) rfl rfl) rfl)

noncomputable def hp763416 := @hp763396 Bool.false 258287536 67108864 3648 67108864 16142971 4194304 57 1048576 (hp763415 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp763417 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763390 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp763418 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763390 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 95857105)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp763419 := nat_lit 226336190177177012081224333405

noncomputable def hp763420 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763390 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp763419

noncomputable def hp763421 := nat_lit 44450776431454303987834202484809513

noncomputable def hp763422 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763390 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp763423 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp763424 := @hp763423 (Enclosure.sfrac Bool.false 1 16) 185586679556607 1125899906842624 1647174543 1125899906842624 1 16 0

noncomputable def hp763425 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)) 705936895497729

noncomputable def hp763426 := @hp763425 1125899906842624 1009640335 1125899906842624 26569473 33554432 19 33554432 6227255619287959732224 185586679556607 1125899906842624 1647174543

noncomputable def hp763427 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)) 26569473 33554432 19

noncomputable def hp763428 := @hp763427 33554432 26569473 33554432 19 33554432 705936895497729 1125899906842624 1009640335 1125899906842624 (@hp763403 1 26569473 26569473 33554432 19 33554432 (hp763385 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763429 := hp763428 (@hp763403 1 26569473 26569473 33554432 19 33554432 (hp763385 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763430 := @hp763426 1125899906842624 (hp763429 rfl) (@hp763403 1 26569473 26569473 33554432 19 33554432 (hp763385 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763431 := @hp763422 500000000000000 255955423734271 1125899906842624 1647174543 1125899906842624 hp763419 hp682141 hp763421 hp682143 hd4948 (@hp763424 1 4095286779748336 255955423734271 1125899906842624 1647174543 1125899906842624 (hp763430 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp763432 := @hp763418 95857105 67108864 617 67108864 Bool.false 4762489 33554432 1 10890000 (@hp763420 hp682141 hp763421 hp682143 95857105 67108864 617 67108864 (hp763431 rfl) rfl) (Enclosure.sfrac_true_div 95857105 67108864)

noncomputable def hp763433 := nat_lit 694923823314983092097332193967936554405640053682941491704334001478065823226136961633622374873451890625

noncomputable def hp763434 := nat_lit 601854765527082213824674688932097677584150073043832974861370016873693246487952274633652587890625

noncomputable def hp763435 := nat_lit 4208921272801366136566904251784884572330980422450017099517592892800909843986244701898129915745029490625

noncomputable def hp763436 := BSN.cos_dyadic_bound_f 95857105 67108864 4 3 33554432 10890000 hp763433 hp745658 hp763434 hp763435 hp745661

noncomputable def hp763437 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 95857105) (BSN.cosEvenQ 67108864) 0 3 hp763433 hp745658 hp763434 rfl rfl rfl

noncomputable def hp763438 := hp763436 hp763434 4762489 rfl rfl rfl rfl rfl rfl rfl rfl (hp763437 rfl)

noncomputable def hp763439 := @BSN.binarySplit_of_base3 (BSN.cosOddP 95857105) (BSN.cosOddQ 67108864) 0 3 hp763435 hp745661 hp763434 rfl rfl rfl

noncomputable def hp763440 := hp763432 (BSN.cos_neg_of_bound 95857105 67108864 Bool.false 4762489 33554432 1 10890000 (hp763438 (hp763439 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp763441 := hp763395 hp763416 (@hp763417 4762489 33554432 6786238864 730815528960000 4762489 33554432 424139929 45675970560000 (hp763440 rfl) rfl)

noncomputable def hp763442 := @hp763370 67108864 76880721814819 140737488355328 8325085176177871 191578906023690240000 1502473104042766198109 9444732965739290427392 27133510145519841944017 hp740342 (hp763388 rfl) (@hp763391 Bool.false 76880721814819 140737488355328 8325085176177871 191578906023690240000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763198 (Enclosure.sfrac Bool.false 11 1)) (hp763392 rfl (hp763201 rfl rfl))) (hp763441 rfl))

noncomputable def hp763443 := @hp763195 hp763193 hp740342 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 873660 1000))) (@hp763200 hp763193 hp740342 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 873660 1000) 11 (hp763201 rfl rfl)) (@hp763204 hp763193 hp740342 hp763369 (hp763442 rfl) rfl rfl))

theorem hd5062 : hp763194 hp740342 := hp763443

noncomputable def hp763444 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 874933 1000)) Bool.false 134090306691679199591637 37778931862957161709568 54961730151268642414957

noncomputable def hp763445 := nat_lit 68568761331267248502865920

noncomputable def hp763446 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 874933 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 874933 1000)) Bool.false 134090306691679199591637 37778931862957161709568

noncomputable def hp763447 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 874933 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763448 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp763447 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763449 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 874933 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763450 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp763448 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp763451 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 874933 1000)) hp763450 Bool.false 134090306691679199591637 37778931862957161709568

noncomputable def hp763452 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 874933 1000) 874933 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl

noncomputable def hp763453 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp763448 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp763454 := nat_lit 35994592621960757348096091881472

noncomputable def hp763455 := @hp763453 909250737 268435456 212301 268435456 6124641681068297714901 37778931862957161709568 731872380954693558637 hp763445 hp763454 134090306691679199591637 37778931862957161709568

noncomputable def hp763456 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) 11)

noncomputable def hp763457 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) 11) hp763456

noncomputable def hp763458 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) 11)

noncomputable def hp763459 := @hp763458 909250737 536870912 212301 536870912 909250737 536870912 212301 536870912 976300544819724288 909250737 268435456

noncomputable def hp763460 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp763461 := hp763460 BSN.quadSignPos 9 10 11 874933 1000 186 239 536870912 268435456 9007199254740992

noncomputable def hp763462 := hp763461 Bool.false 924273576024 3987 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp763463 := hp763462 Bool.false 887058047 182254 Bool.true 454122366 Bool.true 528112629 28296951008113761 1 Bool.false 355988996

noncomputable def hp763464 := hp763463 Bool.true Bool.false 446969271 Bool.false Bool.false 909250737 212301 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 355988996 536870912) BSN.abs_quadSignPos

noncomputable def hp763465 := hp763460 BSN.quadSignPos 7 8 9 874933 1000 62 127 536870912 268435456 9007199254740992

noncomputable def hp763466 := hp763465 Bool.false 924273576024 3987 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp763467 := hp763466 Bool.false 888503443 148846 Bool.true 208821128 Bool.true 719106757 28296951008113761 1 Bool.false 496768847

noncomputable def hp763468 := hp763467 Bool.true Bool.false 522566765 Bool.false Bool.false 887058047 182254 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 62 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 496768847 536870912) BSN.abs_quadSignPos

noncomputable def hp763469 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp763470 := hp763469 BSN.quadSignPos 5 6 7 874933 1000 97 12 536870912 268435456 9007199254740992

noncomputable def hp763471 := hp763470 Bool.false 924273576024 3987 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp763472 := hp763471 Bool.false 908914141 110609 Bool.false 835893782 Bool.false 109069440 28296951008113761 1 Bool.false 536819622

noncomputable def hp763473 := hp763472 Bool.true Bool.false 525829819 Bool.false Bool.false 888503443 148846 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 97 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536819622 536870912) BSN.abs_quadSignPos

noncomputable def hp763474 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp763475 := hp763474 BSN.quadSignPos 3 4 5 874933 1000 323 199 536870912 268435456 9007199254740992

noncomputable def hp763476 := hp763475 Bool.false 924273576024 3987 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp763477 := hp763476 Bool.false 468275398 65375 Bool.false 704276857 Bool.false 458975619 28296951008113761 1 Bool.false 518967390

noncomputable def hp763478 := hp763477 Bool.false Bool.false 405075012 Bool.false Bool.false 908914141 110609 BSN.abs_quadSignPos (BSN.cos_quad_nat3 323 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 518967390 536870912) BSN.abs_quadSignPos

noncomputable def hp763479 := hp763469 BSN.quadSignPos 1 2 3 874933 1000 709 484 536870912 268435456 9007199254740992

noncomputable def hp763480 := hp763479 Bool.false 924273576024 3987 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp763481 := hp763480 Bool.false 536870680 4042 Bool.false 774049488 Bool.false 62348931 28296951008113761 1 Bool.false 532408908

noncomputable def hp763482 := hp763481 Bool.true Bool.false 533254565 Bool.false Bool.false 468275398 65375 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 709 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 532408908 536870912) BSN.abs_quadSignPos

noncomputable def hp763483 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) 1) Bool.false

noncomputable def hp763484 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)))

noncomputable def hp763485 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000))) Bool.false 67108835 67108864

noncomputable def hp763486 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 115534197003) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 115534197003 67108864

noncomputable def hp763487 := nat_lit 125210902805996697230517452116249933558173811823825053099891

noncomputable def hp763488 := nat_lit 72729647720648946829718632061950176692333571855089664000

noncomputable def hp763489 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) Bool.false hp763487 hp763488 44145955917720544753

noncomputable def hp763490 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 874933 4000) (Real.log (Enclosure.sfrac Bool.false 3062032017956 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1749866))))))

noncomputable def hp763491 := nat_lit 246102249097977946628274087948640000

noncomputable def hp763492 := nat_lit 1291938071557455935151612750323660646720

noncomputable def hp763493 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp763490 (Enclosure.sfrac Bool.false 874933 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 874933 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp763491 hp763492)) Bool.false

noncomputable def hp763494 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 874933 1000) 874933 1000 3062032017956 16000000 1749866

noncomputable def hp763495 := hp763494 4000 2000 hp763491 hp763492 (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl rfl rfl rfl

noncomputable def hp763496 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp763490 (Enclosure.sfrac Bool.false 874933 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 874933 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp763491 hp763492) 31013478287702139325971 18014398509481984000

noncomputable def hp763497 := nat_lit 40067488897918943113765584677199978738615619783624016991965120

noncomputable def hp763498 := @hp763496 44145955917720544753 hp737908 hp763491 hp763492 0 1 hp763497 hp763487 hp763488 44145955917720544753 hp737908

noncomputable def hp763499 := @Enclosure.Real.IsNear.subLit_ff_p (hp763490 (Enclosure.sfrac Bool.false 874933 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 874933 2000) (Real.log Real.pi)) 40034746339721732410899 18014398509481984000 3678892899393043 1452000000000000000000

noncomputable def hp763500 := nat_lit 2081279296576355740535639506944000

noncomputable def hp763501 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 874933 4000) (Real.log (Enclosure.sfrac Bool.false 3062032017956 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1749866))))))

noncomputable def hp763502 := @hp763501 (Enclosure.sfrac Bool.false 874933 2000) 9583088441054006552887 3602879701896396800 3678892899393043 1452000000000000000000 874933 2000 0

noncomputable def hp763503 := nat_lit 16013898535888692964359600

noncomputable def hp763504 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 874933 4000) (Real.log (Enclosure.sfrac Bool.false 3062032017956 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1749866))))) 9584502773879425360887

noncomputable def hp763505 := nat_lit 21579196766094665666747097092483710976

noncomputable def hp763506 := @hp763504 3602879701896396800 10936678697634629 4356000000000000000000 883958015886755 2251799813685248 200000001089 8712000000000000000 hp763505 9583088441054006552887 3602879701896396800 3678892899393043

noncomputable def hp763507 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 874933 4000) (Real.log (Enclosure.sfrac Bool.false 3062032017956 16000000)) 874933 4000 0 1 54772781309422695 4503599627370496

noncomputable def hp763508 := nat_lit 117623652217465265832591360

noncomputable def hp763509 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3062032017956) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp763508 hp617687

noncomputable def hp763510 := BSN.log_rat_reduce_isNear 3062032017956 16000000 17 6124064035912 4194304000000 101602422 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp763511 := nat_lit 138878392024691010755303194531307719929254736202920664860552653706719738055784042418488156863788077792527669382282143717080322539520

noncomputable def hp763512 := nat_lit 1654044286943740772007146708631313581859893110129372508619764662154105870715100898550807888719671875569048550312301869324072648704

noncomputable def hp763513 := nat_lit 660944410034067724760776364785646714063122460058225236309349214283744755589540101278211476687740321632446254088425774776320

noncomputable def hp763514 := BSN.log_dyadic_bound 964880017956 5159184017956 6 5 hp763511 268435456 87120000 hp763512 hp763513 101602422 6124064035912

noncomputable def hp763515 := hp763514 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp763516 := @BSN.binarySplit_of_base5 (BSN.artanhP 964880017956) (BSN.artanhQ 5159184017956) 0 5 hp763512 hp763511 hp763513 rfl rfl rfl

noncomputable def hp763517 := hp763510 rfl rfl rfl rfl (hp763515 (hp763516 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp763518 := @hp763507 12500018513 1089000000000000000 9584502773879425360887 3602879701896396800 10936678697634629 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 874933 4000) (BSN.isNear_log_sfrac 3062032017956 16000000 54772781309422695 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp763509 1000001481040000 87120000000000000000000 54772781309422695 4503599627370496 12500018513 1089000000000000000 (hp763517 rfl rfl rfl) rfl)) rfl

noncomputable def hp763519 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1749866)))) 1 4

noncomputable def hp763520 := @hp763519 0 1 883958015886755 562949953421312 200000001089 2178000000000000000 883958015886755 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp763521 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1749866))) 884279719003555 562949953421312 1

noncomputable def hp763522 := @hp763521 2000000000000000 19175 33554432 1 10890000 29660709134927040348160 883958015886755 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp763523 := BSN.arctan_dyadic_bound_f 1000 1749866 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp763524 := hp763523 1 19175 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1749866) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1749866) 0 0 rfl)

noncomputable def hp763525 := hp763520 (hp763522 (hp763524 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp763526 := @hp763499 33606842354013 67108864000 2624799 536870912000 hp763500 31013478287702139325971 18014398509481984000 44145955917720544753 hp737908 (@hp763502 1 hp763503 40034746339721732410899 18014398509481984000 3678892899393043 1452000000000000000000 (@hp763506 1452000000000000000000 hp763518 hp763525 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 874933 2000) rfl rfl)

noncomputable def hp763527 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 874933 2000) (Real.log Real.pi) 874933 2000 0 1 38410761 33554432

noncomputable def hp763528 := hp763526 (@hp763527 3 268435456 33606842354013 67108864000 2624799 536870912000 (Enclosure.Real.IsNear.const Bool.false 874933 2000) hd4909 rfl) rfl

noncomputable def hp763529 := @hp763489 hp737908 115534197003 67108864 499 67108864 (@hp763493 hp763487 hp763488 44145955917720544753 hp737908 (hp763495 rfl rfl rfl rfl rfl) (hp763498 (hp763528 rfl) (Enclosure.Real.IsNear.const Bool.true hp763491 hp763492) rfl rfl)) rfl

noncomputable def hp763530 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 115534197003) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 8885858621134362116096) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp763531 := BSN.sin_reduce_arg_pos_rat_q0 115534197003 67108864 226375608064910080 72057594037927936 274 8885858621134362116096 hp617687 rfl rfl rfl rfl

noncomputable def hp763532 := BSN.cos_dyadic_bound_f 126275645 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp763533 := hp763532 1 67108835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 126275645) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp763534 := hp763533 (@BSN.binarySplit_of_le (BSN.cosOddP 126275645) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp763535 := @BSN.cos_arg_round Bool.false 67108835 67108864 8885858621134362116096 hp617687 126275645 137438953472 21801270 21780000 hp763534 rfl

noncomputable def hp763536 := hp763530 67108835 67108864 274 1000000000000000 21780000 10890000 hp763531 BSN.pi_near_15 hp763535 rfl rfl

noncomputable def hp763537 := @hp763486 499 67108864 Bool.false 67108835 67108864 1 10890000 hp763529 (Enclosure.sfrac_false_div 115534197003 67108864) (hp763536 rfl rfl) rfl

noncomputable def hp763538 := @hp763483 67108835 67108864 343826179 45675970560000 536870680 536870912 4042 536870912 (@hp763484 Bool.false 67108835 67108864 343826179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000)) (@hp763485 5501218864 730815528960000 67108835 67108864 343826179 45675970560000 (hp763537 rfl) rfl))

noncomputable def hp763539 := @hp763489 hp737908 924273576024 536870912 3987 536870912 (@hp763493 hp763487 hp763488 44145955917720544753 hp737908 (hp763495 rfl rfl rfl rfl rfl) (hp763498 (hp763528 rfl) (Enclosure.Real.IsNear.const Bool.true hp763491 hp763492) rfl rfl)) rfl

noncomputable def hp763540 := hp763482 (BSN.cos_quad_nat0 484 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 533254565 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl rfl (hp763538 rfl) hp763539

noncomputable def hp763541 := nat_lit 128751787897789676012119865143946400984703341307536368782173777794898591936119285327721384709067693634834457952256

noncomputable def hp763542 := nat_lit 46262034964634461893909671649149572952459442427919839054205116362413583092241495088255223973048988263776256

noncomputable def hp763543 := nat_lit 643190905481633902196419444605481184090136551915954042634457611842451471544401225383500076400313171561591672406016

noncomputable def hp763544 := BSN.sin_dyadic_bound_f 774049488 536870912 4 3 536870912 268435456 hp763541 hp642702 hp763542 hp763543 hp642705

noncomputable def hp763545 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 774049488) (BSN.sinEvenQ 536870912) 0 3 hp763541 hp642702 hp763542 rfl rfl rfl

noncomputable def hp763546 := hp763544 hp763542 532408908 rfl rfl rfl rfl rfl rfl rfl rfl (hp763545 rfl)

noncomputable def hp763547 := @BSN.binarySplit_of_base3 (BSN.sinOddP 774049488) (BSN.sinOddQ 536870912) 0 3 hp763543 hp642705 hp763542 rfl rfl rfl

noncomputable def hp763548 := nat_lit 15111794767729806429130558103121

noncomputable def hp763549 := BSN.cos_dyadic_bound_f 62348931 536870912 2 1 536870912 268435456 hp763548 hp708767 hp763548 hp763548 hp708768

noncomputable def hp763550 := @BSN.binarySplit_of_base (BSN.cosEvenP 62348931) (BSN.cosEvenQ 536870912) 0 1 hp763548 hp708767 hp763548 rfl rfl rfl

noncomputable def hp763551 := hp763549 hp763548 533254565 rfl rfl rfl rfl rfl rfl rfl rfl (hp763550 rfl)

noncomputable def hp763552 := @BSN.binarySplit_of_base (BSN.cosOddP 62348931) (BSN.cosOddQ 536870912) 0 1 hp763548 hp708768 hp763548 rfl rfl rfl

noncomputable def hp763553 := hp763540 hd4911 hd4913 hd4915 hd4917 hd4918 (hp763546 (hp763547 rfl) rfl rfl rfl rfl) (hp763551 (hp763552 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763554 := hp763478 (BSN.cos_quad_nat3 199 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 405075012 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl rfl (hp763553 rfl rfl rfl rfl rfl) hp763539

noncomputable def hp763555 := nat_lit 88197627040730967465192222778948860343942901090416568051821021458672473385519444556487641178387868105309290695201

noncomputable def hp763556 := nat_lit 14890902124809414429430483485078454111906483696236292184429786365164646903811080393232517102902790822496801

noncomputable def hp763557 := nat_lit 440721371134896038354382152372303096485890823789914910991385768088586309920008181235717660231703206209596461091361

noncomputable def hp763558 := BSN.sin_dyadic_bound_f 704276857 536870912 4 3 536870912 268435456 hp763555 hp642702 hp763556 hp763557 hp642705

noncomputable def hp763559 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 704276857) (BSN.sinEvenQ 536870912) 0 3 hp763555 hp642702 hp763556 rfl rfl rfl

noncomputable def hp763560 := hp763558 hp763556 518967390 rfl rfl rfl rfl rfl rfl rfl rfl (hp763559 rfl)

noncomputable def hp763561 := @BSN.binarySplit_of_base3 (BSN.sinOddP 704276857) (BSN.sinOddQ 536870912) 0 3 hp763557 hp642705 hp763556 rfl rfl rfl

noncomputable def hp763562 := nat_lit 11150554306465189575586729570625444910186536633824378819151040141766253985

noncomputable def hp763563 := nat_lit 1969322894211677775476297920292510830259575409946679052471730672590241

noncomputable def hp763564 := nat_lit 29200644279865820457757330107386167842477651871257268950739198521632185761

noncomputable def hp763565 := BSN.sin_dyadic_bound_f 458975619 536870912 3 2 536870912 268435456 hp763562 hp708845 hp763563 hp763564 hp708848

noncomputable def hp763566 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 458975619) (BSN.sinEvenQ 536870912) 0 2 hp763562 hp708845 hp763563 rfl rfl rfl

noncomputable def hp763567 := hp763565 hp763563 405075012 rfl rfl rfl rfl rfl rfl rfl rfl (hp763566 rfl)

noncomputable def hp763568 := @BSN.binarySplit_of_base2 (BSN.sinOddP 458975619) (BSN.sinOddQ 536870912) 0 2 hp763564 hp708848 hp763563 rfl rfl rfl

noncomputable def hp763569 := hp763554 hd4920 hd4922 hd4924 hd4926 hd4918 (hp763560 (hp763561 rfl) rfl rfl rfl rfl) (hp763567 (hp763568 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763570 := hp763473 (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 525829819 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl rfl (hp763569 rfl rfl rfl rfl rfl) hp763539

noncomputable def hp763571 := nat_lit 175188616601745699621348418040694559843976339883927146307121068859814771097695779632626329540044968048982498021376

noncomputable def hp763572 := nat_lit 116362524740664896359781568335124645674186133241119392207212021780125643971902920247070381992297212523646976

noncomputable def hp763573 := nat_lit 874892369785125661007506078877597627664585272476431881473996106649660044460528196962551030577173983874261887553536

noncomputable def hp763574 := BSN.sin_dyadic_bound_f 835893782 536870912 4 3 536870912 268435456 hp763571 hp642702 hp763572 hp763573 hp642705

noncomputable def hp763575 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 835893782) (BSN.sinEvenQ 536870912) 0 3 hp763571 hp642702 hp763572 rfl rfl rfl

noncomputable def hp763576 := hp763574 hp763572 536819622 rfl rfl rfl rfl rfl rfl rfl rfl (hp763575 rfl)

noncomputable def hp763577 := @BSN.binarySplit_of_base3 (BSN.sinOddP 835893782) (BSN.sinOddQ 536870912) 0 3 hp763573 hp642705 hp763572 rfl rfl rfl

noncomputable def hp763578 := nat_lit 141518212135983625098189864960000

noncomputable def hp763579 := BSN.cos_dyadic_bound_f 109069440 536870912 2 1 536870912 268435456 hp763578 hp708767 hp763578 hp763578 hp708768

noncomputable def hp763580 := @BSN.binarySplit_of_base (BSN.cosEvenP 109069440) (BSN.cosEvenQ 536870912) 0 1 hp763578 hp708767 hp763578 rfl rfl rfl

noncomputable def hp763581 := hp763579 hp763578 525829819 rfl rfl rfl rfl rfl rfl rfl rfl (hp763580 rfl)

noncomputable def hp763582 := @BSN.binarySplit_of_base (BSN.cosOddP 109069440) (BSN.cosOddQ 536870912) 0 1 hp763578 hp708768 hp763578 rfl rfl rfl

noncomputable def hp763583 := hp763570 hd4928 hd4930 hd4932 hd4934 hd4918 (hp763576 (hp763577 rfl) rfl rfl rfl rfl) (hp763581 (hp763582 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763584 := hp763468 (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 522566765 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl rfl (hp763583 rfl rfl rfl rfl rfl) hp763539

noncomputable def hp763585 := nat_lit 265394821905230099837769743266071325712822916776887214524418580142882816

noncomputable def hp763586 := nat_lit 3615725890859518605732138782967545398628458288432802520883775143936

noncomputable def hp763587 := nat_lit 796177234263908580476097765520648042047671493414084777968213972878360576

noncomputable def hp763588 := BSN.cos_dyadic_bound_f 208821128 536870912 3 2 536870912 268435456 hp763585 hp708868 hp763586 hp763587 hp708870

noncomputable def hp763589 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 208821128) (BSN.cosEvenQ 536870912) 0 2 hp763585 hp708868 hp763586 rfl rfl rfl

noncomputable def hp763590 := hp763588 hp763586 496768847 rfl rfl rfl rfl rfl rfl rfl rfl (hp763589 rfl)

noncomputable def hp763591 := @BSN.binarySplit_of_base2 (BSN.cosOddP 208821128) (BSN.cosOddQ 536870912) 0 2 hp763587 hp708870 hp763586 rfl rfl rfl

noncomputable def hp763592 := nat_lit 95872412131362486982844316793205304089118245299985940669915951807559975320569727024258084301209741669423906891601

noncomputable def hp763593 := nat_lit 19121432943940484901661982944769974578695048286305444935147102698464543279886559054846076179915393833445201

noncomputable def hp763594 := nat_lit 479046897545637185564902818931359862683974338717722018569153179609110669720663432484704064330869806093768495015761

noncomputable def hp763595 := BSN.sin_dyadic_bound_f 719106757 536870912 4 3 536870912 268435456 hp763592 hp642702 hp763593 hp763594 hp642705

noncomputable def hp763596 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 719106757) (BSN.sinEvenQ 536870912) 0 3 hp763592 hp642702 hp763593 rfl rfl rfl

noncomputable def hp763597 := hp763595 hp763593 522566765 rfl rfl rfl rfl rfl rfl rfl rfl (hp763596 rfl)

noncomputable def hp763598 := @BSN.binarySplit_of_base3 (BSN.sinOddP 719106757) (BSN.sinOddQ 536870912) 0 3 hp763594 hp642705 hp763593 rfl rfl rfl

noncomputable def hp763599 := hp763584 hd4936 hd4938 hd4940 hd4942 hd4918 (hp763590 (hp763591 rfl) rfl rfl rfl rfl) (hp763597 (hp763598 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763600 := hp763464 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 446969271 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl rfl (hp763599 rfl rfl rfl rfl rfl) hp763539

noncomputable def hp763601 := nat_lit 5937623623474049137639531005695941568863078390193380453698475424033669376

noncomputable def hp763602 := nat_lit 1808769120463551204141290581196926035652972817298899886221365129380096

noncomputable def hp763603 := nat_lit 17809253332181220310510310435925430854517929224945543561322983541842247936

noncomputable def hp763604 := BSN.cos_dyadic_bound_f 454122366 536870912 3 2 536870912 268435456 hp763601 hp708868 hp763602 hp763603 hp708870

noncomputable def hp763605 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 454122366) (BSN.cosEvenQ 536870912) 0 2 hp763601 hp708868 hp763602 rfl rfl rfl

noncomputable def hp763606 := hp763604 hp763602 355988996 rfl rfl rfl rfl rfl rfl rfl rfl (hp763605 rfl)

noncomputable def hp763607 := @BSN.binarySplit_of_base2 (BSN.cosOddP 454122366) (BSN.cosOddQ 536870912) 0 2 hp763603 hp708870 hp763602 rfl rfl rfl

noncomputable def hp763608 := nat_lit 19547982727203461418936266960613532071227728273121429503230439731839253345

noncomputable def hp763609 := nat_lit 6050794796835898835661044588823273577556095057246809446202450320440161

noncomputable def hp763610 := nat_lit 51187301093957045594337247967510679648375626085225344340785871520964950881

noncomputable def hp763611 := BSN.sin_dyadic_bound_f 528112629 536870912 3 2 536870912 268435456 hp763608 hp708845 hp763609 hp763610 hp708848

noncomputable def hp763612 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 528112629) (BSN.sinEvenQ 536870912) 0 2 hp763608 hp708845 hp763609 rfl rfl rfl

noncomputable def hp763613 := hp763611 hp763609 446969271 rfl rfl rfl rfl rfl rfl rfl rfl (hp763612 rfl)

noncomputable def hp763614 := @BSN.binarySplit_of_base2 (BSN.sinOddP 528112629) (BSN.sinOddQ 536870912) 0 2 hp763610 hp708848 hp763609 rfl rfl rfl

noncomputable def hp763615 := hp763600 hd4944 hd4946 hd4961 hd4963 hd4918 (hp763606 (hp763607 rfl) rfl rfl rfl rfl) (hp763613 (hp763614 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763616 := @hp763459 212301 268435456 (hp763615 rfl rfl rfl rfl rfl) (hp763615 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp763617 := @hp763457 Bool.false 909250737 268435456 212301 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 874933 1000)) (Enclosure.sfrac Bool.false 874933 1000) 11) hp763616

noncomputable def hp763618 := @Enclosure.Real.IsNear.mulLit_tf hp763448 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1))) 9767899 33554432 1

noncomputable def hp763619 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp763447 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763620 := @hp763619 1 1 0 1 9767899 33554432 1 33554432 9767899 33554432 1

noncomputable def hp763621 := @Enclosure.Real.IsNear.of_eq (hp763447 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763622 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 874933 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763623 := @hp763621 (@Inv.inv Real Real.instInv (Real.sqrt hp763449)) Bool.false 9767899 33554432 1 33554432 (hp763622 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 874933 1000) 874933 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000))))

noncomputable def hp763624 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp763449)) Bool.false 19535798 67108864 2 67108864 9767899 33554432

noncomputable def hp763625 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp763449) Bool.false 230530618 67108864 6 67108864 115265309 33554432 3 33554432

noncomputable def hp763626 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 874933 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763627 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 874933 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763628 := @hp763627 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 874933 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 9344903017631

noncomputable def hp763629 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 874933 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 874933 1000 0

noncomputable def hp763630 := @hp763629 1 10680707 67108864 1 67108864 9344903017631 67108864000 874933 67108864000 (Enclosure.Real.IsNear.const Bool.false 874933 1000) hd4949

noncomputable def hp763631 := @hp763628 67108864000 874933 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 874933 1000) 874933 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000))) (hp763630 rfl)

noncomputable def hp763632 := @hp763626 9344903017631 67108864000 874933 67108864000 395956363 395956401 33554432 hp763631 rfl rfl rfl

noncomputable def hp763633 := @Enclosure.Real.IsNear.recentre' hp763449 Bool.false 791912764 67108864 38 67108864 197978191 16777216 19 33554432 (hp763632 rfl rfl rfl)

noncomputable def hp763634 := @Enclosure.Real.IsNear.sqrt_image hp763449 197978191 16777216 19 33554432 115265306 115265312 33554432 (hp763633 rfl) rfl rfl

noncomputable def hp763635 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp763449) 115265309 33554432 3 33554432 9767898 9767900 33554432 (hp763625 (hp763634 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp763636 := @hp763620 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp763623 (@hp763624 1 33554432 (hp763635 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp763637 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763638 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp763639 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1))) (hp763637 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763638 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp763640 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 874933 1000) 874933 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl

noncomputable def hp763641 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763642 := @hp763641 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763638 (Enclosure.sfrac Bool.false 1 16)))) 107710521

noncomputable def hp763643 := @hp763642 33554432 1269 33554432 5821319 33554432 213771527 22837985280000 627017302397199 1125899906842624 1870244229954347 51087708272984064000

noncomputable def hp763644 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763645 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)))) 10453017

noncomputable def hp763646 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp763647 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 84375733) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false

noncomputable def hp763648 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1))) Bool.false 11874828754750724437325

noncomputable def hp763649 := nat_lit 512735433002542148644347333

noncomputable def hp763650 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp763651 := @Enclosure.Real.IsNear.subLit_ff_p hp763449 (Enclosure.sfrac Bool.false 11 1) 197978191 16777216 19 33554432 11 1 0

noncomputable def hp763652 := @hp763650 500000000000000 13428815 16777216 19 33554432 11874828754750724437325 2361183241434822606848 hp763649 hp682805 hd4948 (@hp763651 1 13428815 13428815 16777216 19 33554432 (hp763633 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763653 := @hp763647 84375733 16777216 15 4194304 Bool.false 20906034 67108864 1 10890000 (@hp763648 2361183241434822606848 hp763649 hp682805 84375733 16777216 15 4194304 (hp763652 rfl) rfl) (Enclosure.sfrac_false_div 84375733 16777216)

noncomputable def hp763654 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 84375733) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 765967209424183504142336) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp763655 := BSN.sin_reduce_arg_pos_rat_q3 84375733 16777216 226375608064910080 72057594037927936 0 765967209424183504142336 hp619230 rfl rfl rfl rfl

noncomputable def hp763656 := nat_lit 3593862653917552230397627345779799698172176

noncomputable def hp763657 := BSN.sin_dyadic_bound_f 43540194918 137438953472 2 1 67108864 21801270 hp763656 hp749778 hp763656 hp763656 hp749779

noncomputable def hp763658 := @BSN.binarySplit_of_base (BSN.sinEvenP 43540194918) (BSN.sinEvenQ 137438953472) 0 1 hp763656 hp749778 hp763656 rfl rfl rfl

noncomputable def hp763659 := hp763657 hp763656 20906034 rfl rfl rfl rfl rfl rfl rfl rfl (hp763658 rfl)

noncomputable def hp763660 := @BSN.binarySplit_of_base (BSN.sinOddP 43540194918) (BSN.sinOddQ 137438953472) 0 1 hp763656 hp749779 hp763656 rfl rfl rfl

noncomputable def hp763661 := @BSN.sin_arg_round Bool.false 20906034 67108864 765967209424183504142336 hp619230 43540194918 137438953472 21801270 21780000 (hp763659 (hp763660 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763662 := hp763654 20906034 67108864 0 1000000000000000 21780000 10890000 hp763655 BSN.pi_near_15 hp763661 rfl rfl

noncomputable def hp763663 := @hp763645 33554432 10471519 2854748160000 107709252 107711790 33554432 (@hp763646 20906034 67108864 167544304 45675970560000 10453017 33554432 10471519 2854748160000 (hp763653 (hp763662 rfl rfl) rfl rfl) rfl)

noncomputable def hp763664 := @hp763644 Bool.false 215421042 67108864 2538 67108864 107710521 33554432 1269 33554432 (hp763663 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp763665 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763638 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp763666 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763638 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 93712509)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp763667 := nat_lit 55318101809250522677155366205

noncomputable def hp763668 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763638 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp763667

noncomputable def hp763669 := nat_lit 44746273039607582553505739492267211

noncomputable def hp763670 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763638 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp763671 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp763672 := @hp763671 (Enclosure.sfrac Bool.false 1 16) 44965057574815 281474976710656 1658124509 1125899906842624 1 16 0

noncomputable def hp763673 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)) 180333072304225

noncomputable def hp763674 := @hp763673 281474976710656 1020590301 1125899906842624 13428815 16777216 19 33554432 754388483385107415040 44965057574815 281474976710656 1658124509

noncomputable def hp763675 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)) 13428815 16777216 19

noncomputable def hp763676 := @hp763675 33554432 13428815 16777216 19 33554432 180333072304225 281474976710656 1020590301 1125899906842624 (@hp763651 1 13428815 13428815 16777216 19 33554432 (hp763633 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763677 := hp763676 (@hp763651 1 13428815 13428815 16777216 19 33554432 (hp763633 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763678 := @hp763674 1125899906842624 (hp763677 rfl) (@hp763651 1 13428815 13428815 16777216 19 33554432 (hp763633 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763679 := @hp763670 500000000000000 62557243619231 281474976710656 1658124509 1125899906842624 hp763667 hp631146 hp763669 hp682143 hd4948 (@hp763672 1 1000915897907696 62557243619231 281474976710656 1658124509 1125899906842624 (hp763678 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp763680 := @hp763666 93712509 67108864 311 33554432 Bool.false 5821319 33554432 1 10890000 (@hp763668 hp631146 hp763669 hp682143 93712509 67108864 311 33554432 (hp763679 rfl) rfl) (Enclosure.sfrac_true_div 93712509 67108864)

noncomputable def hp763681 := nat_lit 634654360494283594664306534431169569898000241046119856082534372815705721991186869949690367110087768561

noncomputable def hp763682 := nat_lit 458744411618312629364881537858372404420549457215209808231502890595207616401229133627771042986481

noncomputable def hp763683 := nat_lit 3844437501919523865395540131034554198463239535075525653726724707313829275165624571714563292524348766705

noncomputable def hp763684 := BSN.cos_dyadic_bound_f 93712509 67108864 4 3 33554432 10890000 hp763681 hp745658 hp763682 hp763683 hp745661

noncomputable def hp763685 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 93712509) (BSN.cosEvenQ 67108864) 0 3 hp763681 hp745658 hp763682 rfl rfl rfl

noncomputable def hp763686 := hp763684 hp763682 5821319 rfl rfl rfl rfl rfl rfl rfl rfl (hp763685 rfl)

noncomputable def hp763687 := @BSN.binarySplit_of_base3 (BSN.cosOddP 93712509) (BSN.cosOddQ 67108864) 0 3 hp763683 hp745661 hp763682 rfl rfl rfl

noncomputable def hp763688 := hp763680 (BSN.cos_neg_of_bound 93712509 67108864 Bool.false 5821319 33554432 1 10890000 (hp763686 (hp763687 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp763689 := hp763643 hp763664 (@hp763665 5821319 33554432 3420344432 365407764480000 5821319 33554432 213771527 22837985280000 (hp763688 rfl) rfl)

noncomputable def hp763690 := @hp763618 33554432 627017302397199 1125899906842624 1870244229954347 51087708272984064000 6124641681068297714901 37778931862957161709568 731872380954693558637 hp763445 (hp763636 rfl) (@hp763639 Bool.false 627017302397199 1125899906842624 1870244229954347 51087708272984064000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763449 (Enclosure.sfrac Bool.false 11 1)) (hp763640 rfl (hp763452 rfl rfl))) (hp763689 rfl))

noncomputable def hp763691 := @hp763446 54961730151268642414957 hp763445 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 874933 1000))) (@hp763451 54961730151268642414957 hp763445 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 874933 1000) 11 (hp763452 rfl rfl)) (@hp763455 54961730151268642414957 hp763445 hp763617 (hp763690 rfl) rfl rfl))

theorem hd5063 : hp763444 hp763445 := hp763691

noncomputable def hp763692 := nat_lit 2060339746979626872400409

noncomputable def hp763693 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 876205 1000)) Bool.true 55945259405031329085 147573952589676412928 hp763692

noncomputable def hp763694 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 876205 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 876205 1000)) Bool.true 55945259405031329085 147573952589676412928

noncomputable def hp763695 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 876205 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763696 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp763695 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763697 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 876205 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763698 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp763696 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp763699 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 876205 1000)) hp763698 Bool.true 55945259405031329085 147573952589676412928

noncomputable def hp763700 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 876205 1000) 876205 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl

noncomputable def hp763701 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp763696 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp763702 := nat_lit 7508845609713936758609018880

noncomputable def hp763703 := @hp763701 73063371 134217728 212607 268435456 24388766573980463811 147573952589676412928 23788923330691329616409 hp754729 hp763702 55945259405031329085 147573952589676412928

noncomputable def hp763704 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) 11)

noncomputable def hp763705 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) 11) hp763704

noncomputable def hp763706 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) 11)

noncomputable def hp763707 := @hp763706 146126742 536870912 212607 536870912 146126742 536870912 212607 536870912 156902394490257408 73063371 134217728

noncomputable def hp763708 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp763709 := hp763708 BSN.quadSignPos 9 10 11 876205 1000 186 239 536870912 268435456 9007199254740992

noncomputable def hp763710 := hp763709 Bool.false 925959313244 3992 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp763711 := hp763710 Bool.true 135610397 182517 Bool.true 340820042 Bool.true 479897609 28296951008113761 1 Bool.false 432274727

noncomputable def hp763712 := hp763711 Bool.true Bool.false 418494824 Bool.false Bool.true 146126742 212607 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 186 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 432274727 536870912) BSN.abs_quadSignPos

noncomputable def hp763713 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp763714 := hp763713 BSN.quadSignPos 7 8 9 876205 1000 61 127 536870912 268435456 9007199254740992

noncomputable def hp763715 := hp763714 Bool.false 925959313244 3992 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp763716 := hp763715 Bool.true 96902969 149061 Bool.true 786448977 Bool.true 533853743 28296951008113761 1 Bool.false 533862082

noncomputable def hp763717 := hp763716 Bool.true Bool.false 450123986 Bool.false Bool.true 135610397 182517 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 61 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533862082 536870912) BSN.abs_quadSignPos

noncomputable def hp763718 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp763719 := hp763718 BSN.quadSignPos 5 6 7 876205 1000 98 12 536870912 268435456 9007199254740992

noncomputable def hp763720 := hp763719 Bool.false 925959313244 3992 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp763721 := hp763720 Bool.true 82928931 110770 Bool.false 454723971 Bool.false 465945028 28296951008113761 1 Bool.false 355538443

noncomputable def hp763722 := hp763721 Bool.true Bool.false 347053574 Bool.false Bool.true 96902969 149061 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 98 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 355538443 536870912) BSN.abs_quadSignPos

noncomputable def hp763723 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp763724 := hp763723 BSN.quadSignPos 3 4 5 876205 1000 324 200 536870912 268435456 9007199254740992

noncomputable def hp763725 := hp763724 Bool.false 925959313244 3992 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp763726 := hp763725 Bool.true 423713767 65471 Bool.false 599999097 Bool.false 202313174 28296951008113761 1 Bool.false 235071371

noncomputable def hp763727 := hp763726 Bool.false Bool.false 499200274 Bool.false Bool.true 82928931 110770 BSN.abs_quadSignPos (BSN.cos_quad_nat0 324 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 235071371 536870912) BSN.abs_quadSignPos

noncomputable def hp763728 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp763729 := hp763728 BSN.quadSignNeg 1 2 3 876205 1000 711 485 536870912 268435456 9007199254740992

noncomputable def hp763730 := hp763729 Bool.false 925959313244 3992 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp763731 := hp763730 Bool.true 536870760 4050 Bool.false 299806943 Bool.false 154529189 28296951008113761 1 Bool.false 284465724

noncomputable def hp763732 := hp763731 Bool.false Bool.false 152404274 Bool.true Bool.true 423713767 65471 BSN.abs_quadSignPos (BSN.cos_quad_nat3 711 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 284465724 536870912) BSN.abs_quadSignNeg

noncomputable def hp763733 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) 1) Bool.true

noncomputable def hp763734 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)))

noncomputable def hp763735 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000))) Bool.true 67108845 67108864

noncomputable def hp763736 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 115744914155) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 115744914155 67108864

noncomputable def hp763737 := nat_lit 1619679411909387666707446834722413405534617783780212023

noncomputable def hp763738 := nat_lit 939089602082514904010317792156860486084994478899200

noncomputable def hp763739 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) Bool.false hp763737 hp763738 2947329196215434727

noncomputable def hp763740 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 876205 4000) (Real.log (Enclosure.sfrac Bool.false 3070941808100 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1752410))))))

noncomputable def hp763741 := nat_lit 247896406468402870887136301500000000

noncomputable def hp763742 := nat_lit 1303248623022605501301393316144845000000

noncomputable def hp763743 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp763740 (Enclosure.sfrac Bool.false 876205 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 876205 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp763741 hp763742)) Bool.false

noncomputable def hp763744 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 876205 1000) 876205 1000 3070941808100 16000000 1752410

noncomputable def hp763745 := hp763744 4000 2000 hp763741 hp763742 (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl rfl rfl rfl

noncomputable def hp763746 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp763740 (Enclosure.sfrac Bool.false 876205 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 876205 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp763741 hp763742) 6214008447525057231967 3602879701896396800

noncomputable def hp763747 := nat_lit 8098397059546938333537234173612067027673088918901060115000000

noncomputable def hp763748 := @hp763746 2947329196215434727 396492800000000000000000 hp763741 hp763742 0 1 hp763747 hp763737 hp763738 2947329196215434727 396492800000000000000000

noncomputable def hp763749 := @Enclosure.Real.IsNear.subLit_ff_p (hp763740 (Enclosure.sfrac Bool.false 876205 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 876205 2000) (Real.log Real.pi)) 8020885128029696457823 3602879701896396800 245612860482837 96800000000000000000

noncomputable def hp763750 := nat_lit 83403009559962040474457971097600

noncomputable def hp763751 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 876205 4000) (Real.log (Enclosure.sfrac Bool.false 3070941808100 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1752410))))))

noncomputable def hp763752 := @hp763751 (Enclosure.sfrac Bool.false 876205 2000) 1919863146525952527379 720575940379279360 245612860482837 96800000000000000000 876205 2000 0

noncomputable def hp763753 := nat_lit 3208354051211878583129200

noncomputable def hp763754 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 876205 4000) (Real.log (Enclosure.sfrac Bool.false 3070941808100 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1752410))))) 1920146013241360144339

noncomputable def hp763755 := nat_lit 4323147475648313882229525497608404992

noncomputable def hp763756 := @hp763754 720575940379279360 199137794930603 79200000000000000000 883958485648803 2251799813685248 200000001089 8712000000000000000 hp763755 1919863146525952527379 720575940379279360 245612860482837

noncomputable def hp763757 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 876205 4000) (Real.log (Enclosure.sfrac Bool.false 3070941808100 16000000)) 876205 4000 0 1 54785866699041895 4503599627370496

noncomputable def hp763758 := nat_lit 117651752877700206779432960

noncomputable def hp763759 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3070941808100) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp763758 hp617687

noncomputable def hp763760 := BSN.log_rat_reduce_isNear 3070941808100 16000000 17 6141883616200 4194304000000 102382372 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp763761 := nat_lit 141295514365948475668511399095156932395839500863944676051666312527486616856939145618440053020270791503689198639500000000000000000000

noncomputable def hp763762 := nat_lit 1708705303018742198639585099606930993587491628413924141531737645765759394124815522050983382921942123558280432900000000000000000000

noncomputable def hp763763 := nat_lit 724576186432838323177424532757684581001415923487834228656321799019851518241542034503524907598626581694500000000000000000000

noncomputable def hp763764 := BSN.log_dyadic_bound 973789808100 5168093808100 6 5 hp763761 268435456 87120000 hp763762 hp763763 102382372 6141883616200

noncomputable def hp763765 := hp763764 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp763766 := @BSN.binarySplit_of_base5 (BSN.artanhP 973789808100) (BSN.artanhQ 5168093808100) 0 5 hp763762 hp763761 hp763763 rfl rfl rfl

noncomputable def hp763767 := hp763760 rfl rfl rfl rfl (hp763765 (hp763766 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp763768 := @hp763757 12500018513 1089000000000000000 1920146013241360144339 720575940379279360 199137794930603 79200000000000000000 (Enclosure.Real.IsNear.const Bool.false 876205 4000) (BSN.isNear_log_sfrac 3070941808100 16000000 54785866699041895 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp763759 1000001481040000 87120000000000000000000 54785866699041895 4503599627370496 12500018513 1089000000000000000 (hp763767 rfl rfl rfl) rfl)) rfl

noncomputable def hp763769 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1752410)))) 1 4

noncomputable def hp763770 := @hp763769 0 1 883958485648803 562949953421312 200000001089 2178000000000000000 883958485648803 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp763771 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1752410))) 884279719003555 562949953421312 1

noncomputable def hp763772 := @hp763771 2000000000000000 19147 33554432 1 10890000 29660724897525736144896 883958485648803 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp763773 := BSN.arctan_dyadic_bound_f 1000 1752410 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp763774 := hp763773 1 19147 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1752410) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1752410) 0 0 rfl)

noncomputable def hp763775 := hp763770 (hp763772 (hp763774 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp763776 := @hp763749 6731140168401 13421772800 525723 107374182400 hp763750 6214008447525057231967 3602879701896396800 2947329196215434727 396492800000000000000000 (@hp763752 1 hp763753 8020885128029696457823 3602879701896396800 245612860482837 96800000000000000000 (@hp763756 96800000000000000000 hp763768 hp763775 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 876205 2000) rfl rfl)

noncomputable def hp763777 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 876205 2000) (Real.log Real.pi) 876205 2000 0 1 38410761 33554432

noncomputable def hp763778 := hp763776 (@hp763777 3 268435456 6731140168401 13421772800 525723 107374182400 (Enclosure.Real.IsNear.const Bool.false 876205 2000) hd4909 rfl) rfl

noncomputable def hp763779 := @hp763739 396492800000000000000000 115744914155 67108864 125 16777216 (@hp763743 hp763737 hp763738 2947329196215434727 396492800000000000000000 (hp763745 rfl rfl rfl rfl rfl) (hp763748 (hp763778 rfl) (Enclosure.Real.IsNear.const Bool.true hp763741 hp763742) rfl rfl)) rfl

noncomputable def hp763780 := nat_lit 15184617955364489941483520

noncomputable def hp763781 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 115744914155) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp763780) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp763782 := BSN.sin_reduce_arg_pos_rat_q1 115744914155 67108864 226375608064910080 72057594037927936 274 hp763780 hp617687 rfl rfl rfl rfl

noncomputable def hp763783 := nat_lit 14353115662586758346764632225600103793420394011347285816925870359098540990234477523116823715363322780150079837826694801399546862588961994575761

noncomputable def hp763784 := nat_lit 10192690288690885878242554269220844716424615300135345933118789610938615487591691451530153083851964386398386342025277546514885929423081361

noncomputable def hp763785 := nat_lit 71676569214813095933919517860926853580358187382798367323424236298876954181881443262660142506341269373037142781703675746350678146368311124037521

noncomputable def hp763786 := BSN.sin_dyadic_bound_f 215786399669 137438953472 4 3 67108864 21801270 hp763783 hp737934 hp763784 hp763785 hp737937

noncomputable def hp763787 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215786399669) (BSN.sinEvenQ 137438953472) 0 3 hp763783 hp737934 hp763784 rfl rfl rfl

noncomputable def hp763788 := hp763786 hp763784 67108845 rfl rfl rfl rfl rfl rfl rfl rfl (hp763787 rfl)

noncomputable def hp763789 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215786399669) (BSN.sinOddQ 137438953472) 0 3 hp763785 hp737937 hp763784 rfl rfl rfl

noncomputable def hp763790 := @BSN.sin_arg_round Bool.false 67108845 67108864 hp763780 hp617687 215786399669 137438953472 21801270 21780000 (hp763788 (hp763789 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763791 := hp763781 67108845 67108864 274 1000000000000000 21780000 10890000 hp763782 BSN.pi_near_15 hp763790 rfl rfl

noncomputable def hp763792 := @hp763736 125 16777216 Bool.true 67108845 67108864 1 10890000 hp763779 (Enclosure.sfrac_false_div 115744914155 67108864) (hp763791 rfl rfl) rfl

noncomputable def hp763793 := @hp763733 67108845 67108864 86126701 11418992640000 536870760 536870912 4050 536870912 (@hp763734 Bool.true 67108845 67108864 86126701 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000)) (@hp763735 1378027216 182703882240000 67108845 67108864 86126701 11418992640000 (hp763792 rfl) rfl))

noncomputable def hp763794 := @hp763739 396492800000000000000000 925959313244 536870912 3992 536870912 (@hp763743 hp763737 hp763738 2947329196215434727 396492800000000000000000 (hp763745 rfl rfl rfl rfl rfl) (hp763748 (hp763778 rfl) (Enclosure.Real.IsNear.const Bool.true hp763741 hp763742) rfl rfl)) rfl

noncomputable def hp763795 := hp763732 (BSN.cos_quad_nat1 485 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 152404274 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl rfl (hp763793 rfl) hp763794

noncomputable def hp763796 := nat_lit 2029747404295188691541111910864120288289793890634198452900268174025156865

noncomputable def hp763797 := nat_lit 65272987270192467824625783958265503653619532513752991716023475104001

noncomputable def hp763798 := nat_lit 5315899426412771023374053229565334991848306710513116538466495465391909121

noncomputable def hp763799 := BSN.sin_dyadic_bound_f 299806943 536870912 3 2 536870912 268435456 hp763796 hp708845 hp763797 hp763798 hp708848

noncomputable def hp763800 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 299806943) (BSN.sinEvenQ 536870912) 0 2 hp763796 hp708845 hp763797 rfl rfl rfl

noncomputable def hp763801 := hp763799 hp763797 284465724 rfl rfl rfl rfl rfl rfl rfl rfl (hp763800 rfl)

noncomputable def hp763802 := @BSN.binarySplit_of_base2 (BSN.sinOddP 299806943) (BSN.sinOddQ 536870912) 0 2 hp763798 hp708848 hp763797 rfl rfl rfl

noncomputable def hp763803 := nat_lit 570219547815701842295186831193841

noncomputable def hp763804 := BSN.sin_dyadic_bound_f 154529189 536870912 2 1 536870912 268435456 hp763803 hp708890 hp763803 hp763803 hp708891

noncomputable def hp763805 := @BSN.binarySplit_of_base (BSN.sinEvenP 154529189) (BSN.sinEvenQ 536870912) 0 1 hp763803 hp708890 hp763803 rfl rfl rfl

noncomputable def hp763806 := hp763804 hp763803 152404274 rfl rfl rfl rfl rfl rfl rfl rfl (hp763805 rfl)

noncomputable def hp763807 := @BSN.binarySplit_of_base (BSN.sinOddP 154529189) (BSN.sinOddQ 536870912) 0 1 hp763803 hp708891 hp763803 rfl rfl rfl

noncomputable def hp763808 := hp763795 hd4911 hd4913 hd4915 hd4917 hd4918 (hp763801 (hp763802 rfl) rfl rfl rfl rfl) (hp763806 (hp763807 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763809 := hp763727 (BSN.cos_quad_nat0 200 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 499200274 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl rfl (hp763808 rfl rfl rfl rfl rfl) hp763794

noncomputable def hp763810 := nat_lit 17868588239478349365598912989927302900212325187851926730094140900848959210653781885367004817017080389921654117921

noncomputable def hp763811 := nat_lit 2176743023636420990627593814250839989430299865056703999781020891707322603967522852825346730931389313259041

noncomputable def hp763812 := nat_lit 108335713675159281302449321405627542730662655076541008219544604719378217021915378741611369203212124585348898166305

noncomputable def hp763813 := BSN.cos_dyadic_bound_f 599999097 536870912 4 3 536870912 268435456 hp763810 hp716712 hp763811 hp763812 hp716714

noncomputable def hp763814 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 599999097) (BSN.cosEvenQ 536870912) 0 3 hp763810 hp716712 hp763811 rfl rfl rfl

noncomputable def hp763815 := hp763813 hp763811 235071371 rfl rfl rfl rfl rfl rfl rfl rfl (hp763814 rfl)

noncomputable def hp763816 := @BSN.binarySplit_of_base3 (BSN.cosOddP 599999097) (BSN.cosOddQ 536870912) 0 3 hp763812 hp716714 hp763811 rfl rfl rfl

noncomputable def hp763817 := nat_lit 233824840149890745053188861149676933608462953815950266935935347928883456

noncomputable def hp763818 := nat_lit 2806682641715661020848327250181455842948845578833386322721472798976

noncomputable def hp763819 := nat_lit 701468907084388803837524886794530437913702963756693134035160600841052416

noncomputable def hp763820 := BSN.cos_dyadic_bound_f 202313174 536870912 3 2 536870912 268435456 hp763817 hp708868 hp763818 hp763819 hp708870

noncomputable def hp763821 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 202313174) (BSN.cosEvenQ 536870912) 0 2 hp763817 hp708868 hp763818 rfl rfl rfl

noncomputable def hp763822 := hp763820 hp763818 499200274 rfl rfl rfl rfl rfl rfl rfl rfl (hp763821 rfl)

noncomputable def hp763823 := @BSN.binarySplit_of_base2 (BSN.cosOddP 202313174) (BSN.cosOddQ 536870912) 0 2 hp763819 hp708870 hp763818 rfl rfl rfl

noncomputable def hp763824 := hp763809 hd4920 hd4922 hd4924 hd4926 hd4918 (hp763815 (hp763816 rfl) rfl rfl rfl rfl) (hp763822 (hp763823 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763825 := hp763722 (BSN.cos_quad_nat0 12 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 347053574 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl rfl (hp763824 rfl rfl rfl rfl rfl) hp763794

noncomputable def hp763826 := nat_lit 5969159658780132630677078328651414467924780147030855471741148109409639841

noncomputable def hp763827 := nat_lit 1828027778189420974205826015257960841655075882148729111326940264684961

noncomputable def hp763828 := nat_lit 17903822920784019050082823333923727482091030289328268957000790447699549601

noncomputable def hp763829 := BSN.cos_dyadic_bound_f 454723971 536870912 3 2 536870912 268435456 hp763826 hp708868 hp763827 hp763828 hp708870

noncomputable def hp763830 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 454723971) (BSN.cosEvenQ 536870912) 0 2 hp763826 hp708868 hp763827 rfl rfl rfl

noncomputable def hp763831 := hp763829 hp763827 355538443 rfl rfl rfl rfl rfl rfl rfl rfl (hp763830 rfl)

noncomputable def hp763832 := @BSN.binarySplit_of_base2 (BSN.cosOddP 454723971) (BSN.cosOddQ 536870912) 0 2 hp763828 hp708870 hp763827 rfl rfl rfl

noncomputable def hp763833 := nat_lit 6580731157458917223060553624393200012183584591802269964889382019850633216

noncomputable def hp763834 := nat_lit 2221659277810602114089972032844478725469483775763658031100610792718336

noncomputable def hp763835 := nat_lit 19737750153821130464953480929113911079099814807855282578605944837966462976

noncomputable def hp763836 := BSN.cos_dyadic_bound_f 465945028 536870912 3 2 536870912 268435456 hp763833 hp708868 hp763834 hp763835 hp708870

noncomputable def hp763837 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 465945028) (BSN.cosEvenQ 536870912) 0 2 hp763833 hp708868 hp763834 rfl rfl rfl

noncomputable def hp763838 := hp763836 hp763834 347053574 rfl rfl rfl rfl rfl rfl rfl rfl (hp763837 rfl)

noncomputable def hp763839 := @BSN.binarySplit_of_base2 (BSN.cosOddP 465945028) (BSN.cosOddQ 536870912) 0 2 hp763835 hp708870 hp763834 rfl rfl rfl

noncomputable def hp763840 := hp763825 hd4928 hd4930 hd4932 hd4934 hd4918 (hp763831 (hp763832 rfl) rfl rfl rfl rfl) (hp763838 (hp763839 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763841 := hp763717 (BSN.cos_quad_nat3 127 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 450123986 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl rfl (hp763840 rfl rfl rfl rfl rfl) hp763794

noncomputable def hp763842 := nat_lit 137214894549629136422094840482591179148808420302865880671739704275857523959921003359916383624291151650773152157121

noncomputable def hp763843 := nat_lit 55981769553243465985710723796732987132289578151712347232774566705626499367151069231997434390363471963344321

noncomputable def hp763844 := nat_lit 685429415565160117836476382274644328553430451228058416950249424660619286899210953704088538043886992090273621855681

noncomputable def hp763845 := BSN.sin_dyadic_bound_f 786448977 536870912 4 3 536870912 268435456 hp763842 hp642702 hp763843 hp763844 hp642705

noncomputable def hp763846 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 786448977) (BSN.sinEvenQ 536870912) 0 3 hp763842 hp642702 hp763843 rfl rfl rfl

noncomputable def hp763847 := hp763845 hp763843 533862082 rfl rfl rfl rfl rfl rfl rfl rfl (hp763846 rfl)

noncomputable def hp763848 := @BSN.binarySplit_of_base3 (BSN.sinOddP 786448977) (BSN.sinOddQ 536870912) 0 3 hp763844 hp642705 hp763843 rfl rfl rfl

noncomputable def hp763849 := nat_lit 20412248360911919787776087762039982108281936606771199196565373796310043265

noncomputable def hp763850 := nat_lit 6597483857188968698665651114497078013101994703720724674870287711324801

noncomputable def hp763851 := nat_lit 53449968828524341113901437846395529300145764073928069103435712810231777921

noncomputable def hp763852 := BSN.sin_dyadic_bound_f 533853743 536870912 3 2 536870912 268435456 hp763849 hp708845 hp763850 hp763851 hp708848

noncomputable def hp763853 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 533853743) (BSN.sinEvenQ 536870912) 0 2 hp763849 hp708845 hp763850 rfl rfl rfl

noncomputable def hp763854 := hp763852 hp763850 450123986 rfl rfl rfl rfl rfl rfl rfl rfl (hp763853 rfl)

noncomputable def hp763855 := @BSN.binarySplit_of_base2 (BSN.sinOddP 533853743) (BSN.sinOddQ 536870912) 0 2 hp763851 hp708848 hp763850 rfl rfl rfl

noncomputable def hp763856 := hp763841 hd4936 hd4938 hd4940 hd4942 hd4918 (hp763847 (hp763848 rfl) rfl rfl rfl rfl) (hp763854 (hp763855 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763857 := hp763712 (BSN.cos_quad_nat3 239 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 418494824 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl rfl (hp763856 rfl rfl rfl rfl rfl) hp763794

noncomputable def hp763858 := nat_lit 1883350988861347998535381900502048023023089947434628100328624678920970496

noncomputable def hp763859 := nat_lit 182054326793221505069910052407786895098699387927299386763980118876416

noncomputable def hp763860 := nat_lit 5649688857930457552596005881401328495279072443528029702212346076525158656

noncomputable def hp763861 := BSN.cos_dyadic_bound_f 340820042 536870912 3 2 536870912 268435456 hp763858 hp708868 hp763859 hp763860 hp708870

noncomputable def hp763862 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 340820042) (BSN.cosEvenQ 536870912) 0 2 hp763858 hp708868 hp763859 rfl rfl rfl

noncomputable def hp763863 := hp763861 hp763859 432274727 rfl rfl rfl rfl rfl rfl rfl rfl (hp763862 rfl)

noncomputable def hp763864 := @BSN.binarySplit_of_base2 (BSN.cosOddP 340820042) (BSN.cosOddQ 536870912) 0 2 hp763860 hp708870 hp763859 rfl rfl rfl

noncomputable def hp763865 := nat_lit 13327457546474976044037586339891459428688779858857298355884230744227977025

noncomputable def hp763866 := nat_lit 2813122790489429158080000693704716633213410158281205779978779583321921

noncomputable def hp763867 := nat_lit 34900691375297478182413929936687824200588268394846183265576829163176466241

noncomputable def hp763868 := BSN.sin_dyadic_bound_f 479897609 536870912 3 2 536870912 268435456 hp763865 hp708845 hp763866 hp763867 hp708848

noncomputable def hp763869 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 479897609) (BSN.sinEvenQ 536870912) 0 2 hp763865 hp708845 hp763866 rfl rfl rfl

noncomputable def hp763870 := hp763868 hp763866 418494824 rfl rfl rfl rfl rfl rfl rfl rfl (hp763869 rfl)

noncomputable def hp763871 := @BSN.binarySplit_of_base2 (BSN.sinOddP 479897609) (BSN.sinOddQ 536870912) 0 2 hp763867 hp708848 hp763866 rfl rfl rfl

noncomputable def hp763872 := hp763857 hd4944 hd4946 hd4961 hd4963 hd4918 (hp763863 (hp763864 rfl) rfl rfl rfl rfl) (hp763870 (hp763871 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763873 := @hp763707 212607 268435456 (hp763872 rfl rfl rfl rfl rfl) (hp763872 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp763874 := @hp763705 Bool.true 73063371 134217728 212607 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 876205 1000)) (Enclosure.sfrac Bool.false 876205 1000) 11) hp763873

noncomputable def hp763875 := @Enclosure.Real.IsNear.mulLit_tf hp763696 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1))) 19071 65536 1

noncomputable def hp763876 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp763695 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763877 := @hp763876 1 1 0 1 19071 65536 1 33554432 19071 65536 1

noncomputable def hp763878 := @Enclosure.Real.IsNear.of_eq (hp763695 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp763879 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 876205 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763880 := @hp763878 (@Inv.inv Real Real.instInv (Real.sqrt hp763697)) Bool.false 19071 65536 1 33554432 (hp763879 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 876205 1000) 876205 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000))))

noncomputable def hp763881 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp763697)) Bool.false 19528704 67108864 2 67108864 19071 65536

noncomputable def hp763882 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp763697) Bool.false 230614360 67108864 6 67108864 28826795 8388608 3 33554432

noncomputable def hp763883 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 876205 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763884 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 876205 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp763885 := @hp763884 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 876205 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 1871697775387

noncomputable def hp763886 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 876205 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 876205 1000 0

noncomputable def hp763887 := @hp763886 1 10680707 67108864 1 67108864 1871697775387 13421772800 175241 13421772800 (Enclosure.Real.IsNear.const Bool.false 876205 1000) hd4949

noncomputable def hp763888 := @hp763885 13421772800 175241 13421772800 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 876205 1000) 876205 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000))) (hp763887 rfl)

noncomputable def hp763889 := @hp763883 1871697775387 13421772800 175241 13421772800 396244084 396244122 33554432 hp763888 rfl rfl rfl

noncomputable def hp763890 := @Enclosure.Real.IsNear.recentre' hp763697 Bool.false 792488206 67108864 38 67108864 396244103 33554432 19 33554432 (hp763889 rfl rfl rfl)

noncomputable def hp763891 := @Enclosure.Real.IsNear.sqrt_image hp763697 396244103 33554432 19 33554432 115307177 115307183 33554432 (hp763890 rfl) rfl rfl

noncomputable def hp763892 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp763697) 28826795 8388608 3 33554432 9764351 9764353 33554432 (hp763882 (hp763891 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp763893 := @hp763877 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp763880 (@hp763881 1 33554432 (hp763892 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp763894 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763895 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp763896 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1))) (hp763894 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763895 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp763897 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 876205 1000) 876205 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl

noncomputable def hp763898 := @Enclosure.Real.IsNear.mulLit_ff (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763899 := @hp763898 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763895 (Enclosure.sfrac Bool.false 1 16)))) 185259161

noncomputable def hp763900 := @hp763899 67108864 1869 67108864 6902981 33554432 215132777 22837985280000 1278840468458941 2251799813685248 9727384002196187 306526249637904384000

noncomputable def hp763901 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp763902 := @Enclosure.Real.IsNear.inv_image (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)))) 24309727

noncomputable def hp763903 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)))) Bool.false

noncomputable def hp763904 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 341118541) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp763905 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1))) Bool.false 24004083354532870722805

noncomputable def hp763906 := nat_lit 102547086601002730643018433

noncomputable def hp763907 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp763908 := @Enclosure.Real.IsNear.subLit_ff_p hp763697 (Enclosure.sfrac Bool.false 11 1) 396244103 33554432 19 33554432 11 1 0

noncomputable def hp763909 := @hp763907 500000000000000 27145351 33554432 19 33554432 24004083354532870722805 4722366482869645213696 hp763906 hp682117 hd4948 (@hp763908 1 27145351 27145351 33554432 19 33554432 (hp763890 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763910 := @hp763904 341118541 67108864 239 67108864 Bool.false 24309727 67108864 1 10890000 (@hp763905 4722366482869645213696 hp763906 hp682117 341118541 67108864 239 67108864 (hp763909 rfl) rfl) (Enclosure.sfrac_false_div 341118541 67108864)

noncomputable def hp763911 := nat_lit 3584933008740491190075392

noncomputable def hp763912 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 341118541) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp763911) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp763913 := BSN.sin_reduce_arg_pos_rat_q3 341118541 67108864 226375608064910080 72057594037927936 0 hp763911 hp617687 rfl rfl rfl rfl

noncomputable def hp763914 := nat_lit 6736044935785094408788828503464727506250000

noncomputable def hp763915 := BSN.sin_dyadic_bound_f 50944962150 137438953472 2 1 67108864 21801270 hp763914 hp749778 hp763914 hp763914 hp749779

noncomputable def hp763916 := @BSN.binarySplit_of_base (BSN.sinEvenP 50944962150) (BSN.sinEvenQ 137438953472) 0 1 hp763914 hp749778 hp763914 rfl rfl rfl

noncomputable def hp763917 := hp763915 hp763914 24309727 rfl rfl rfl rfl rfl rfl rfl rfl (hp763916 rfl)

noncomputable def hp763918 := @BSN.binarySplit_of_base (BSN.sinOddP 50944962150) (BSN.sinOddQ 137438953472) 0 1 hp763914 hp749779 hp763914 rfl rfl rfl

noncomputable def hp763919 := @BSN.sin_arg_round Bool.false 24309727 67108864 hp763911 hp617687 50944962150 137438953472 21801270 21780000 (hp763917 (hp763918 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp763920 := hp763912 24309727 67108864 0 1000000000000000 21780000 10890000 hp763913 BSN.pi_near_15 hp763919 rfl rfl

noncomputable def hp763921 := @hp763902 67108864 166863679 45675970560000 92628646 92630515 33554432 (@hp763903 24309727 67108864 2669818864 730815528960000 24309727 67108864 166863679 45675970560000 (hp763910 (hp763920 rfl rfl) rfl rfl) rfl)

noncomputable def hp763922 := @hp763901 Bool.false 185259161 67108864 1869 67108864 185259161 67108864 1869 67108864 (hp763921 rfl rfl rfl rfl rfl rfl) rfl

noncomputable def hp763923 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763895 (Enclosure.sfrac Bool.false 1 16)))) Bool.false

noncomputable def hp763924 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763895 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 45754553)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp763925 := nat_lit 216069767878010654506953387725

noncomputable def hp763926 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763895 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp763925

noncomputable def hp763927 := nat_lit 45041322542462135219678593302078309

noncomputable def hp763928 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp763895 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp763929 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp763930 := @hp763929 (Enclosure.sfrac Bool.false 1 16) 173976753332431 1125899906842624 1669057907 1125899906842624 1 16 0

noncomputable def hp763931 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)) 736870080913201

noncomputable def hp763932 := @hp763931 1125899906842624 1031523699 1125899906842624 27145351 33554432 19 33554432 5837691139273829384192 173976753332431 1125899906842624 1669057907

noncomputable def hp763933 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)) 27145351 33554432 19

noncomputable def hp763934 := @hp763933 33554432 27145351 33554432 19 33554432 736870080913201 1125899906842624 1031523699 1125899906842624 (@hp763908 1 27145351 27145351 33554432 19 33554432 (hp763890 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763935 := hp763934 (@hp763908 1 27145351 27145351 33554432 19 33554432 (hp763890 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763936 := @hp763932 1125899906842624 (hp763935 rfl) (@hp763908 1 27145351 27145351 33554432 19 33554432 (hp763890 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp763937 := @hp763928 500000000000000 244345497510095 1125899906842624 1669057907 1125899906842624 hp763925 hp682141 hp763927 hp682143 hd4948 (@hp763930 1 3909527960161520 244345497510095 1125899906842624 1669057907 1125899906842624 (hp763936 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp763938 := @hp763924 45754553 33554432 313 33554432 Bool.false 6902981 33554432 1 10890000 (@hp763926 hp682141 hp763927 hp682143 45754553 33554432 313 33554432 (hp763937 rfl) rfl) (Enclosure.sfrac_true_div 45754553 33554432)

noncomputable def hp763939 := nat_lit 140849466702599156736038759907389031565350277565486319349992591006418519922413237990576410766866721

noncomputable def hp763940 := nat_lit 84180558410801162849173016756209281432324943013660187546723150217894038524141009961313892641

noncomputable def hp763941 := nat_lit 853316436328882164252219796880280033867175015844504218924671666840530679036359348752936701747788065

noncomputable def hp763942 := BSN.cos_dyadic_bound_f 45754553 33554432 4 3 33554432 10890000 hp763939 hp681868 hp763940 hp763941 hp681871

noncomputable def hp763943 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 45754553) (BSN.cosEvenQ 33554432) 0 3 hp763939 hp681868 hp763940 rfl rfl rfl

noncomputable def hp763944 := hp763942 hp763940 6902981 rfl rfl rfl rfl rfl rfl rfl rfl (hp763943 rfl)

noncomputable def hp763945 := @BSN.binarySplit_of_base3 (BSN.cosOddP 45754553) (BSN.cosOddQ 33554432) 0 3 hp763941 hp681871 hp763940 rfl rfl rfl

noncomputable def hp763946 := hp763938 (BSN.cos_neg_of_bound 45754553 33554432 Bool.false 6902981 33554432 1 10890000 (hp763944 (hp763945 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp763947 := hp763900 hp763922 (@hp763923 6902981 33554432 3442124432 365407764480000 6902981 33554432 215132777 22837985280000 (hp763946 rfl) rfl)

noncomputable def hp763948 := @hp763875 33554432 1278840468458941 2251799813685248 9727384002196187 306526249637904384000 24388766573980463811 147573952589676412928 23788923330691329616409 hp754729 (hp763893 rfl) (@hp763896 Bool.false 1278840468458941 2251799813685248 9727384002196187 306526249637904384000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp763697 (Enclosure.sfrac Bool.false 11 1)) (hp763897 rfl (hp763700 rfl rfl))) (hp763947 rfl))

noncomputable def hp763949 := @hp763694 hp763692 hp754729 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 876205 1000))) (@hp763699 hp763692 hp754729 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 876205 1000) 11 (hp763700 rfl rfl)) (@hp763703 hp763692 hp754729 hp763874 (hp763948 rfl) rfl rfl))

theorem hd5064 : hp763693 hp754729 := hp763949

noncomputable def hp790762 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) Bool.false 556919581 10737418240 1213 10737418240

noncomputable def hp792897 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) 860908 1000 862185 1000

noncomputable def hp792898 := hp792897 (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl rfl rfl

noncomputable def hp792899 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898))

noncomputable def hp792900 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 860908 1000) 860908 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl rfl

noncomputable def hp792901 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898))

noncomputable def hp792902 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898)) 32991745972947692065011

noncomputable def hp792903 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 860908 1000))

noncomputable def hp792904 := @hp792902 37778931862957161709568 845217165000330524886353 hp750331 (@hp792903 Bool.true 32991745972947692065011 37778931862957161709568 845217165000330524886353 hp750331 (hd4340 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898) hd5052)

noncomputable def hp792905 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898)) 25090042554906256788119

noncomputable def hp792906 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 862185 1000))

noncomputable def hp792907 := @hp792905 4722366482869645213696 5149422059257954218647 hp760910 (@hp792906 Bool.false 25090042554906256788119 4722366482869645213696 5149422059257954218647 hp760910 (hd4359 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898) hd5053)

noncomputable def hp792908 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898) hp792900 (hp792901 (hp792904 rfl rfl rfl) (hp792907 rfl rfl rfl))

noncomputable def hp792909 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792910 := hp792909 (Enclosure.sfrac Bool.false 860908 1000) 749551 1000 860908 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792911 := hp792910 (@Eq.refl Real (Enclosure.sfrac Bool.false 860908 1000)) rfl rfl rfl rfl

noncomputable def hp792912 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792913 := @hp792912 Bool.true Bool.false 32991745972947692065011 37778931862957161709568 845217165000330524886353 hp750331 556919581 10737418240 1213 10737418240 (@hp792903 Bool.true 32991745972947692065011 37778931862957161709568 845217165000330524886353 hp750331 (hd4340 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898) hd5052)

noncomputable def hp792914 := hp792913 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792915 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792916 := hp792915 (Enclosure.sfrac Bool.false 862185 1000) 749551 1000 862185 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792917 := hp792916 (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl rfl rfl rfl

noncomputable def hp792918 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792919 := @hp792918 Bool.false Bool.false 25090042554906256788119 4722366482869645213696 5149422059257954218647 hp760910 556919581 10737418240 1213 10737418240 (@hp792906 Bool.false 25090042554906256788119 4722366482869645213696 5149422059257954218647 hp760910 (hd4359 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898) hd5053)

noncomputable def hp792920 := hp792919 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792922 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) 862185 1000 863462 1000

noncomputable def hp792923 := hp792922 (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl rfl rfl

noncomputable def hp792924 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923))

noncomputable def hp792925 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 862185 1000) 862185 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl rfl

noncomputable def hp792926 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923))

noncomputable def hp792927 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923)) 25090042554906256788119

noncomputable def hp792928 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 862185 1000))

noncomputable def hp792929 := @hp792927 4722366482869645213696 5149422059257954218647 hp760910 (@hp792928 Bool.false 25090042554906256788119 4722366482869645213696 5149422059257954218647 hp760910 (hd4340 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923) hd5053)

noncomputable def hp792930 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923)) 6362793886179603060855

noncomputable def hp792931 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 863462 1000))

noncomputable def hp792932 := @hp792930 4722366482869645213696 114088751760915325805619 hp739341 (@hp792931 Bool.true 6362793886179603060855 4722366482869645213696 114088751760915325805619 hp739341 (hd4359 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923) hd5054)

noncomputable def hp792933 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923) hp792925 (hp792926 (hp792929 rfl rfl rfl) (hp792932 rfl rfl rfl))

noncomputable def hp792934 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792935 := hp792934 (Enclosure.sfrac Bool.false 862185 1000) 749551 1000 862185 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792936 := hp792935 (@Eq.refl Real (Enclosure.sfrac Bool.false 862185 1000)) rfl rfl rfl rfl

noncomputable def hp792937 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792938 := @hp792937 Bool.false Bool.false 25090042554906256788119 4722366482869645213696 5149422059257954218647 hp760910 556919581 10737418240 1213 10737418240 (@hp792928 Bool.false 25090042554906256788119 4722366482869645213696 5149422059257954218647 hp760910 (hd4340 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923) hd5053)

noncomputable def hp792939 := hp792938 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792940 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792941 := hp792940 (Enclosure.sfrac Bool.false 863462 1000) 749551 1000 863462 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792942 := hp792941 (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl rfl rfl rfl

noncomputable def hp792943 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792944 := @hp792943 Bool.true Bool.false 6362793886179603060855 4722366482869645213696 114088751760915325805619 hp739341 556919581 10737418240 1213 10737418240 (@hp792931 Bool.true 6362793886179603060855 4722366482869645213696 114088751760915325805619 hp739341 (hd4359 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923) hd5054)

noncomputable def hp792945 := hp792944 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792947 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) 863462 1000 864738 1000

noncomputable def hp792948 := hp792947 (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl rfl rfl

noncomputable def hp792949 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948))

noncomputable def hp792950 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 863462 1000) 863462 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl rfl

noncomputable def hp792951 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948))

noncomputable def hp792952 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948)) 6362793886179603060855

noncomputable def hp792953 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 863462 1000))

noncomputable def hp792954 := @hp792952 4722366482869645213696 114088751760915325805619 hp739341 (@hp792953 Bool.true 6362793886179603060855 4722366482869645213696 114088751760915325805619 hp739341 (hd4340 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948) hd5054)

noncomputable def hp792955 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948)) 22580982327743074310781

noncomputable def hp792956 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 864738 1000))

noncomputable def hp792957 := @hp792955 18889465931478580854784 hp761419 hp742094 (@hp792956 Bool.false 22580982327743074310781 18889465931478580854784 hp761419 hp742094 (hd4359 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948) hd5055)

noncomputable def hp792958 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948) hp792950 (hp792951 (hp792954 rfl rfl rfl) (hp792957 rfl rfl rfl))

noncomputable def hp792959 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792960 := hp792959 (Enclosure.sfrac Bool.false 863462 1000) 749551 1000 863462 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792961 := hp792960 (@Eq.refl Real (Enclosure.sfrac Bool.false 863462 1000)) rfl rfl rfl rfl

noncomputable def hp792962 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792963 := @hp792962 Bool.true Bool.false 6362793886179603060855 4722366482869645213696 114088751760915325805619 hp739341 556919581 10737418240 1213 10737418240 (@hp792953 Bool.true 6362793886179603060855 4722366482869645213696 114088751760915325805619 hp739341 (hd4340 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948) hd5054)

noncomputable def hp792964 := hp792963 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792965 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792966 := hp792965 (Enclosure.sfrac Bool.false 864738 1000) 749551 1000 864738 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792967 := hp792966 (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl rfl rfl rfl

noncomputable def hp792968 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792969 := @hp792968 Bool.false Bool.false 22580982327743074310781 18889465931478580854784 hp761419 hp742094 556919581 10737418240 1213 10737418240 (@hp792956 Bool.false 22580982327743074310781 18889465931478580854784 hp761419 hp742094 (hd4359 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948) hd5055)

noncomputable def hp792970 := hp792969 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792972 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) 864738 1000 866013 1000

noncomputable def hp792973 := hp792972 (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl rfl rfl

noncomputable def hp792974 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973))

noncomputable def hp792975 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 864738 1000) 864738 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl rfl

noncomputable def hp792976 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973))

noncomputable def hp792977 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973)) 22580982327743074310781

noncomputable def hp792978 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 864738 1000))

noncomputable def hp792979 := @hp792977 18889465931478580854784 hp761419 hp742094 (@hp792978 Bool.false 22580982327743074310781 18889465931478580854784 hp761419 hp742094 (hd4340 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973) hd5055)

noncomputable def hp792980 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973)) 44234242815971035122205

noncomputable def hp792981 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 866013 1000))

noncomputable def hp792982 := @hp792980 75557863725914323419136 hp761674 hp738860 (@hp792981 Bool.true 44234242815971035122205 75557863725914323419136 hp761674 hp738860 (hd4359 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973) hd5056)

noncomputable def hp792983 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973) hp792975 (hp792976 (hp792979 rfl rfl rfl) (hp792982 rfl rfl rfl))

noncomputable def hp792984 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792985 := hp792984 (Enclosure.sfrac Bool.false 864738 1000) 749551 1000 864738 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792986 := hp792985 (@Eq.refl Real (Enclosure.sfrac Bool.false 864738 1000)) rfl rfl rfl rfl

noncomputable def hp792987 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792988 := @hp792987 Bool.false Bool.false 22580982327743074310781 18889465931478580854784 hp761419 hp742094 556919581 10737418240 1213 10737418240 (@hp792978 Bool.false 22580982327743074310781 18889465931478580854784 hp761419 hp742094 (hd4340 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973) hd5055)

noncomputable def hp792989 := hp792988 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792990 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792991 := hp792990 (Enclosure.sfrac Bool.false 866013 1000) 749551 1000 866013 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792992 := hp792991 (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl rfl rfl rfl

noncomputable def hp792993 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792994 := @hp792993 Bool.true Bool.false 44234242815971035122205 75557863725914323419136 hp761674 hp738860 556919581 10737418240 1213 10737418240 (@hp792981 Bool.true 44234242815971035122205 75557863725914323419136 hp761674 hp738860 (hd4359 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973) hd5056)

noncomputable def hp792995 := hp792994 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792997 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) 866013 1000 867289 1000

noncomputable def hp792998 := hp792997 (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl rfl rfl

noncomputable def hp792999 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998))

noncomputable def hp793000 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 866013 1000) 866013 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl rfl

noncomputable def hp793001 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998))

noncomputable def hp793002 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998)) 44234242815971035122205

noncomputable def hp793003 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 866013 1000))

noncomputable def hp793004 := @hp793002 75557863725914323419136 hp761674 hp738860 (@hp793003 Bool.true 44234242815971035122205 75557863725914323419136 hp761674 hp738860 (hd4340 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998) hd5056)

noncomputable def hp793005 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998)) 11106355472190084315145

noncomputable def hp793006 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 867289 1000))

noncomputable def hp793007 := @hp793005 9444732965739290427392 hp761933 hp752398 (@hp793006 Bool.false 11106355472190084315145 9444732965739290427392 hp761933 hp752398 (hd4359 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998) hd5057)

noncomputable def hp793008 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998) hp793000 (hp793001 (hp793004 rfl rfl rfl) (hp793007 rfl rfl rfl))

noncomputable def hp793009 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793010 := hp793009 (Enclosure.sfrac Bool.false 866013 1000) 749551 1000 866013 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793011 := hp793010 (@Eq.refl Real (Enclosure.sfrac Bool.false 866013 1000)) rfl rfl rfl rfl

noncomputable def hp793012 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793013 := @hp793012 Bool.true Bool.false 44234242815971035122205 75557863725914323419136 hp761674 hp738860 556919581 10737418240 1213 10737418240 (@hp793003 Bool.true 44234242815971035122205 75557863725914323419136 hp761674 hp738860 (hd4340 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998) hd5056)

noncomputable def hp793014 := hp793013 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793015 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793016 := hp793015 (Enclosure.sfrac Bool.false 867289 1000) 749551 1000 867289 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793017 := hp793016 (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl rfl rfl rfl

noncomputable def hp793018 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793019 := @hp793018 Bool.false Bool.false 11106355472190084315145 9444732965739290427392 hp761933 hp752398 556919581 10737418240 1213 10737418240 (@hp793006 Bool.false 11106355472190084315145 9444732965739290427392 hp761933 hp752398 (hd4359 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998) hd5057)

noncomputable def hp793020 := hp793019 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793022 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) 867289 1000 868564 1000

noncomputable def hp793023 := hp793022 (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl rfl rfl

noncomputable def hp793024 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023))

noncomputable def hp793025 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 867289 1000) 867289 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl rfl

noncomputable def hp793026 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023))

noncomputable def hp793027 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023)) 11106355472190084315145

noncomputable def hp793028 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 867289 1000))

noncomputable def hp793029 := @hp793027 9444732965739290427392 hp761933 hp752398 (@hp793028 Bool.false 11106355472190084315145 9444732965739290427392 hp761933 hp752398 (hd4340 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023) hd5057)

noncomputable def hp793030 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023)) 10885507039153897382031

noncomputable def hp793031 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 868564 1000))

noncomputable def hp793032 := @hp793030 18889465931478580854784 609813783743004399890237 hp762191 (@hp793031 Bool.true 10885507039153897382031 18889465931478580854784 609813783743004399890237 hp762191 (hd4359 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023) hd5058)

noncomputable def hp793033 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023) hp793025 (hp793026 (hp793029 rfl rfl rfl) (hp793032 rfl rfl rfl))

noncomputable def hp793034 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793035 := hp793034 (Enclosure.sfrac Bool.false 867289 1000) 749551 1000 867289 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793036 := hp793035 (@Eq.refl Real (Enclosure.sfrac Bool.false 867289 1000)) rfl rfl rfl rfl

noncomputable def hp793037 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793038 := @hp793037 Bool.false Bool.false 11106355472190084315145 9444732965739290427392 hp761933 hp752398 556919581 10737418240 1213 10737418240 (@hp793028 Bool.false 11106355472190084315145 9444732965739290427392 hp761933 hp752398 (hd4340 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023) hd5057)

noncomputable def hp793039 := hp793038 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793040 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793041 := hp793040 (Enclosure.sfrac Bool.false 868564 1000) 749551 1000 868564 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793042 := hp793041 (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl rfl rfl rfl

noncomputable def hp793043 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793044 := @hp793043 Bool.true Bool.false 10885507039153897382031 18889465931478580854784 609813783743004399890237 hp762191 556919581 10737418240 1213 10737418240 (@hp793031 Bool.true 10885507039153897382031 18889465931478580854784 609813783743004399890237 hp762191 (hd4359 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023) hd5058)

noncomputable def hp793045 := hp793044 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793047 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) 868564 1000 869838 1000

noncomputable def hp793048 := hp793047 (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl rfl rfl

noncomputable def hp793049 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048))

noncomputable def hp793050 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 868564 1000) 868564 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl rfl

noncomputable def hp793051 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048))

noncomputable def hp793052 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048)) 10885507039153897382031

noncomputable def hp793053 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 868564 1000))

noncomputable def hp793054 := @hp793052 18889465931478580854784 609813783743004399890237 hp762191 (@hp793053 Bool.true 10885507039153897382031 18889465931478580854784 609813783743004399890237 hp762191 (hd4340 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048) hd5058)

noncomputable def hp793055 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048)) 69069943403023471068459

noncomputable def hp793056 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 869838 1000))

noncomputable def hp793057 := @hp793055 9444732965739290427392 292220567895345409944501 hp762433 (@hp793056 Bool.false 69069943403023471068459 9444732965739290427392 292220567895345409944501 hp762433 (hd4359 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048) hd5059)

noncomputable def hp793058 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048) hp793050 (hp793051 (hp793054 rfl rfl rfl) (hp793057 rfl rfl rfl))

noncomputable def hp793059 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793060 := hp793059 (Enclosure.sfrac Bool.false 868564 1000) 749551 1000 868564 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793061 := hp793060 (@Eq.refl Real (Enclosure.sfrac Bool.false 868564 1000)) rfl rfl rfl rfl

noncomputable def hp793062 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793063 := @hp793062 Bool.true Bool.false 10885507039153897382031 18889465931478580854784 609813783743004399890237 hp762191 556919581 10737418240 1213 10737418240 (@hp793053 Bool.true 10885507039153897382031 18889465931478580854784 609813783743004399890237 hp762191 (hd4340 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048) hd5058)

noncomputable def hp793064 := hp793063 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793065 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793066 := hp793065 (Enclosure.sfrac Bool.false 869838 1000) 749551 1000 869838 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793067 := hp793066 (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl rfl rfl rfl

noncomputable def hp793068 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793069 := @hp793068 Bool.false Bool.false 69069943403023471068459 9444732965739290427392 292220567895345409944501 hp762433 556919581 10737418240 1213 10737418240 (@hp793056 Bool.false 69069943403023471068459 9444732965739290427392 292220567895345409944501 hp762433 (hd4359 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048) hd5059)

noncomputable def hp793070 := hp793069 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793072 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) 869838 1000 871112 1000

noncomputable def hp793073 := hp793072 (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl rfl rfl

noncomputable def hp793074 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073))

noncomputable def hp793075 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 869838 1000) 869838 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl rfl

noncomputable def hp793076 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073))

noncomputable def hp793077 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073)) 69069943403023471068459

noncomputable def hp793078 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 869838 1000))

noncomputable def hp793079 := @hp793077 9444732965739290427392 292220567895345409944501 hp762433 (@hp793078 Bool.false 69069943403023471068459 9444732965739290427392 292220567895345409944501 hp762433 (hd4340 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073) hd5059)

noncomputable def hp793080 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073)) 65514246868862362231561

noncomputable def hp793081 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 871112 1000))

noncomputable def hp793082 := @hp793080 37778931862957161709568 461956554045444868163437 hp751106 (@hp793081 Bool.true 65514246868862362231561 37778931862957161709568 461956554045444868163437 hp751106 (hd4359 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073) hd5060)

noncomputable def hp793083 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073) hp793075 (hp793076 (hp793079 rfl rfl rfl) (hp793082 rfl rfl rfl))

noncomputable def hp793084 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793085 := hp793084 (Enclosure.sfrac Bool.false 869838 1000) 749551 1000 869838 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793086 := hp793085 (@Eq.refl Real (Enclosure.sfrac Bool.false 869838 1000)) rfl rfl rfl rfl

noncomputable def hp793087 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793088 := @hp793087 Bool.false Bool.false 69069943403023471068459 9444732965739290427392 292220567895345409944501 hp762433 556919581 10737418240 1213 10737418240 (@hp793078 Bool.false 69069943403023471068459 9444732965739290427392 292220567895345409944501 hp762433 (hd4340 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073) hd5059)

noncomputable def hp793089 := hp793088 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793090 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793091 := hp793090 (Enclosure.sfrac Bool.false 871112 1000) 749551 1000 871112 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793092 := hp793091 (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl rfl rfl rfl

noncomputable def hp793093 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793094 := @hp793093 Bool.true Bool.false 65514246868862362231561 37778931862957161709568 461956554045444868163437 hp751106 556919581 10737418240 1213 10737418240 (@hp793081 Bool.true 65514246868862362231561 37778931862957161709568 461956554045444868163437 hp751106 (hd4359 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073) hd5060)

noncomputable def hp793095 := hp793094 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793097 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) 871112 1000 872386 1000

noncomputable def hp793098 := hp793097 (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl rfl rfl

noncomputable def hp793099 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098))

noncomputable def hp793100 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 871112 1000) 871112 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl rfl

noncomputable def hp793101 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098))

noncomputable def hp793102 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098)) 65514246868862362231561

noncomputable def hp793103 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 871112 1000))

noncomputable def hp793104 := @hp793102 37778931862957161709568 461956554045444868163437 hp751106 (@hp793103 Bool.true 65514246868862362231561 37778931862957161709568 461956554045444868163437 hp751106 (hd4340 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098) hd5060)

noncomputable def hp793105 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098)) 41282108026741643214671

noncomputable def hp793106 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 872386 1000))

noncomputable def hp793107 := @hp793105 75557863725914323419136 hp762941 hp741590 (@hp793106 Bool.false 41282108026741643214671 75557863725914323419136 hp762941 hp741590 (hd4359 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098) hd5061)

noncomputable def hp793108 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098) hp793100 (hp793101 (hp793104 rfl rfl rfl) (hp793107 rfl rfl rfl))

noncomputable def hp793109 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793110 := hp793109 (Enclosure.sfrac Bool.false 871112 1000) 749551 1000 871112 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793111 := hp793110 (@Eq.refl Real (Enclosure.sfrac Bool.false 871112 1000)) rfl rfl rfl rfl

noncomputable def hp793112 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793113 := @hp793112 Bool.true Bool.false 65514246868862362231561 37778931862957161709568 461956554045444868163437 hp751106 556919581 10737418240 1213 10737418240 (@hp793103 Bool.true 65514246868862362231561 37778931862957161709568 461956554045444868163437 hp751106 (hd4340 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098) hd5060)

noncomputable def hp793114 := hp793113 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793115 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793116 := hp793115 (Enclosure.sfrac Bool.false 872386 1000) 749551 1000 872386 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793117 := hp793116 (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl rfl rfl rfl

noncomputable def hp793118 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793119 := @hp793118 Bool.false Bool.false 41282108026741643214671 75557863725914323419136 hp762941 hp741590 556919581 10737418240 1213 10737418240 (@hp793106 Bool.false 41282108026741643214671 75557863725914323419136 hp762941 hp741590 (hd4359 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098) hd5061)

noncomputable def hp793120 := hp793119 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793122 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) 872386 1000 873660 1000

noncomputable def hp793123 := hp793122 (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl rfl rfl

noncomputable def hp793124 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123))

noncomputable def hp793125 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 872386 1000) 872386 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl rfl

noncomputable def hp793126 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123))

noncomputable def hp793127 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123)) 41282108026741643214671

noncomputable def hp793128 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 872386 1000))

noncomputable def hp793129 := @hp793127 75557863725914323419136 hp762941 hp741590 (@hp793128 Bool.false 41282108026741643214671 75557863725914323419136 hp762941 hp741590 (hd4340 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123) hd5061)

noncomputable def hp793130 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123)) 5330217008264793987747

noncomputable def hp793131 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 873660 1000))

noncomputable def hp793132 := @hp793130 9444732965739290427392 hp763193 hp740342 (@hp793131 Bool.true 5330217008264793987747 9444732965739290427392 hp763193 hp740342 (hd4359 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123) hd5062)

noncomputable def hp793133 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123) hp793125 (hp793126 (hp793129 rfl rfl rfl) (hp793132 rfl rfl rfl))

noncomputable def hp793134 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793135 := hp793134 (Enclosure.sfrac Bool.false 872386 1000) 749551 1000 872386 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793136 := hp793135 (@Eq.refl Real (Enclosure.sfrac Bool.false 872386 1000)) rfl rfl rfl rfl

noncomputable def hp793137 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793138 := @hp793137 Bool.false Bool.false 41282108026741643214671 75557863725914323419136 hp762941 hp741590 556919581 10737418240 1213 10737418240 (@hp793128 Bool.false 41282108026741643214671 75557863725914323419136 hp762941 hp741590 (hd4340 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123) hd5061)

noncomputable def hp793139 := hp793138 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793140 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793141 := hp793140 (Enclosure.sfrac Bool.false 873660 1000) 749551 1000 873660 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793142 := hp793141 (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl rfl rfl rfl

noncomputable def hp793143 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793144 := @hp793143 Bool.true Bool.false 5330217008264793987747 9444732965739290427392 hp763193 hp740342 556919581 10737418240 1213 10737418240 (@hp793131 Bool.true 5330217008264793987747 9444732965739290427392 hp763193 hp740342 (hd4359 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123) hd5062)

noncomputable def hp793145 := hp793144 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793147 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) 873660 1000 874933 1000

noncomputable def hp793148 := hp793147 (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl rfl rfl

noncomputable def hp793149 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148))

noncomputable def hp793150 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 873660 1000) 873660 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl rfl

noncomputable def hp793151 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148))

noncomputable def hp793152 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148)) 5330217008264793987747

noncomputable def hp793153 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 873660 1000))

noncomputable def hp793154 := @hp793152 9444732965739290427392 hp763193 hp740342 (@hp793153 Bool.true 5330217008264793987747 9444732965739290427392 hp763193 hp740342 (hd4340 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148) hd5062)

noncomputable def hp793155 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148)) 134090306691679199591637

noncomputable def hp793156 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 874933 1000))

noncomputable def hp793157 := @hp793155 37778931862957161709568 54961730151268642414957 hp763445 (@hp793156 Bool.false 134090306691679199591637 37778931862957161709568 54961730151268642414957 hp763445 (hd4359 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148) hd5063)

noncomputable def hp793158 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148) hp793150 (hp793151 (hp793154 rfl rfl rfl) (hp793157 rfl rfl rfl))

noncomputable def hp793159 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793160 := hp793159 (Enclosure.sfrac Bool.false 873660 1000) 749551 1000 873660 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793161 := hp793160 (@Eq.refl Real (Enclosure.sfrac Bool.false 873660 1000)) rfl rfl rfl rfl

noncomputable def hp793162 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793163 := @hp793162 Bool.true Bool.false 5330217008264793987747 9444732965739290427392 hp763193 hp740342 556919581 10737418240 1213 10737418240 (@hp793153 Bool.true 5330217008264793987747 9444732965739290427392 hp763193 hp740342 (hd4340 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148) hd5062)

noncomputable def hp793164 := hp793163 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793165 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793166 := hp793165 (Enclosure.sfrac Bool.false 874933 1000) 749551 1000 874933 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793167 := hp793166 (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl rfl rfl rfl

noncomputable def hp793168 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793169 := @hp793168 Bool.false Bool.false 134090306691679199591637 37778931862957161709568 54961730151268642414957 hp763445 556919581 10737418240 1213 10737418240 (@hp793156 Bool.false 134090306691679199591637 37778931862957161709568 54961730151268642414957 hp763445 (hd4359 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148) hd5063)

noncomputable def hp793170 := hp793169 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793172 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) 874933 1000 876205 1000

noncomputable def hp793173 := hp793172 (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl rfl rfl

noncomputable def hp793174 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173))

noncomputable def hp793175 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 874933 1000) 874933 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl rfl

noncomputable def hp793176 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173))

noncomputable def hp793177 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173)) 134090306691679199591637

noncomputable def hp793178 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 874933 1000))

noncomputable def hp793179 := @hp793177 37778931862957161709568 54961730151268642414957 hp763445 (@hp793178 Bool.false 134090306691679199591637 37778931862957161709568 54961730151268642414957 hp763445 (hd4340 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173) hd5063)

noncomputable def hp793180 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173)) 55945259405031329085

noncomputable def hp793181 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 876205 1000))

noncomputable def hp793182 := @hp793180 147573952589676412928 hp763692 hp754729 (@hp793181 Bool.true 55945259405031329085 147573952589676412928 hp763692 hp754729 (hd4359 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173) hd5064)

noncomputable def hp793183 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173) hp793175 (hp793176 (hp793179 rfl rfl rfl) (hp793182 rfl rfl rfl))

noncomputable def hp793184 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793185 := hp793184 (Enclosure.sfrac Bool.false 874933 1000) 749551 1000 874933 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793186 := hp793185 (@Eq.refl Real (Enclosure.sfrac Bool.false 874933 1000)) rfl rfl rfl rfl

noncomputable def hp793187 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793188 := @hp793187 Bool.false Bool.false 134090306691679199591637 37778931862957161709568 54961730151268642414957 hp763445 556919581 10737418240 1213 10737418240 (@hp793178 Bool.false 134090306691679199591637 37778931862957161709568 54961730151268642414957 hp763445 (hd4340 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173) hd5063)

noncomputable def hp793189 := hp793188 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp793190 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp793191 := hp793190 (Enclosure.sfrac Bool.false 876205 1000) 749551 1000 876205 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793192 := hp793191 (@Eq.refl Real (Enclosure.sfrac Bool.false 876205 1000)) rfl rfl rfl rfl

noncomputable def hp793193 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp793194 := @hp793193 Bool.true Bool.false 55945259405031329085 147573952589676412928 hp763692 hp754729 556919581 10737418240 1213 10737418240 (@hp793181 Bool.true 55945259405031329085 147573952589676412928 hp763692 hp754729 (hd4359 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173) hd5064)

noncomputable def hp793195 := hp793194 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl
open Zeta.Certificates
noncomputable def certificatePairs : List (Σ' I : ZIntervalRS, I.Certified) := [(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 860908 1000) (Enclosure.sfrac Bool.false 862185 1000) hp792898) (hp792899 (hp792908 (hp792911 (hp792914 rfl rfl)) (hp792917 (hp792920 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 862185 1000) (Enclosure.sfrac Bool.false 863462 1000) hp792923) (hp792924 (hp792933 (hp792936 (hp792939 rfl rfl)) (hp792942 (hp792945 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 863462 1000) (Enclosure.sfrac Bool.false 864738 1000) hp792948) (hp792949 (hp792958 (hp792961 (hp792964 rfl rfl)) (hp792967 (hp792970 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 864738 1000) (Enclosure.sfrac Bool.false 866013 1000) hp792973) (hp792974 (hp792983 (hp792986 (hp792989 rfl rfl)) (hp792992 (hp792995 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 866013 1000) (Enclosure.sfrac Bool.false 867289 1000) hp792998) (hp792999 (hp793008 (hp793011 (hp793014 rfl rfl)) (hp793017 (hp793020 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 867289 1000) (Enclosure.sfrac Bool.false 868564 1000) hp793023) (hp793024 (hp793033 (hp793036 (hp793039 rfl rfl)) (hp793042 (hp793045 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 868564 1000) (Enclosure.sfrac Bool.false 869838 1000) hp793048) (hp793049 (hp793058 (hp793061 (hp793064 rfl rfl)) (hp793067 (hp793070 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 869838 1000) (Enclosure.sfrac Bool.false 871112 1000) hp793073) (hp793074 (hp793083 (hp793086 (hp793089 rfl rfl)) (hp793092 (hp793095 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 871112 1000) (Enclosure.sfrac Bool.false 872386 1000) hp793098) (hp793099 (hp793108 (hp793111 (hp793114 rfl rfl)) (hp793117 (hp793120 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 872386 1000) (Enclosure.sfrac Bool.false 873660 1000) hp793123) (hp793124 (hp793133 (hp793136 (hp793139 rfl rfl)) (hp793142 (hp793145 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 873660 1000) (Enclosure.sfrac Bool.false 874933 1000) hp793148) (hp793149 (hp793158 (hp793161 (hp793164 rfl rfl)) (hp793167 (hp793170 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 874933 1000) (Enclosure.sfrac Bool.false 876205 1000) hp793173) (hp793174 (hp793183 (hp793186 (hp793189 rfl rfl)) (hp793192 (hp793195 rfl rfl)))))]

theorem solution : Zeta.Certificates.BatchSpec 12 860908 1000 876205 1000 :=
  ⟨CertifiedZeroIntervals.ofCertifiedRS certificatePairs (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.singleton _)))))))))))), rfl, rfl, rfl⟩
#print axioms solution
