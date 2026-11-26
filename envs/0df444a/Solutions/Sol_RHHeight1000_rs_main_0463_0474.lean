-- Prove2me | solution 1 for RHHeight1000.rs_main_0463_0474
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:37:43.941269+00:00
-- url     : https://prove2.me/submissions/6afd9a6b-2d90-437d-8799-1a83ff919c45

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

noncomputable def hp633059 := nat_lit 58158844227896986633558482781719779619497718984807332131428259197799420928759449934993817600

noncomputable def hp633062 := nat_lit 5292454824738625783653821933136499945374292427617467223959971586999747304517109944084437401600

noncomputable def hp633087 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600

noncomputable def hp633090 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600

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

noncomputable def hp741590 := nat_lit 17142190332816812125716480000

noncomputable def hp742826 := nat_lit 3868562622766813359059763200000000000000

noncomputable def hp743344 := nat_lit 5142657099845043637714944000

noncomputable def hp743892 := nat_lit 1622016000000000000000000

noncomputable def hp745658 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600

noncomputable def hp745661 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600

noncomputable def hp746621 := nat_lit 5133330660362904937396483134791632965849700352038159351603073932373040875403608499582161387520

noncomputable def hp746624 := nat_lit 230999879716330722182841741065623483463236515841717170822138326956786839393162382481197262438400

noncomputable def hp747268 := nat_lit 773712524553362671811952640000000000000

noncomputable def hp754162 := nat_lit 11529215046068469760000000000000

noncomputable def hp754467 := nat_lit 3872033672070192118840997

noncomputable def hp754468 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 830146 1000)) Bool.true 72094639779617503274629 37778931862957161709568 hp754467

noncomputable def hp754469 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 830146 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 830146 1000)) Bool.true 72094639779617503274629 37778931862957161709568

noncomputable def hp754470 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 830146 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754471 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp754470 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754472 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 830146 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754473 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp754471 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp754474 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 830146 1000)) hp754473 Bool.true 72094639779617503274629 37778931862957161709568

noncomputable def hp754475 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 830146 1000) 830146 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl

noncomputable def hp754476 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp754471 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp754477 := nat_lit 19352757504397363997106528845824

noncomputable def hp754478 := @hp754476 542567059 268435456 100723 134217728 4264885368379556665723 37778931862957161709568 12753241785361710136997 hp743344 hp754477 72094639779617503274629 37778931862957161709568

noncomputable def hp754479 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) 11)

noncomputable def hp754480 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) 11) hp754479

noncomputable def hp754481 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) 11)

noncomputable def hp754482 := @hp754481 542567059 536870912 201446 536870912 542567059 536870912 201446 536870912 582576943572975616 542567059 268435456

noncomputable def hp754483 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp754484 := hp754483 BSN.quadSignNeg 9 10 11 830146 1000 190 241 536870912 268435456 9007199254740992

noncomputable def hp754485 := hp754484 Bool.false 865240766132 3783 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp754486 := hp754485 Bool.true 448963381 172936 Bool.true 748388486 Bool.true 217290635 28296951008113761 1 Bool.false 94432525

noncomputable def hp754487 := hp754486 Bool.true Bool.false 211406613 Bool.true Bool.true 542567059 201446 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 94432525 536870912) BSN.abs_quadSignNeg

noncomputable def hp754488 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp754489 := hp754488 BSN.quadSignPos 7 8 9 830146 1000 72 135 536870912 268435456 9007199254740992

noncomputable def hp754490 := hp754489 Bool.false 865240766132 3783 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp754491 := hp754490 Bool.true 518040181 141237 Bool.true 808648462 Bool.true 173490464 28296951008113761 1 Bool.false 34642309

noncomputable def hp754492 := hp754491 Bool.false Bool.false 170486685 Bool.false Bool.true 448963381 172936 BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 34642309 536870912) BSN.abs_quadSignPos

noncomputable def hp754493 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp754494 := hp754493 BSN.quadSignNeg 5 6 7 830146 1000 79 2 536870912 268435456 9007199254740992

noncomputable def hp754495 := hp754494 Bool.false 865240766132 3783 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp754496 := hp754495 Bool.true 378480506 104957 Bool.false 65316320 Bool.true 328239755 28296951008113761 1 Bool.false 65155310

noncomputable def hp754497 := hp754496 Bool.false Bool.false 439615960 Bool.true Bool.true 518040181 141237 BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 65155310 536870912) BSN.abs_quadSignNeg

noncomputable def hp754498 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp754499 := hp754498 BSN.quadSignPos 3 4 5 830146 1000 293 175 536870912 268435456 9007199254740992

noncomputable def hp754500 := hp754499 Bool.false 865240766132 3783 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp754501 := hp754500 Bool.true 385152076 62037 Bool.false 304134726 Bool.false 364394702 28296951008113761 1 Bool.false 288126774

noncomputable def hp754502 := hp754501 Bool.true Bool.false 337053595 Bool.false Bool.true 378480506 104957 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 293 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 288126774 536870912) BSN.abs_quadSignPos

noncomputable def hp754503 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp754504 := hp754503 BSN.quadSignNeg 1 2 3 830146 1000 659 445 536870912 268435456 9007199254740992

noncomputable def hp754505 := hp754504 Bool.false 865240766132 3783 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp754506 := hp754505 Bool.true 536870840 3842 Bool.false 573593097 Bool.false 334772200 28296951008113761 1 Bool.false 470530511

noncomputable def hp754507 := hp754506 Bool.false Bool.false 313495221 Bool.true Bool.true 385152076 62037 BSN.abs_quadSignPos (BSN.cos_quad_nat3 659 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 470530511 536870912) BSN.abs_quadSignNeg

noncomputable def hp754508 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) 1) Bool.true

noncomputable def hp754509 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)))

noncomputable def hp754510 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000))) Bool.true 67108855 67108864

noncomputable def hp754511 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 54077547883) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 54077547883 33554432

noncomputable def hp754512 := nat_lit 668108127554525438291183760161235140582864221143693349571

noncomputable def hp754513 := nat_lit 414552612168331318471018974600893889009116032008192000

noncomputable def hp754514 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) Bool.false hp754512 hp754513 20946577417759608493

noncomputable def hp754515 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 830146 4000) (Real.log (Enclosure.sfrac Bool.false 2756570525264 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1660292))))))

noncomputable def hp754516 := nat_lit 189240477249469595571948875668480000

noncomputable def hp754517 := nat_lit 942583510933062185520200215707731988480

noncomputable def hp754518 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp754515 (Enclosure.sfrac Bool.false 830146 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 830146 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp754516 hp754517)) Bool.false

noncomputable def hp754519 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 830146 1000) 830146 1000 2756570525264 16000000 1660292

noncomputable def hp754520 := hp754519 4000 2000 hp754516 hp754517 (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl rfl rfl rfl

noncomputable def hp754521 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp754515 (Enclosure.sfrac Bool.false 830146 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 830146 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp754516 hp754517) 14516333033768780018471 9007199254740992000

noncomputable def hp754522 := nat_lit 13682854452316680976203443408102095679137059249022839799214080

noncomputable def hp754523 := @hp754521 20946577417759608493 hp740893 hp754516 hp754517 0 1 hp754522 hp754512 hp754513 20946577417759608493 hp740893

noncomputable def hp754524 := @Enclosure.Real.IsNear.subLit_ff_p (hp754515 (Enclosure.sfrac Bool.false 830146 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 830146 2000) (Real.log Real.pi)) 18796071932811253625639 9007199254740992000 1746140061506233 726000000000000000000

noncomputable def hp754525 := nat_lit 487087309670948232852743913472000

noncomputable def hp754526 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 830146 4000) (Real.log (Enclosure.sfrac Bool.false 2756570525264 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1660292))))))

noncomputable def hp754527 := @hp754526 (Enclosure.sfrac Bool.false 830146 2000) 4506943429814872279611 1801439850948198400 1746140061506233 726000000000000000000 830146 2000 0

noncomputable def hp754528 := nat_lit 7518428773124501450255600

noncomputable def hp754529 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 830146 4000) (Real.log (Enclosure.sfrac Bool.false 2756570525264 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1660292))))) 4507650582349468608411

noncomputable def hp754530 := nat_lit 10148734375547081995240715112601878528

noncomputable def hp754531 := @hp754529 1801439850948198400 5188420184246449 2178000000000000000000 883940668245411 2251799813685248 200000001089 8712000000000000000 hp754530 4506943429814872279611 1801439850948198400 1746140061506233

noncomputable def hp754532 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 830146 4000) (Real.log (Enclosure.sfrac Bool.false 2756570525264 16000000)) 830146 4000 0 1 54299491683986535 4503599627370496

noncomputable def hp754533 := nat_lit 116607270486073067364679680

noncomputable def hp754534 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2756570525264) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp754533 hp617687

noncomputable def hp754535 := BSN.log_rat_reduce_isNear 2756570525264 16000000 17 5513141050528 4194304000000 73392162 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp754536 := nat_lit 291092737442807038503081386070168537918230545806028366107602724501959840949658605401241128122506459217920

noncomputable def hp754537 := nat_lit 1811045139288668107867200615804736565723622704404978356006893185445321002107176421973396397218452209664

noncomputable def hp754538 := nat_lit 3753863263248781162912448821767456469370866688774396151268969690726882541549321350562599277690880

noncomputable def hp754539 := BSN.log_dyadic_bound 659418525264 4853722525264 5 4 hp754536 268435456 87120000 hp754537 hp754538 73392162 5513141050528

noncomputable def hp754540 := hp754539 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp754541 := @BSN.binarySplit_of_base4 (BSN.artanhP 659418525264) (BSN.artanhQ 4853722525264) 0 4 hp754537 hp754536 hp754538 rfl rfl rfl

noncomputable def hp754542 := hp754535 rfl rfl rfl rfl (hp754540 (hp754541 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp754543 := @hp754532 12500018513 1089000000000000000 4507650582349468608411 1801439850948198400 5188420184246449 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 830146 4000) (BSN.isNear_log_sfrac 2756570525264 16000000 54299491683986535 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp754534 1000001481040000 87120000000000000000000 54299491683986535 4503599627370496 12500018513 1089000000000000000 (hp754542 rfl rfl rfl) rfl)) rfl

noncomputable def hp754544 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1660292)))) 1 4

noncomputable def hp754545 := @hp754544 0 1 883940668245411 562949953421312 200000001089 2178000000000000000 883940668245411 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp754546 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1660292))) 884279719003555 562949953421312 1

noncomputable def hp754547 := @hp754546 2000000000000000 20209 33554432 1 10890000 29660127044675202711552 883940668245411 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp754548 := BSN.arctan_dyadic_bound_f 1000 1660292 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp754549 := hp754548 1 20209 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1660292) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1660292) 0 0 rfl)

noncomputable def hp754550 := hp754545 (hp754547 (hp754549 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp754551 := @hp754524 15943269800553 33554432000 1245219 268435456000 hp754525 14516333033768780018471 9007199254740992000 20946577417759608493 hp740893 (@hp754527 1 hp754528 18796071932811253625639 9007199254740992000 1746140061506233 726000000000000000000 (@hp754531 726000000000000000000 hp754543 hp754550 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 830146 2000) rfl rfl)

noncomputable def hp754552 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 830146 2000) (Real.log Real.pi) 830146 2000 0 1 38410761 33554432

noncomputable def hp754553 := hp754551 (@hp754552 3 268435456 15943269800553 33554432000 1245219 268435456000 (Enclosure.Real.IsNear.const Bool.false 830146 2000) hd4909 rfl) rfl

noncomputable def hp754554 := @hp754514 hp740893 54077547883 33554432 237 33554432 (@hp754518 hp754512 hp754513 20946577417759608493 hp740893 (hp754520 rfl rfl rfl rfl rfl) (hp754523 (hp754553 rfl) (Enclosure.Real.IsNear.const Bool.true hp754516 hp754517) rfl rfl)) rfl

noncomputable def hp754555 := nat_lit 7593412885152767175294976

noncomputable def hp754556 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 54077547883) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp754555) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp754557 := BSN.sin_reduce_arg_pos_rat_q1 54077547883 33554432 226375608064910080 72057594037927936 256 hp754555 hp619237 rfl rfl rfl rfl

noncomputable def hp754558 := nat_lit 14361481913287008567944548528282453500978772520193821572769120606869570422985782717430344389078727570442025950555155613060486874575117398183936

noncomputable def hp754559 := nat_lit 10210488493410768435866710217119336149096938317352941013320332885018834619626742525531768850708652532552291876965018114595121786014273536

noncomputable def hp754560 := nat_lit 71718296857821699944048515032764396737109126622312483675064687254734717785176900883743719041192291077967599595510520006025955407808452549021696

noncomputable def hp754561 := BSN.sin_dyadic_bound_f 215817774606 137438953472 4 3 67108864 21801270 hp754558 hp737934 hp754559 hp754560 hp737937

noncomputable def hp754562 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215817774606) (BSN.sinEvenQ 137438953472) 0 3 hp754558 hp737934 hp754559 rfl rfl rfl

noncomputable def hp754563 := hp754561 hp754559 67108855 rfl rfl rfl rfl rfl rfl rfl rfl (hp754562 rfl)

noncomputable def hp754564 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215817774606) (BSN.sinOddQ 137438953472) 0 3 hp754560 hp737937 hp754559 rfl rfl rfl

noncomputable def hp754565 := @BSN.sin_arg_round Bool.false 67108855 67108864 hp754555 hp619237 215817774606 137438953472 21801270 21780000 (hp754563 (hp754564 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754566 := hp754556 67108855 67108864 256 1000000000000000 21780000 10890000 hp754557 BSN.pi_near_15 hp754565 rfl rfl

noncomputable def hp754567 := @hp754511 237 33554432 Bool.true 67108855 67108864 1 10890000 hp754554 (Enclosure.sfrac_false_div 54077547883 33554432) (hp754566 rfl rfl) rfl

noncomputable def hp754568 := @hp754508 67108855 67108864 163405277 22837985280000 536870840 536870912 3842 536870912 (@hp754509 Bool.true 67108855 67108864 163405277 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000)) (@hp754510 2614484432 365407764480000 67108855 67108864 163405277 22837985280000 (hp754567 rfl) rfl))

noncomputable def hp754569 := @hp754514 hp740893 865240766132 536870912 3783 536870912 (@hp754518 hp754512 hp754513 20946577417759608493 hp740893 (hp754520 rfl rfl rfl rfl rfl) (hp754523 (hp754553 rfl) (Enclosure.Real.IsNear.const Bool.true hp754516 hp754517) rfl rfl)) rfl

noncomputable def hp754570 := hp754507 (BSN.cos_quad_nat1 445 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 313495221 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl rfl (hp754568 rfl) hp754569

noncomputable def hp754571 := nat_lit 27205958792814091932112005109012865084096823002081917518902322576907175745

noncomputable def hp754572 := nat_lit 11717401970207390408047839332875417823921329353045436195749329542448961

noncomputable def hp754573 := nat_lit 71234730568466095475823174021828086448538663805547710414712964977402447681

noncomputable def hp754574 := BSN.sin_dyadic_bound_f 573593097 536870912 3 2 536870912 268435456 hp754571 hp708845 hp754572 hp754573 hp708848

noncomputable def hp754575 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 573593097) (BSN.sinEvenQ 536870912) 0 2 hp754571 hp708845 hp754572 rfl rfl rfl

noncomputable def hp754576 := hp754574 hp754572 470530511 rfl rfl rfl rfl rfl rfl rfl rfl (hp754575 rfl)

noncomputable def hp754577 := @BSN.binarySplit_of_base2 (BSN.sinOddP 573593097) (BSN.sinOddQ 536870912) 0 2 hp754573 hp708848 hp754572 rfl rfl rfl

noncomputable def hp754578 := nat_lit 3155589786117173224915405679707100206573506300738559911305995878400000000

noncomputable def hp754579 := nat_lit 157759343627392342885598069169864582145354690856143360000000000000000

noncomputable def hp754580 := nat_lit 8264384496131485525270914383311368379321424022911032678456655872000000000

noncomputable def hp754581 := BSN.sin_dyadic_bound_f 334772200 536870912 3 2 536870912 268435456 hp754578 hp708845 hp754579 hp754580 hp708848

noncomputable def hp754582 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 334772200) (BSN.sinEvenQ 536870912) 0 2 hp754578 hp708845 hp754579 rfl rfl rfl

noncomputable def hp754583 := hp754581 hp754579 313495221 rfl rfl rfl rfl rfl rfl rfl rfl (hp754582 rfl)

noncomputable def hp754584 := @BSN.binarySplit_of_base2 (BSN.sinOddP 334772200) (BSN.sinOddQ 536870912) 0 2 hp754580 hp708848 hp754579 rfl rfl rfl

noncomputable def hp754585 := hp754570 hd4911 hd4913 hd4915 hd4917 hd4918 (hp754576 (hp754577 rfl) rfl rfl rfl rfl) (hp754583 (hp754584 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754586 := hp754502 (BSN.cos_quad_nat3 175 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 337053595 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl rfl (hp754585 rfl rfl rfl rfl rfl) hp754569

noncomputable def hp754587 := nat_lit 2149513200494979697980879703576460151198505394934056260379306106649616640

noncomputable def hp754588 := nat_lit 73202865986069218672586192213522788355415719084381606985871580242176

noncomputable def hp754589 := nat_lit 5629558910941921763595881703150954692433986313663058349820205534857175296

noncomputable def hp754590 := BSN.sin_dyadic_bound_f 304134726 536870912 3 2 536870912 268435456 hp754587 hp708845 hp754588 hp754589 hp708848

noncomputable def hp754591 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 304134726) (BSN.sinEvenQ 536870912) 0 2 hp754587 hp708845 hp754588 rfl rfl rfl

noncomputable def hp754592 := hp754590 hp754588 288126774 rfl rfl rfl rfl rfl rfl rfl rfl (hp754591 rfl)

noncomputable def hp754593 := @BSN.binarySplit_of_base2 (BSN.sinOddP 304134726) (BSN.sinOddQ 536870912) 0 2 hp754589 hp708848 hp754588 rfl rfl rfl

noncomputable def hp754594 := nat_lit 4429757771828716676365318991575051875785797586764844868239472245579956480

noncomputable def hp754595 := nat_lit 310868295890999673784401684350403869555115129029596627216633013453056

noncomputable def hp754596 := nat_lit 11601243234691386819580184518064759020793047302746641022278362284973342976

noncomputable def hp754597 := BSN.sin_dyadic_bound_f 364394702 536870912 3 2 536870912 268435456 hp754594 hp708845 hp754595 hp754596 hp708848

noncomputable def hp754598 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 364394702) (BSN.sinEvenQ 536870912) 0 2 hp754594 hp708845 hp754595 rfl rfl rfl

noncomputable def hp754599 := hp754597 hp754595 337053595 rfl rfl rfl rfl rfl rfl rfl rfl (hp754598 rfl)

noncomputable def hp754600 := @BSN.binarySplit_of_base2 (BSN.sinOddP 364394702) (BSN.sinOddQ 536870912) 0 2 hp754596 hp708848 hp754595 rfl rfl rfl

noncomputable def hp754601 := hp754586 hd4920 hd4922 hd4924 hd4926 hd4918 (hp754592 (hp754593 rfl) rfl rfl rfl rfl) (hp754599 (hp754600 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754602 := hp754497 (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 439615960 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl rfl (hp754601 rfl rfl rfl rfl rfl) hp754569

noncomputable def hp754603 := nat_lit 18200647238109777555515637760000

noncomputable def hp754604 := BSN.sin_dyadic_bound_f 65316320 536870912 2 1 536870912 268435456 hp754603 hp708890 hp754603 hp754603 hp708891

noncomputable def hp754605 := @BSN.binarySplit_of_base (BSN.sinEvenP 65316320) (BSN.sinEvenQ 536870912) 0 1 hp754603 hp708890 hp754603 rfl rfl rfl

noncomputable def hp754606 := hp754604 hp754603 65155310 rfl rfl rfl rfl rfl rfl rfl rfl (hp754605 rfl)

noncomputable def hp754607 := @BSN.binarySplit_of_base (BSN.sinOddP 65316320) (BSN.sinOddQ 536870912) 0 1 hp754603 hp708891 hp754603 rfl rfl rfl

noncomputable def hp754608 := nat_lit 1620278306883490724534202236397749220534293924525745669767953258403190625

noncomputable def hp754609 := nat_lit 134750206187429904735679065903625666999908987954399131841153750390625

noncomputable def hp754610 := nat_lit 4860565420238097313793135351061440410268881955601328211040177467708790625

noncomputable def hp754611 := BSN.cos_dyadic_bound_f 328239755 536870912 3 2 536870912 268435456 hp754608 hp708868 hp754609 hp754610 hp708870

noncomputable def hp754612 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 328239755) (BSN.cosEvenQ 536870912) 0 2 hp754608 hp708868 hp754609 rfl rfl rfl

noncomputable def hp754613 := hp754611 hp754609 439615960 rfl rfl rfl rfl rfl rfl rfl rfl (hp754612 rfl)

noncomputable def hp754614 := @BSN.binarySplit_of_base2 (BSN.cosOddP 328239755) (BSN.cosOddQ 536870912) 0 2 hp754610 hp708870 hp754609 rfl rfl rfl

noncomputable def hp754615 := hp754602 hd4928 hd4930 hd4932 hd4934 hd4918 (hp754606 (hp754607 rfl) rfl rfl rfl rfl) (hp754613 (hp754614 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754616 := hp754492 (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 170486685 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl rfl (hp754615 rfl rfl rfl rfl rfl) hp754569

noncomputable def hp754617 := nat_lit 59081685563871827472158014873333775652269519628617615016005589039206193100843444524588227674132182293365777371136

noncomputable def hp754618 := nat_lit 78183872693394414091783858529957191431820320773171075209742149693289607209431032155997980006874952958611456

noncomputable def hp754619 := nat_lit 357698647434344250458036050770147328579631665201470173894797322627598829841228521781635347102702484866099778293760

noncomputable def hp754620 := BSN.cos_dyadic_bound_f 808648462 536870912 4 3 536870912 268435456 hp754617 hp716712 hp754618 hp754619 hp716714

noncomputable def hp754621 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 808648462) (BSN.cosEvenQ 536870912) 0 3 hp754617 hp716712 hp754618 rfl rfl rfl

noncomputable def hp754622 := hp754620 hp754618 34642309 rfl rfl rfl rfl rfl rfl rfl rfl (hp754621 rfl)

noncomputable def hp754623 := @BSN.binarySplit_of_base3 (BSN.cosOddP 808648462) (BSN.cosOddQ 536870912) 0 3 hp754619 hp716714 hp754618 rfl rfl rfl

noncomputable def hp754624 := nat_lit 905946255277176284031264794607616

noncomputable def hp754625 := BSN.sin_dyadic_bound_f 173490464 536870912 2 1 536870912 268435456 hp754624 hp708890 hp754624 hp754624 hp708891

noncomputable def hp754626 := @BSN.binarySplit_of_base (BSN.sinEvenP 173490464) (BSN.sinEvenQ 536870912) 0 1 hp754624 hp708890 hp754624 rfl rfl rfl

noncomputable def hp754627 := hp754625 hp754624 170486685 rfl rfl rfl rfl rfl rfl rfl rfl (hp754626 rfl)

noncomputable def hp754628 := @BSN.binarySplit_of_base (BSN.sinOddP 173490464) (BSN.sinOddQ 536870912) 0 1 hp754624 hp708891 hp754624 rfl rfl rfl

noncomputable def hp754629 := hp754616 hd4936 hd4938 hd4940 hd4942 hd4918 (hp754622 (hp754623 rfl) rfl rfl rfl rfl) (hp754627 (hp754628 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754630 := hp754487 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 211406613 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl rfl (hp754629 rfl rfl rfl rfl rfl) hp754569

noncomputable def hp754631 := nat_lit 43308031219483119718914310106832598764553980952195618999208383994324242558971545731452832808050440712531099979776

noncomputable def hp754632 := nat_lit 30869185234456724391695333685666916433540830964023596896852959801941024218163945086574039522151115690807296

noncomputable def hp754633 := nat_lit 262342432894264324811341585954042672201333699495694584093358041465611893780763214121693184063503908547243860234240

noncomputable def hp754634 := BSN.cos_dyadic_bound_f 748388486 536870912 4 3 536870912 268435456 hp754631 hp716712 hp754632 hp754633 hp716714

noncomputable def hp754635 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 748388486) (BSN.cosEvenQ 536870912) 0 3 hp754631 hp716712 hp754632 rfl rfl rfl

noncomputable def hp754636 := hp754634 hp754632 94432525 rfl rfl rfl rfl rfl rfl rfl rfl (hp754635 rfl)

noncomputable def hp754637 := @BSN.binarySplit_of_base3 (BSN.cosOddP 748388486) (BSN.cosOddQ 536870912) 0 3 hp754633 hp716714 hp754632 rfl rfl rfl

noncomputable def hp754638 := nat_lit 2229277005191771369615068625400625

noncomputable def hp754639 := BSN.sin_dyadic_bound_f 217290635 536870912 2 1 536870912 268435456 hp754638 hp708890 hp754638 hp754638 hp708891

noncomputable def hp754640 := @BSN.binarySplit_of_base (BSN.sinEvenP 217290635) (BSN.sinEvenQ 536870912) 0 1 hp754638 hp708890 hp754638 rfl rfl rfl

noncomputable def hp754641 := hp754639 hp754638 211406613 rfl rfl rfl rfl rfl rfl rfl rfl (hp754640 rfl)

noncomputable def hp754642 := @BSN.binarySplit_of_base (BSN.sinOddP 217290635) (BSN.sinOddQ 536870912) 0 1 hp754638 hp708891 hp754638 rfl rfl rfl

noncomputable def hp754643 := hp754630 hd4944 hd4946 hd4961 hd4963 hd4918 (hp754636 (hp754637 rfl) rfl rfl rfl rfl) (hp754641 (hp754642 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754644 := @hp754482 100723 134217728 (hp754643 rfl rfl rfl rfl rfl) (hp754643 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp754645 := @hp754480 Bool.true 542567059 268435456 100723 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 830146 1000)) (Enclosure.sfrac Bool.false 830146 1000) 11) hp754644

noncomputable def hp754646 := @Enclosure.Real.IsNear.mulLit_tf hp754471 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1))) 9897061 33554432 1

noncomputable def hp754647 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp754470 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754648 := @hp754647 1 1 0 1 9897061 33554432 1 33554432 9897061 33554432 1

noncomputable def hp754649 := @Enclosure.Real.IsNear.of_eq (hp754470 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754650 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 830146 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754651 := @hp754649 (@Inv.inv Real Real.instInv (Real.sqrt hp754472)) Bool.false 9897061 33554432 1 33554432 (hp754650 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 830146 1000) 830146 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000))))

noncomputable def hp754652 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp754472)) Bool.false 19794122 67108864 2 67108864 9897061 33554432

noncomputable def hp754653 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp754472) Bool.false 227522073 67108864 7 67108864 227522073 67108864 7 67108864

noncomputable def hp754654 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 830146 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754655 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 830146 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754656 := @hp754655 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 830146 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4433273096611

noncomputable def hp754657 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 830146 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 830146 1000 0

noncomputable def hp754658 := @hp754657 1 10680707 67108864 1 67108864 4433273096611 33554432000 415073 33554432000 (Enclosure.Real.IsNear.const Bool.false 830146 1000) hd4949

noncomputable def hp754659 := @hp754656 33554432000 415073 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 830146 1000) 830146 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000))) (hp754658 rfl)

noncomputable def hp754660 := @hp754654 4433273096611 33554432000 415073 33554432000 385688924 385688961 33554432 hp754659 rfl rfl rfl

noncomputable def hp754661 := @Enclosure.Real.IsNear.recentre' hp754472 Bool.false 771377885 67108864 37 67108864 771377885 67108864 37 67108864 (hp754660 rfl rfl rfl)

noncomputable def hp754662 := @Enclosure.Real.IsNear.sqrt_image hp754472 771377885 67108864 37 67108864 113761033 113761040 33554432 (hp754661 rfl) rfl rfl

noncomputable def hp754663 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp754472) 227522073 67108864 7 67108864 9897060 9897062 33554432 (hp754653 (hp754662 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp754664 := @hp754648 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp754651 (@hp754652 1 33554432 (hp754663 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp754665 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754666 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp754667 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1))) (hp754665 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754666 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp754668 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 830146 1000) 830146 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl

noncomputable def hp754669 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754670 := @hp754669 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754666 (Enclosure.sfrac Bool.false 1 16)))) 67150039

noncomputable def hp754671 := @hp754670 67108864 241 67108864 6417337 16777216 319323679 45675970560000 430924429826143 1125899906842624 1282661682563131 153263124818952192000

noncomputable def hp754672 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754673 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754674 := @hp754672 (@Neg.neg Real Real.instNeg hp754673) Bool.true 67150039 67108864 241 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754675 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754676 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp754677 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp754678 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 104239241) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp754679 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1))) Bool.false 29340737987110895254455

noncomputable def hp754680 := nat_lit 998484790419646984368891331

noncomputable def hp754681 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp754682 := @Enclosure.Real.IsNear.subLit_ff_p hp754472 (Enclosure.sfrac Bool.false 11 1) 771377885 67108864 37 67108864 11 1 0

noncomputable def hp754683 := @hp754681 500000000000000 33180381 67108864 37 67108864 29340737987110895254455 9444732965739290427392 hp754680 hp738031 hd4948 (@hp754682 1 33180381 33180381 67108864 37 67108864 (hp754661 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754684 := @hp754678 104239241 33554432 233 67108864 Bool.true 67067714 67108864 1 10890000 (@hp754679 9444732965739290427392 hp754680 hp738031 104239241 33554432 233 67108864 (hp754683 rfl) rfl) (Enclosure.sfrac_false_div 104239241 33554432)

noncomputable def hp754685 := nat_lit 7426552874326789657198592

noncomputable def hp754686 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 104239241) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp754685) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp754687 := BSN.sin_reduce_arg_pos_rat_q1 104239241 33554432 226375608064910080 72057594037927936 0 hp754685 hp619237 rfl rfl rfl rfl

noncomputable def hp754688 := nat_lit 13137905676702122443091869481639743867799639405244528248895006533960303244556595485591411484999761702977543094913753145932628862047368804691681

noncomputable def hp754689 := nat_lit 7820772817367260683773427230205988812280097156397456333572399439713871339419175320262002207193519483712296517447758212127037518752902881

noncomputable def hp754690 := nat_lit 65614930790095545423829832545471265902852662471273270229226155878402643213939384854446847315861142173350496752201238099493282331891005327535841

noncomputable def hp754691 := BSN.sin_dyadic_bound_f 211075327863 137438953472 4 3 67108864 21801270 hp754688 hp737934 hp754689 hp754690 hp737937

noncomputable def hp754692 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 211075327863) (BSN.sinEvenQ 137438953472) 0 3 hp754688 hp737934 hp754689 rfl rfl rfl

noncomputable def hp754693 := hp754691 hp754689 67067714 rfl rfl rfl rfl rfl rfl rfl rfl (hp754692 rfl)

noncomputable def hp754694 := @BSN.binarySplit_of_base3 (BSN.sinOddP 211075327863) (BSN.sinOddQ 137438953472) 0 3 hp754690 hp737937 hp754689 rfl rfl rfl

noncomputable def hp754695 := @BSN.sin_arg_round Bool.false 67067714 67108864 hp754685 hp619237 211075327863 137438953472 21801270 21780000 (hp754693 (hp754694 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754696 := hp754686 67067714 67108864 0 1000000000000000 21780000 10890000 hp754687 BSN.pi_near_15 hp754695 rfl rfl

noncomputable def hp754697 := @hp754676 33533857 33554432 162779929 45675970560000 (@hp754677 67067714 67108864 2604478864 730815528960000 33533857 33554432 162779929 45675970560000 (hp754684 (hp754696 rfl rfl) rfl rfl) rfl)

noncomputable def hp754698 := @hp754675 33533857 33554432 162779929 45675970560000 33574899 33575140 33554432 hp754697 rfl rfl rfl

noncomputable def hp754699 := @Enclosure.Real.IsNear.recentre' hp754673 Bool.false 67150039 67108864 241 67108864 67150039 67108864 241 67108864 (hp754698 rfl rfl rfl)

noncomputable def hp754700 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754666 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp754701 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754666 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65877423)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp754702 := nat_lit 1244389343315377304283427523845

noncomputable def hp754703 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754666 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp754702

noncomputable def hp754704 := nat_lit 26653485692396560921578645672170489

noncomputable def hp754705 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754666 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp754706 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp754707 := @hp754706 (Enclosure.sfrac Bool.false 1 16) 1125759992692023 4503599627370496 4938377531 4503599627370496 1 16 0

noncomputable def hp754708 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)) 1100937683305161

noncomputable def hp754709 := @hp754708 4503599627370496 2455349563 4503599627370496 33180381 67108864 37 67108864 75548474246209965391872 1125759992692023 4503599627370496 4938377531

noncomputable def hp754710 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)) 33180381 67108864 37

noncomputable def hp754711 := @hp754710 67108864 33180381 67108864 37 67108864 1100937683305161 4503599627370496 2455349563 4503599627370496 (@hp754682 1 33180381 33180381 67108864 37 67108864 (hp754661 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754712 := hp754711 (@hp754682 1 33180381 33180381 67108864 37 67108864 (hp754661 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754713 := @hp754709 4503599627370496 (hp754712 rfl) (@hp754682 1 33180381 33180381 67108864 37 67108864 (hp754661 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754714 := @hp754705 500000000000000 1407234969402679 4503599627370496 4938377531 4503599627370496 hp754702 hp627574 hp754704 hp742826 hd4948 (@hp754707 1 22515759510442864 1407234969402679 4503599627370496 4938377531 4503599627370496 (hp754713 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp754715 := @hp754701 65877423 33554432 463 67108864 Bool.true 12834674 33554432 1 10890000 (@hp754703 hp627574 hp754704 hp742826 65877423 33554432 463 67108864 (hp754714 rfl) rfl) (Enclosure.sfrac_true_div 65877423 33554432)

noncomputable def hp754716 := nat_lit 609396481159490248059456277823859119505985827295507538658998940115363347722424857626324759796657601

noncomputable def hp754717 := nat_lit 6680965431305953513584390771096465509679576362573858954408428446673592674239372177759140457921

noncomputable def hp754718 := nat_lit 3675365800840092269739417415623954734047292315764434678184403169754031527713706805298345471930674625

noncomputable def hp754719 := BSN.cos_dyadic_bound_t 65877423 33554432 4 3 33554432 10890000 hp754716 hp681868 hp754717 hp754718 hp681871

noncomputable def hp754720 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 65877423) (BSN.cosEvenQ 33554432) 0 3 hp754716 hp681868 hp754717 rfl rfl rfl

noncomputable def hp754721 := hp754719 hp754717 12834674 rfl rfl rfl rfl rfl rfl rfl rfl (hp754720 rfl)

noncomputable def hp754722 := @BSN.binarySplit_of_base3 (BSN.cosOddP 65877423) (BSN.cosOddQ 33554432) 0 3 hp754718 hp681871 hp754717 rfl rfl rfl

noncomputable def hp754723 := hp754715 (BSN.cos_neg_of_bound 65877423 33554432 Bool.true 12834674 33554432 1 10890000 (hp754721 (hp754722 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp754724 := hp754671 (hp754674 (@Enclosure.Real.IsNear.neg hp754673 Bool.false 67150039 67108864 241 67108864 (hp754699 rfl))) (@hp754700 12834674 33554432 5109178864 730815528960000 6417337 16777216 319323679 45675970560000 (hp754723 rfl) rfl)

noncomputable def hp754725 := @hp754646 33554432 430924429826143 1125899906842624 1282661682563131 153263124818952192000 4264885368379556665723 37778931862957161709568 12753241785361710136997 hp743344 (hp754664 rfl) (@hp754667 Bool.false 430924429826143 1125899906842624 1282661682563131 153263124818952192000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754472 (Enclosure.sfrac Bool.false 11 1)) (hp754668 rfl (hp754475 rfl rfl))) (hp754724 rfl))

noncomputable def hp754726 := @hp754469 hp754467 hp743344 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 830146 1000))) (@hp754474 hp754467 hp743344 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 830146 1000) 11 (hp754475 rfl rfl)) (@hp754478 hp754467 hp743344 hp754645 (hp754725 rfl) rfl rfl))

theorem hd5028 : hp754468 hp743344 := hp754726

noncomputable def hp754727 := nat_lit 1939005513320656690268581

noncomputable def hp754728 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 831433 1000)) Bool.false 15784989092937944361795 18889465931478580854784 hp754727

noncomputable def hp754729 := nat_lit 2571328549922521818857472000

noncomputable def hp754730 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 831433 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 831433 1000)) Bool.false 15784989092937944361795 18889465931478580854784

noncomputable def hp754731 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 831433 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754732 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp754731 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754733 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 831433 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754734 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp754732 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp754735 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 831433 1000)) hp754734 Bool.false 15784989092937944361795 18889465931478580854784

noncomputable def hp754736 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 831433 1000) 831433 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl

noncomputable def hp754737 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp754732 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp754738 := nat_lit 4237250745117823474461069803520

noncomputable def hp754739 := @hp754737 194028849 268435456 201753 268435456 2131422654570346933059 18889465931478580854784 6424561970777840732581 hp754729 hp754738 15784989092937944361795 18889465931478580854784

noncomputable def hp754740 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) 11)

noncomputable def hp754741 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) 11) hp754740

noncomputable def hp754742 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) 11)

noncomputable def hp754743 := @hp754742 194028849 536870912 201753 536870912 194028849 536870912 201753 536870912 208336890233880576 194028849 268435456

noncomputable def hp754744 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp754745 := hp754744 BSN.quadSignNeg 9 10 11 831433 1000 190 241 536870912 268435456 9007199254740992

noncomputable def hp754746 := hp754745 Bool.false 866928245459 3789 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp754747 := hp754746 Bool.false 308437610 173199 Bool.true 651886919 Bool.true 186643911 28296951008113761 1 Bool.false 187397392

noncomputable def hp754748 := hp754747 Bool.true Bool.false 182906889 Bool.true Bool.false 194028849 201753 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 187397392 536870912) BSN.abs_quadSignNeg

noncomputable def hp754749 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp754750 := hp754749 BSN.quadSignPos 7 8 9 831433 1000 72 135 536870912 268435456 9007199254740992

noncomputable def hp754751 := hp754750 Bool.false 866928245459 3789 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp754752 := hp754751 Bool.false 210838096 141451 Bool.true 557965222 Bool.true 4189732 28296951008113761 1 Bool.false 272103030

noncomputable def hp754753 := hp754752 Bool.false Bool.false 4189689 Bool.false Bool.false 308437610 173199 BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 272103030 536870912) BSN.abs_quadSignPos

noncomputable def hp754754 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp754755 := hp754754 BSN.quadSignNeg 5 6 7 831433 1000 79 1 536870912 268435456 9007199254740992

noncomputable def hp754756 := hp754755 Bool.false 866928245459 3789 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp754757 := hp754756 Bool.false 234278144 105114 Bool.false 514774320 Bool.true 828607455 28296951008113761 1 Bool.false 439443240

noncomputable def hp754758 := hp754757 Bool.false Bool.false 536669472 Bool.true Bool.false 210838096 141451 BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 439443240 536870912) BSN.abs_quadSignNeg

noncomputable def hp754759 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp754760 := hp754759 BSN.quadSignPos 3 4 5 831433 1000 294 176 536870912 268435456 9007199254740992

noncomputable def hp754761 := hp754760 Bool.false 866928245459 3789 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp754762 := hp754761 Bool.false 249775679 62127 Bool.false 190435156 Bool.false 96513458 28296951008113761 1 Bool.false 503448639

noncomputable def hp754763 := hp754762 Bool.true Bool.false 528219122 Bool.false Bool.false 234278144 105114 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 294 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 503448639 536870912) BSN.abs_quadSignPos

noncomputable def hp754764 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp754765 := hp754764 BSN.quadSignNeg 1 2 3 831433 1000 661 446 536870912 268435456 9007199254740992

noncomputable def hp754766 := hp754765 Bool.false 866928245459 3789 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp754767 := hp754766 Bool.false 536870600 3842 Bool.false 95510701 Bool.false 419847370 28296951008113761 1 Bool.false 95007689

noncomputable def hp754768 := hp754767 Bool.true Bool.false 380902806 Bool.true Bool.false 249775679 62127 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 661 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 95007689 536870912) BSN.abs_quadSignNeg

noncomputable def hp754769 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) 1) Bool.false

noncomputable def hp754770 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)))

noncomputable def hp754771 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000))) Bool.false 67108825 67108864

noncomputable def hp754772 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 54183015341) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 54183015341 33554432

noncomputable def hp754773 := nat_lit 86484757593923980507196476865902015905192028538383567649527

noncomputable def hp754774 := nat_lit 53558239596781549336005261524104288860280437199601664000

noncomputable def hp754775 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) Bool.false hp754773 hp754774 41957891366048011253

noncomputable def hp754776 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 831433 4000) (Real.log (Enclosure.sfrac Bool.false 2765124333956 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1662866))))))

noncomputable def hp754777 := nat_lit 190711957863773777042712655548640000

noncomputable def hp754778 := nat_lit 951385452139802178379661894853290406720

noncomputable def hp754779 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp754776 (Enclosure.sfrac Bool.false 831433 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 831433 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp754777 hp754778)) Bool.false

noncomputable def hp754780 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 831433 1000) 831433 1000 2765124333956 16000000 1662866

noncomputable def hp754781 := hp754780 4000 2000 hp754777 hp754778 (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl rfl rfl rfl

noncomputable def hp754782 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp754776 (Enclosure.sfrac Bool.false 831433 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 831433 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp754777 hp754778) 29089288472271212896287 18014398509481984000

noncomputable def hp754783 := nat_lit 27675122430055673762302872597088645089661449132282741647848640

noncomputable def hp754784 := @hp754782 41957891366048011253 hp737908 hp754777 hp754778 0 1 hp754783 hp754773 hp754774 41957891366048011253 hp737908

noncomputable def hp754785 := @Enclosure.Real.IsNear.subLit_ff_p (hp754776 (Enclosure.sfrac Bool.false 831433 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 831433 2000) (Real.log Real.pi)) 7532407256602385657043 3602879701896396800 3497642630954543 1452000000000000000000

noncomputable def hp754786 := nat_lit 390429820788483319474394077593600

noncomputable def hp754787 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 831433 4000) (Real.log (Enclosure.sfrac Bool.false 2765124333956 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1662866))))))

noncomputable def hp754788 := @hp754787 (Enclosure.sfrac Bool.false 831433 2000) 45150918980978995486751 18014398509481984000 3497642630954543 1452000000000000000000 831433 2000 0

noncomputable def hp754789 := nat_lit 75324072566023856570430000

noncomputable def hp754790 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 831433 4000) (Real.log (Enclosure.sfrac Bool.false 2765124333956 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1662866))))) 45157990510485708342751

noncomputable def hp754791 := nat_lit 101670830949086229523871640476868149248

noncomputable def hp754792 := @hp754790 18014398509481984000 10392927892319129 4356000000000000000000 883941188339107 2251799813685248 200000001089 8712000000000000000 hp754791 45150918980978995486751 18014398509481984000 3497642630954543

noncomputable def hp754793 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 831433 4000) (Real.log (Enclosure.sfrac Bool.false 2765124333956 16000000)) 831433 4000 0 1 54313444992543847 4503599627370496

noncomputable def hp754794 := nat_lit 116637234988035393355513856

noncomputable def hp754795 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2765124333956) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp754794 hp617687

noncomputable def hp754796 := BSN.log_rat_reduce_isNear 2765124333956 16000000 17 5530248667912 4194304000000 74223844 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp754797 := nat_lit 295222127436306491656912881279831484548390532210366069316287346078738766016274753766311985997328059269120

noncomputable def hp754798 := nat_lit 1878546841025774609166198687832710583579116443442084081654218872864469157033838476233662413758494408704

noncomputable def hp754799 := nat_lit 4161569013472959642308124868384209052187247846894485489887212131876105757759938744393973268807680

noncomputable def hp754800 := BSN.log_dyadic_bound 667972333956 4862276333956 5 4 hp754797 268435456 87120000 hp754798 hp754799 74223844 5530248667912

noncomputable def hp754801 := hp754800 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp754802 := @BSN.binarySplit_of_base4 (BSN.artanhP 667972333956) (BSN.artanhQ 4862276333956) 0 4 hp754798 hp754797 hp754799 rfl rfl rfl

noncomputable def hp754803 := hp754796 rfl rfl rfl rfl (hp754801 (hp754802 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp754804 := @hp754793 12500018513 1089000000000000000 45157990510485708342751 18014398509481984000 10392927892319129 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 831433 4000) (BSN.isNear_log_sfrac 2765124333956 16000000 54313444992543847 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp754795 1000001481040000 87120000000000000000000 54313444992543847 4503599627370496 12500018513 1089000000000000000 (hp754803 rfl rfl rfl) rfl)) rfl

noncomputable def hp754805 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1662866)))) 1 4

noncomputable def hp754806 := @hp754805 0 1 883941188339107 562949953421312 200000001089 2178000000000000000 883941188339107 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp754807 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1662866))) 884279719003555 562949953421312 1

noncomputable def hp754808 := @hp754807 2000000000000000 20178 33554432 1 10890000 29660144496123758772224 883941188339107 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp754809 := BSN.arctan_dyadic_bound_f 1000 1662866 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp754810 := hp754809 1 20178 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1662866) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1662866) 0 0 rfl)

noncomputable def hp754811 := hp754806 (hp754808 (hp754810 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp754812 := @hp754785 31935974250513 67108864000 2494299 536870912000 hp754786 29089288472271212896287 18014398509481984000 41957891366048011253 hp737908 (@hp754788 1 hp754789 7532407256602385657043 3602879701896396800 3497642630954543 1452000000000000000000 (@hp754792 1452000000000000000000 hp754804 hp754811 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 831433 2000) rfl rfl)

noncomputable def hp754813 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 831433 2000) (Real.log Real.pi) 831433 2000 0 1 38410761 33554432

noncomputable def hp754814 := hp754812 (@hp754813 3 268435456 31935974250513 67108864000 2494299 536870912000 (Enclosure.Real.IsNear.const Bool.false 831433 2000) hd4909 rfl) rfl

noncomputable def hp754815 := @hp754775 hp737908 54183015341 33554432 237 33554432 (@hp754779 hp754773 hp754774 41957891366048011253 hp737908 (hp754781 rfl rfl rfl rfl rfl) (hp754784 (hp754814 rfl) (Enclosure.Real.IsNear.const Bool.true hp754777 hp754778) rfl rfl)) rfl

noncomputable def hp754816 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 54183015341) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 5160588887166573084672) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp754817 := BSN.sin_reduce_arg_pos_rat_q0 54183015341 33554432 226375608064910080 72057594037927936 257 5160588887166573084672 hp619237 rfl rfl rfl rfl

noncomputable def hp754818 := BSN.cos_dyadic_bound_f 146672757 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp754819 := hp754818 1 67108825 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 146672757) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp754820 := hp754819 (@BSN.binarySplit_of_le (BSN.cosOddP 146672757) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp754821 := @BSN.cos_arg_round Bool.false 67108825 67108864 5160588887166573084672 hp619237 146672757 137438953472 21801270 21780000 hp754820 rfl

noncomputable def hp754822 := hp754816 67108825 67108864 257 1000000000000000 21780000 10890000 hp754817 BSN.pi_near_15 hp754821 rfl rfl

noncomputable def hp754823 := @hp754772 237 33554432 Bool.false 67108825 67108864 1 10890000 hp754815 (Enclosure.sfrac_false_div 54183015341 33554432) (hp754822 rfl rfl) rfl

noncomputable def hp754824 := @hp754769 67108825 67108864 163405277 22837985280000 536870600 536870912 3842 536870912 (@hp754770 Bool.false 67108825 67108864 163405277 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000)) (@hp754771 2614484432 365407764480000 67108825 67108864 163405277 22837985280000 (hp754823 rfl) rfl))

noncomputable def hp754825 := @hp754775 hp737908 866928245459 536870912 3789 536870912 (@hp754779 hp754773 hp754774 41957891366048011253 hp737908 (hp754781 rfl rfl rfl rfl rfl) (hp754784 (hp754814 rfl) (Enclosure.Real.IsNear.const Bool.true hp754777 hp754778) rfl rfl)) rfl

noncomputable def hp754826 := hp754768 (BSN.cos_quad_nat2 446 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 380902806 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl rfl (hp754824 rfl) hp754825

noncomputable def hp754827 := nat_lit 83216247922989240578163540982801

noncomputable def hp754828 := BSN.sin_dyadic_bound_f 95510701 536870912 2 1 536870912 268435456 hp754827 hp708890 hp754827 hp754827 hp708891

noncomputable def hp754829 := @BSN.binarySplit_of_base (BSN.sinEvenP 95510701) (BSN.sinEvenQ 536870912) 0 1 hp754827 hp708890 hp754827 rfl rfl rfl

noncomputable def hp754830 := hp754828 hp754827 95007689 rfl rfl rfl rfl rfl rfl rfl rfl (hp754829 rfl)

noncomputable def hp754831 := @BSN.binarySplit_of_base (BSN.sinOddP 95510701) (BSN.sinOddQ 536870912) 0 1 hp754827 hp708891 hp754827 rfl rfl rfl

noncomputable def hp754832 := nat_lit 4337616992692498073831332006589217178278477222670453322281109260592800000

noncomputable def hp754833 := nat_lit 965453799982575725052335292875895595052620933869175574105472100000000

noncomputable def hp754834 := nat_lit 13010920070477529070043891349181899743645326426143621615695116837578400000

noncomputable def hp754835 := BSN.cos_dyadic_bound_f 419847370 536870912 3 2 536870912 268435456 hp754832 hp708868 hp754833 hp754834 hp708870

noncomputable def hp754836 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 419847370) (BSN.cosEvenQ 536870912) 0 2 hp754832 hp708868 hp754833 rfl rfl rfl

noncomputable def hp754837 := hp754835 hp754833 380902806 rfl rfl rfl rfl rfl rfl rfl rfl (hp754836 rfl)

noncomputable def hp754838 := @BSN.binarySplit_of_base2 (BSN.cosOddP 419847370) (BSN.cosOddQ 536870912) 0 2 hp754834 hp708870 hp754833 rfl rfl rfl

noncomputable def hp754839 := hp754826 hd4911 hd4913 hd4915 hd4917 hd4918 (hp754830 (hp754831 rfl) rfl rfl rfl rfl) (hp754837 (hp754838 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754840 := hp754763 (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 528219122 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl rfl (hp754839 rfl rfl rfl rfl rfl) hp754825

noncomputable def hp754841 := nat_lit 183561405883437830123160319635509758929031949421848368271930099352272896

noncomputable def hp754842 := nat_lit 1729724784010250252631504443393878434459590775852737678294416162816

noncomputable def hp754843 := nat_lit 550680758200745469868975695897642489030226929083993399340433709224493056

noncomputable def hp754844 := BSN.cos_dyadic_bound_f 190435156 536870912 3 2 536870912 268435456 hp754841 hp708868 hp754842 hp754843 hp708870

noncomputable def hp754845 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 190435156) (BSN.cosEvenQ 536870912) 0 2 hp754841 hp708868 hp754842 rfl rfl rfl

noncomputable def hp754846 := hp754844 hp754842 503448639 rfl rfl rfl rfl rfl rfl rfl rfl (hp754845 rfl)

noncomputable def hp754847 := @BSN.binarySplit_of_base2 (BSN.cosOddP 190435156) (BSN.cosOddQ 536870912) 0 2 hp754843 hp708870 hp754842 rfl rfl rfl

noncomputable def hp754848 := nat_lit 86766385347677288044658468359696

noncomputable def hp754849 := BSN.cos_dyadic_bound_f 96513458 536870912 2 1 536870912 268435456 hp754848 hp708767 hp754848 hp754848 hp708768

noncomputable def hp754850 := @BSN.binarySplit_of_base (BSN.cosEvenP 96513458) (BSN.cosEvenQ 536870912) 0 1 hp754848 hp708767 hp754848 rfl rfl rfl

noncomputable def hp754851 := hp754849 hp754848 528219122 rfl rfl rfl rfl rfl rfl rfl rfl (hp754850 rfl)

noncomputable def hp754852 := @BSN.binarySplit_of_base (BSN.cosOddP 96513458) (BSN.cosOddQ 536870912) 0 1 hp754848 hp708768 hp754848 rfl rfl rfl

noncomputable def hp754853 := hp754840 hd4920 hd4922 hd4924 hd4926 hd4918 (hp754846 (hp754847 rfl) rfl rfl rfl rfl) (hp754851 (hp754852 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754854 := hp754758 (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536669472 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl rfl (hp754853 rfl rfl rfl rfl rfl) hp754825

noncomputable def hp754855 := nat_lit 17646157588230840901140194889820823560449129098119547713626351222128640000

noncomputable def hp754856 := nat_lit 4930999842730646350612428675152611400693769675149679177341337600000000

noncomputable def hp754857 := nat_lit 46208143493240162266037614112628100335098976772743811197972367225651200000

noncomputable def hp754858 := BSN.sin_dyadic_bound_f 514774320 536870912 3 2 536870912 268435456 hp754855 hp708845 hp754856 hp754857 hp708848

noncomputable def hp754859 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 514774320) (BSN.sinEvenQ 536870912) 0 2 hp754855 hp708845 hp754856 rfl rfl rfl

noncomputable def hp754860 := hp754858 hp754856 439443240 rfl rfl rfl rfl rfl rfl rfl rfl (hp754859 rfl)

noncomputable def hp754861 := @BSN.binarySplit_of_base2 (BSN.sinOddP 514774320) (BSN.sinOddQ 536870912) 0 2 hp754857 hp708848 hp754856 rfl rfl rfl

noncomputable def hp754862 := nat_lit 169148379499835102667387266277572693063466443162249385959419725652379372259295658883961320966232974556690977290625

noncomputable def hp754863 := nat_lit 104757719612648412214637765331996377187045819685660308121362086171559839528848732546155671880692011962890625

noncomputable def hp754864 := nat_lit 844762273286294669487666107364740803050597592600306974953471983328528726704712341257973488266116025168303034890625

noncomputable def hp754865 := BSN.sin_dyadic_bound_f 828607455 536870912 4 3 536870912 268435456 hp754862 hp642702 hp754863 hp754864 hp642705

noncomputable def hp754866 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 828607455) (BSN.sinEvenQ 536870912) 0 3 hp754862 hp642702 hp754863 rfl rfl rfl

noncomputable def hp754867 := hp754865 hp754863 536669472 rfl rfl rfl rfl rfl rfl rfl rfl (hp754866 rfl)

noncomputable def hp754868 := @BSN.binarySplit_of_base3 (BSN.sinOddP 828607455) (BSN.sinOddQ 536870912) 0 3 hp754864 hp642705 hp754863 rfl rfl rfl

noncomputable def hp754869 := hp754854 hd4928 hd4930 hd4932 hd4934 hd4918 (hp754860 (hp754861 rfl) rfl rfl rfl rfl) (hp754867 (hp754868 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754870 := hp754753 (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 4189689 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl rfl (hp754869 rfl rfl rfl rfl rfl) hp754825

noncomputable def hp754871 := nat_lit 13360255297038943579845091599475376033688170361842424919287968743798941089461705755213808181780004207951942455296

noncomputable def hp754872 := nat_lit 910511765830106911908557739132829950598192903704978206624855273877887747193117996678933620853436251836416

noncomputable def hp754873 := nat_lit 81014712531777705392617302855277087675576110413774875501856253284213749421233837896828165051491959611984341831680

noncomputable def hp754874 := BSN.cos_dyadic_bound_f 557965222 536870912 4 3 536870912 268435456 hp754871 hp716712 hp754872 hp754873 hp716714

noncomputable def hp754875 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 557965222) (BSN.cosEvenQ 536870912) 0 3 hp754871 hp716712 hp754872 rfl rfl rfl

noncomputable def hp754876 := hp754874 hp754872 272103030 rfl rfl rfl rfl rfl rfl rfl rfl (hp754875 rfl)

noncomputable def hp754877 := @BSN.binarySplit_of_base3 (BSN.cosOddP 557965222) (BSN.cosOddQ 536870912) 0 3 hp754873 hp716714 hp754872 rfl rfl rfl

noncomputable def hp754878 := BSN.sin_dyadic_bound_f 4189732 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp754879 := hp754878 1 4189689 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 4189732) (BSN.sinEvenQ 536870912) 0 0 rfl)

noncomputable def hp754880 := hp754879 (@BSN.binarySplit_of_le (BSN.sinOddP 4189732) (BSN.sinOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp754881 := hp754870 hd4936 hd4938 hd4940 hd4942 hd4918 (hp754876 (hp754877 rfl) rfl rfl rfl rfl) hp754880 rfl

noncomputable def hp754882 := hp754748 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 182906889 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl rfl (hp754881 rfl rfl rfl rfl rfl) hp754825

noncomputable def hp754883 := nat_lit 24907804861850112710470594371266006196060971735437066979075136960151559087431271342077737409460925809011278692641

noncomputable def hp754884 := nat_lit 5889347723041222618698031274818780193447774814890224231770173204093927252224342940838744590992709306499361

noncomputable def hp754885 := nat_lit 150977143050191841283918260869584386357169149009058606248508990910041586134351364872441674028712817094153976365345

noncomputable def hp754886 := BSN.cos_dyadic_bound_f 651886919 536870912 4 3 536870912 268435456 hp754883 hp716712 hp754884 hp754885 hp716714

noncomputable def hp754887 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 651886919) (BSN.cosEvenQ 536870912) 0 3 hp754883 hp716712 hp754884 rfl rfl rfl

noncomputable def hp754888 := hp754886 hp754884 187397392 rfl rfl rfl rfl rfl rfl rfl rfl (hp754887 rfl)

noncomputable def hp754889 := @BSN.binarySplit_of_base3 (BSN.cosOddP 651886919) (BSN.cosOddQ 536870912) 0 3 hp754885 hp716714 hp754884 rfl rfl rfl

noncomputable def hp754890 := nat_lit 1213543378498476067122894262598241

noncomputable def hp754891 := BSN.sin_dyadic_bound_f 186643911 536870912 2 1 536870912 268435456 hp754890 hp708890 hp754890 hp754890 hp708891

noncomputable def hp754892 := @BSN.binarySplit_of_base (BSN.sinEvenP 186643911) (BSN.sinEvenQ 536870912) 0 1 hp754890 hp708890 hp754890 rfl rfl rfl

noncomputable def hp754893 := hp754891 hp754890 182906889 rfl rfl rfl rfl rfl rfl rfl rfl (hp754892 rfl)

noncomputable def hp754894 := @BSN.binarySplit_of_base (BSN.sinOddP 186643911) (BSN.sinOddQ 536870912) 0 1 hp754890 hp708891 hp754890 rfl rfl rfl

noncomputable def hp754895 := hp754882 hd4944 hd4946 hd4961 hd4963 hd4918 (hp754888 (hp754889 rfl) rfl rfl rfl rfl) (hp754893 (hp754894 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754896 := @hp754743 201753 268435456 (hp754895 rfl rfl rfl rfl rfl) (hp754895 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp754897 := @hp754741 Bool.false 194028849 268435456 201753 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 831433 1000)) (Enclosure.sfrac Bool.false 831433 1000) 11) hp754896

noncomputable def hp754898 := @Enclosure.Real.IsNear.mulLit_tf hp754732 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1))) 9893229 33554432 1

noncomputable def hp754899 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp754731 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754900 := @hp754899 1 1 0 1 9893229 33554432 1 33554432 9893229 33554432 1

noncomputable def hp754901 := @Enclosure.Real.IsNear.of_eq (hp754731 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754902 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 831433 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754903 := @hp754901 (@Inv.inv Real Real.instInv (Real.sqrt hp754733)) Bool.false 9893229 33554432 1 33554432 (hp754902 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 831433 1000) 831433 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000))))

noncomputable def hp754904 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp754733)) Bool.false 19786458 67108864 2 67108864 9893229 33554432

noncomputable def hp754905 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp754733) Bool.false 227610205 67108864 7 67108864 227610205 67108864 7 67108864

noncomputable def hp754906 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 831433 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754907 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 831433 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754908 := @hp754907 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 831433 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8880292263131

noncomputable def hp754909 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 831433 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 831433 1000 0

noncomputable def hp754910 := @hp754909 1 10680707 67108864 1 67108864 8880292263131 67108864000 831433 67108864000 (Enclosure.Real.IsNear.const Bool.false 831433 1000) hd4949

noncomputable def hp754911 := @hp754908 67108864000 831433 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 831433 1000) 831433 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000))) (hp754910 rfl)

noncomputable def hp754912 := @hp754906 8880292263131 67108864000 831433 67108864000 385987781 385987818 33554432 hp754911 rfl rfl rfl

noncomputable def hp754913 := @Enclosure.Real.IsNear.recentre' hp754733 Bool.false 771975599 67108864 37 67108864 771975599 67108864 37 67108864 (hp754912 rfl rfl rfl)

noncomputable def hp754914 := @Enclosure.Real.IsNear.sqrt_image hp754733 771975599 67108864 37 67108864 113805099 113805106 33554432 (hp754913 rfl) rfl rfl

noncomputable def hp754915 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp754733) 227610205 67108864 7 67108864 9893228 9893230 33554432 (hp754905 (hp754914 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp754916 := @hp754900 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp754903 (@hp754904 1 33554432 (hp754915 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp754917 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754918 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp754919 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1))) (hp754917 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754918 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp754920 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 831433 1000) 831433 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl

noncomputable def hp754921 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754922 := @hp754921 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754918 (Enclosure.sfrac Bool.false 1 16)))) 33561791

noncomputable def hp754923 := @hp754922 33554432 15 4194304 6419281 16777216 80681701 11418992640000 215442567292271 562949953421312 3232126843965611 383157812047380480000

noncomputable def hp754924 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754925 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754926 := @hp754924 (@Neg.neg Real Real.instNeg hp754925) Bool.true 33561791 33554432 15 4194304 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754927 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754928 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp754929 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp754930 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 106117015) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp754931 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1))) Bool.false 29869284355075386127725

noncomputable def hp754932 := nat_lit 998484790424781308533614019

noncomputable def hp754933 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp754934 := @Enclosure.Real.IsNear.subLit_ff_p hp754733 (Enclosure.sfrac Bool.false 11 1) 771975599 67108864 37 67108864 11 1 0

noncomputable def hp754935 := @hp754933 500000000000000 33778095 67108864 37 67108864 29869284355075386127725 9444732965739290427392 hp754932 hp738031 hd4948 (@hp754934 1 33778095 33778095 67108864 37 67108864 (hp754913 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754936 := @hp754930 106117015 33554432 233 67108864 Bool.true 67094149 67108864 1 10890000 (@hp754931 9444732965739290427392 hp754932 hp738031 106117015 33554432 233 67108864 (hp754935 rfl) rfl) (Enclosure.sfrac_false_div 106117015 33554432)

noncomputable def hp754937 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 106117015) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 101263680228064975912960) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp754938 := BSN.sin_reduce_arg_pos_rat_q2 106117015 33554432 226375608064910080 72057594037927936 0 101263680228064975912960 hp619237 rfl rfl rfl rfl

noncomputable def hp754939 := BSN.cos_dyadic_bound_f 2878086895 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp754940 := hp754939 1 67094149 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2878086895) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp754941 := hp754940 (@BSN.binarySplit_of_le (BSN.cosOddP 2878086895) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp754942 := @BSN.cos_arg_round Bool.false 67094149 67108864 101263680228064975912960 hp619237 2878086895 137438953472 21801270 21780000 hp754941 rfl

noncomputable def hp754943 := hp754937 67094149 67108864 0 1000000000000000 21780000 10890000 hp754938 BSN.pi_near_15 hp754942 rfl rfl

noncomputable def hp754944 := @hp754928 67094149 67108864 162779929 45675970560000 (@hp754929 67094149 67108864 2604478864 730815528960000 67094149 67108864 162779929 45675970560000 (hp754936 (hp754943 rfl rfl) rfl rfl) rfl)

noncomputable def hp754945 := @hp754927 67094149 67108864 162779929 45675970560000 33561671 33561911 33554432 hp754944 rfl rfl rfl

noncomputable def hp754946 := @Enclosure.Real.IsNear.recentre' hp754925 Bool.false 67123582 67108864 240 67108864 33561791 33554432 15 4194304 (hp754945 rfl rfl rfl)

noncomputable def hp754947 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754918 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp754948 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754918 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65881631)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp754949 := nat_lit 1244468830346562748136876852605

noncomputable def hp754950 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754918 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp754949

noncomputable def hp754951 := nat_lit 134461045137684636839939836608121801

noncomputable def hp754952 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754918 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp754953 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp754954 := @hp754953 (Enclosure.sfrac Bool.false 1 16) 1125849881705055 4503599627370496 4982608367 4503599627370496 1 16 0

noncomputable def hp754955 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)) 1140959701829025

noncomputable def hp754956 := @hp754955 4503599627370496 2499580399 4503599627370496 33778095 67108864 37 67108864 75554506595760624107520 1125849881705055 4503599627370496 4982608367

noncomputable def hp754957 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)) 33778095 67108864 37

noncomputable def hp754958 := @hp754957 67108864 33778095 67108864 37 67108864 1140959701829025 4503599627370496 2499580399 4503599627370496 (@hp754934 1 33778095 33778095 67108864 37 67108864 (hp754913 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754959 := hp754958 (@hp754934 1 33778095 33778095 67108864 37 67108864 (hp754913 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754960 := @hp754956 4503599627370496 (hp754959 rfl) (@hp754934 1 33778095 33778095 67108864 37 67108864 (hp754913 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754961 := @hp754952 500000000000000 1407324858415711 4503599627370496 4982608367 4503599627370496 hp754949 hp627574 hp754951 hp738055 hd4948 (@hp754954 1 22517197734651376 1407324858415711 4503599627370496 4982608367 4503599627370496 (hp754960 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp754962 := @hp754948 65881631 33554432 117 16777216 Bool.true 12838562 33554432 1 10890000 (@hp754950 hp627574 hp754951 hp738055 65881631 33554432 117 16777216 (hp754961 rfl) rfl) (Enclosure.sfrac_true_div 65881631 33554432)

noncomputable def hp754963 := nat_lit 609553568642888642505195174945025622371413146332438577549280819505971622952846846850834917038669441

noncomputable def hp754964 := nat_lit 6686088287696359978932939563218163972212949499582522246897798068015656834493960903874669624961

noncomputable def hp754965 := nat_lit 3676307729109722872686513017529522794857781879940333753159789268875270459737241127111451252341259905

noncomputable def hp754966 := BSN.cos_dyadic_bound_t 65881631 33554432 4 3 33554432 10890000 hp754963 hp681868 hp754964 hp754965 hp681871

noncomputable def hp754967 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 65881631) (BSN.cosEvenQ 33554432) 0 3 hp754963 hp681868 hp754964 rfl rfl rfl

noncomputable def hp754968 := hp754966 hp754964 12838562 rfl rfl rfl rfl rfl rfl rfl rfl (hp754967 rfl)

noncomputable def hp754969 := @BSN.binarySplit_of_base3 (BSN.cosOddP 65881631) (BSN.cosOddQ 33554432) 0 3 hp754965 hp681871 hp754964 rfl rfl rfl

noncomputable def hp754970 := hp754962 (BSN.cos_neg_of_bound 65881631 33554432 Bool.true 12838562 33554432 1 10890000 (hp754968 (hp754969 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp754971 := hp754923 (hp754926 (@Enclosure.Real.IsNear.neg hp754925 Bool.false 33561791 33554432 15 4194304 (hp754946 rfl))) (@hp754947 12838562 33554432 1290907216 182703882240000 6419281 16777216 80681701 11418992640000 (hp754970 rfl) rfl)

noncomputable def hp754972 := @hp754898 33554432 215442567292271 562949953421312 3232126843965611 383157812047380480000 2131422654570346933059 18889465931478580854784 6424561970777840732581 hp754729 (hp754916 rfl) (@hp754919 Bool.false 215442567292271 562949953421312 3232126843965611 383157812047380480000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754733 (Enclosure.sfrac Bool.false 11 1)) (hp754920 rfl (hp754736 rfl rfl))) (hp754971 rfl))

noncomputable def hp754973 := @hp754730 hp754727 hp754729 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 831433 1000))) (@hp754735 hp754727 hp754729 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 831433 1000) 11 (hp754736 rfl rfl)) (@hp754739 hp754727 hp754729 hp754897 (hp754972 rfl) rfl rfl))

theorem hd5029 : hp754728 hp754729 := hp754973

noncomputable def hp754974 := nat_lit 1942038947872810959199447

noncomputable def hp754975 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 832719 1000)) Bool.true 25666612124073623993571 18889465931478580854784 hp754974

noncomputable def hp754976 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 832719 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 832719 1000)) Bool.true 25666612124073623993571 18889465931478580854784

noncomputable def hp754977 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 832719 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754978 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp754977 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754979 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 832719 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754980 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp754978 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp754981 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 832719 1000)) hp754980 Bool.true 25666612124073623993571 18889465931478580854784

noncomputable def hp754982 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 832719 1000) 832719 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl

noncomputable def hp754983 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp754978 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp754984 := nat_lit 6889828729500831834286772453376

noncomputable def hp754985 := @hp754983 395041281 268435456 202063 268435456 2131946718232054154013 18889465931478580854784 6488523479564910943447 hp754729 hp754984 25666612124073623993571 18889465931478580854784

noncomputable def hp754986 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) 11)

noncomputable def hp754987 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) 11) hp754986

noncomputable def hp754988 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) 11)

noncomputable def hp754989 := @hp754988 395041281 536870912 202063 536870912 395041281 536870912 202063 536870912 424172345616236544 395041281 268435456

noncomputable def hp754990 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp754991 := hp754990 BSN.quadSignNeg 9 10 11 832719 1000 190 241 536870912 268435456 9007199254740992

noncomputable def hp754992 := hp754991 Bool.false 868614947809 3794 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp754993 := hp754992 Bool.true 261939269 173465 Bool.true 554926139 Bool.true 155486804 28296951008113761 1 Bool.false 274718483

noncomputable def hp754994 := hp754993 Bool.true Bool.false 153322251 Bool.true Bool.true 395041281 202063 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 274718483 536870912) BSN.abs_quadSignNeg

noncomputable def hp754995 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp754996 := hp754995 BSN.quadSignNeg 7 8 9 832719 1000 72 134 536870912 268435456 9007199254740992

noncomputable def hp754997 := hp754996 Bool.false 868614947809 3794 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp754998 := hp754997 Bool.true 367264288 141668 Bool.true 306942567 Bool.true 677801208 28296951008113761 1 Bool.false 451491693

noncomputable def hp754999 := hp754998 Bool.false Bool.false 162904214 Bool.true Bool.true 261939269 173465 BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 451491693 536870912) BSN.abs_quadSignNeg

noncomputable def hp755000 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp755001 := hp755000 BSN.quadSignNeg 5 6 7 832719 1000 80 1 536870912 268435456 9007199254740992

noncomputable def hp755002 := hp755001 Bool.false 868614947809 3794 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp755003 := hp755002 Bool.true 421419599 105276 Bool.false 121102430 Bool.true 485392573 28296951008113761 1 Bool.false 523270139

noncomputable def hp755004 := hp755003 Bool.false Bool.false 421914851 Bool.true Bool.true 367264288 141668 BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 523270139 536870912) BSN.abs_quadSignNeg

noncomputable def hp755005 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp755006 := hp755005 BSN.quadSignPos 3 4 5 832719 1000 295 176 536870912 268435456 9007199254740992

noncomputable def hp755007 := hp755006 Bool.false 868614947809 3794 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp755008 := hp755007 Bool.true 534946932 62224 Bool.false 76702870 Bool.false 672034155 28296951008113761 1 Bool.false 76442194

noncomputable def hp755009 := hp755008 Bool.false Bool.false 168389863 Bool.false Bool.true 421419599 105276 BSN.abs_quadSignPos (BSN.cos_quad_nat3 295 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 76442194 536870912) BSN.abs_quadSignPos

noncomputable def hp755010 := hp754990 BSN.quadSignPos 1 2 3 832719 1000 662 447 536870912 268435456 9007199254740992

noncomputable def hp755011 := hp755010 Bool.false 868614947809 3794 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp755012 := hp755011 Bool.true 536870520 3850 Bool.false 460338315 Bool.false 504735377 28296951008113761 1 Bool.false 351312307

noncomputable def hp755013 := hp755012 Bool.true Bool.false 433599697 Bool.false Bool.true 534946932 62224 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 662 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 351312307 536870912) BSN.abs_quadSignPos

noncomputable def hp755014 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) 1) Bool.true

noncomputable def hp755015 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)))

noncomputable def hp755016 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000))) Bool.true 67108815 67108864

noncomputable def hp755017 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 27144217119) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false 27144217119 16777216

noncomputable def hp755018 := nat_lit 1943562449507789329031644648727515059075058415743949119429

noncomputable def hp755019 := nat_lit 1201271227748802771723286011249399537121615739145420800

noncomputable def hp755020 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) Bool.false hp755018 hp755019 11460702980793350267

noncomputable def hp755021 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 832719 4000) (Real.log (Enclosure.sfrac Bool.false 2773684731844 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1665438))))))

noncomputable def hp755022 := nat_lit 192191423730303002993551564607520000

noncomputable def hp755023 := nat_lit 960248862623844785125510812417512681280

noncomputable def hp755024 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp755021 (Enclosure.sfrac Bool.false 832719 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 832719 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp755022 hp755023)) Bool.false

noncomputable def hp755025 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 832719 1000) 832719 1000 2773684731844 16000000 1665438

noncomputable def hp755026 := hp755025 4000 2000 hp755022 hp755023 (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl rfl rfl rfl

noncomputable def hp755027 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp755021 (Enclosure.sfrac Bool.false 832719 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 832719 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp755022 hp755023) 5829176961199576048309 3602879701896396800

noncomputable def hp755028 := nat_lit 5597459854582433267611136588335243370136168237342573463955520

noncomputable def hp755029 := @hp755027 11460702980793350267 hp743892 hp755022 hp755023 0 1 hp755028 hp755018 hp755019 11460702980793350267 hp743892

noncomputable def hp755030 := @Enclosure.Real.IsNear.subLit_ff_p (hp755021 (Enclosure.sfrac Bool.false 832719 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 832719 2000) (Real.log Real.pi)) 37731892318584219463049 18014398509481984000 955363901515577 396000000000000000000

noncomputable def hp755031 := nat_lit 1955947219605378129418130554880000

noncomputable def hp755032 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 832719 4000) (Real.log (Enclosure.sfrac Bool.false 2773684731844 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1665438))))))

noncomputable def hp755033 := @hp755032 (Enclosure.sfrac Bool.false 832719 2000) 45232358274792883580297 18014398509481984000 955363901515577 396000000000000000000 832719 2000 0

noncomputable def hp755034 := nat_lit 75463784637168438926098000

noncomputable def hp755035 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 832719 4000) (Real.log (Enclosure.sfrac Bool.false 2773684731844 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1665438))))) 45239429808460346004297

noncomputable def hp755036 := nat_lit 101854215935723000902928828972092358656

noncomputable def hp755037 := @hp755035 18014398509481984000 3469667638708949 1452000000000000000000 883941708432803 2251799813685248 200000001089 8712000000000000000 hp755036 45232358274792883580297 18014398509481984000 955363901515577

noncomputable def hp755038 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 832719 4000) (Real.log (Enclosure.sfrac Bool.false 2773684731844 16000000)) 832719 4000 0 1 54327365904297063 4503599627370496

noncomputable def hp755039 := nat_lit 116667129918390675726925824

noncomputable def hp755040 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2773684731844) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp755039 hp617687

noncomputable def hp755041 := BSN.log_rat_reduce_isNear 2773684731844 16000000 17 5547369463688 4194304000000 75053595 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp755042 := nat_lit 299405923506919393858281707026036353871038403130310574528553230371159468137679836538624301771537419141120

noncomputable def hp755043 := nat_lit 1947947335809073165936405639667467585807734348968231442323949757939714218011934190548110069998148911104

noncomputable def hp755044 := nat_lit 4607865629149160175975635212021500660278837776500260467499396471568448446582295123437582451015680

noncomputable def hp755045 := BSN.log_dyadic_bound 676532731844 4870836731844 5 4 hp755042 268435456 87120000 hp755043 hp755044 75053595 5547369463688

noncomputable def hp755046 := hp755045 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp755047 := @BSN.binarySplit_of_base4 (BSN.artanhP 676532731844) (BSN.artanhQ 4870836731844) 0 4 hp755043 hp755042 hp755044 rfl rfl rfl

noncomputable def hp755048 := hp755041 rfl rfl rfl rfl (hp755046 (hp755047 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp755049 := @hp755038 12500018513 1089000000000000000 45239429808460346004297 18014398509481984000 3469667638708949 1452000000000000000000 (Enclosure.Real.IsNear.const Bool.false 832719 4000) (BSN.isNear_log_sfrac 2773684731844 16000000 54327365904297063 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp755040 1000001481040000 87120000000000000000000 54327365904297063 4503599627370496 12500018513 1089000000000000000 (hp755048 rfl rfl rfl) rfl)) rfl

noncomputable def hp755050 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1665438)))) 1 4

noncomputable def hp755051 := @hp755050 0 1 883941708432803 562949953421312 200000001089 2178000000000000000 883941708432803 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp755052 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1665438))) 884279719003555 562949953421312 1

noncomputable def hp755053 := @hp755052 2000000000000000 20147 33554432 1 10890000 29660161947572314832896 883941708432803 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp755054 := BSN.arctan_dyadic_bound_f 1000 1665438 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp755055 := hp755054 1 20147 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1665438) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1665438) 0 0 rfl)

noncomputable def hp755056 := hp755051 (hp755053 (hp755055 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp755057 := @hp755030 31985370489159 67108864000 2498157 536870912000 hp755031 5829176961199576048309 3602879701896396800 11460702980793350267 hp743892 (@hp755033 1 hp755034 37731892318584219463049 18014398509481984000 955363901515577 396000000000000000000 (@hp755037 396000000000000000000 hp755049 hp755056 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 832719 2000) rfl rfl)

noncomputable def hp755058 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 832719 2000) (Real.log Real.pi) 832719 2000 0 1 38410761 33554432

noncomputable def hp755059 := hp755057 (@hp755058 3 268435456 31985370489159 67108864000 2498157 536870912000 (Enclosure.Real.IsNear.const Bool.false 832719 2000) hd4909 rfl) rfl

noncomputable def hp755060 := @hp755020 hp743892 27144217119 16777216 475 67108864 (@hp755024 hp755018 hp755019 11460702980793350267 hp743892 (hp755026 rfl rfl rfl rfl rfl) (hp755029 (hp755059 rfl) (Enclosure.Real.IsNear.const Bool.true hp755022 hp755023) rfl rfl)) rfl

noncomputable def hp755061 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 27144217119) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2907431123045599674368) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp755062 := BSN.sin_reduce_arg_pos_rat_q2 27144217119 16777216 226375608064910080 72057594037927936 257 2907431123045599674368 hp619230 rfl rfl rfl rfl

noncomputable def hp755063 := BSN.cos_dyadic_bound_f 165268325 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp755064 := hp755063 1 67108815 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 165268325) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp755065 := hp755064 (@BSN.binarySplit_of_le (BSN.cosOddP 165268325) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp755066 := @BSN.cos_arg_round Bool.false 67108815 67108864 2907431123045599674368 hp619230 165268325 137438953472 21801270 21780000 hp755065 rfl

noncomputable def hp755067 := hp755061 67108815 67108864 257 1000000000000000 21780000 10890000 hp755062 BSN.pi_near_15 hp755066 rfl rfl

noncomputable def hp755068 := @hp755017 475 67108864 Bool.true 67108815 67108864 1 10890000 hp755060 (Enclosure.sfrac_false_div 27144217119 16777216) (hp755067 rfl rfl) rfl

noncomputable def hp755069 := @hp755014 67108815 67108864 327491179 45675970560000 536870520 536870912 3850 536870912 (@hp755015 Bool.true 67108815 67108864 327491179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000)) (@hp755016 5239858864 730815528960000 67108815 67108864 327491179 45675970560000 (hp755068 rfl) rfl))

noncomputable def hp755070 := @hp755020 hp743892 868614947809 536870912 3794 536870912 (@hp755024 hp755018 hp755019 11460702980793350267 hp743892 (hp755026 rfl rfl rfl rfl rfl) (hp755029 (hp755059 rfl) (Enclosure.Real.IsNear.const Bool.true hp755022 hp755023) rfl rfl)) rfl

noncomputable def hp755071 := hp755013 (BSN.cos_quad_nat3 447 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 433599697 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl rfl (hp755069 rfl) hp755070

noncomputable def hp755072 := nat_lit 6269558885306003015892107208289887608797911075849272009345190721891190625

noncomputable def hp755073 := nat_lit 2016587123152252768145199342818352880701498828657855797873945750390625

noncomputable def hp755074 := nat_lit 18804643481671704542140031226184026120632330229890500316439824274172790625

noncomputable def hp755075 := BSN.cos_dyadic_bound_f 460338315 536870912 3 2 536870912 268435456 hp755072 hp708868 hp755073 hp755074 hp708870

noncomputable def hp755076 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 460338315) (BSN.cosEvenQ 536870912) 0 2 hp755072 hp708868 hp755073 rfl rfl rfl

noncomputable def hp755077 := hp755075 hp755073 351312307 rfl rfl rfl rfl rfl rfl rfl rfl (hp755076 rfl)

noncomputable def hp755078 := @BSN.binarySplit_of_base2 (BSN.cosOddP 460338315) (BSN.cosOddQ 536870912) 0 2 hp755074 hp708870 hp755073 rfl rfl rfl

noncomputable def hp755079 := nat_lit 16309041876638487773169066131923501043343757415678171847112951220993560705

noncomputable def hp755080 := nat_lit 4212209513538993870830520317988965043285953163052872084297915603914881

noncomputable def hp755081 := nat_lit 42707337528174119130128114264999092027258806450226459711445056572576796801

noncomputable def hp755082 := BSN.sin_dyadic_bound_f 504735377 536870912 3 2 536870912 268435456 hp755079 hp708845 hp755080 hp755081 hp708848

noncomputable def hp755083 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 504735377) (BSN.sinEvenQ 536870912) 0 2 hp755079 hp708845 hp755080 rfl rfl rfl

noncomputable def hp755084 := hp755082 hp755080 433599697 rfl rfl rfl rfl rfl rfl rfl rfl (hp755083 rfl)

noncomputable def hp755085 := @BSN.binarySplit_of_base2 (BSN.sinOddP 504735377) (BSN.sinOddQ 536870912) 0 2 hp755081 hp708848 hp755080 rfl rfl rfl

noncomputable def hp755086 := hp755071 hd4911 hd4913 hd4915 hd4917 hd4918 (hp755077 (hp755078 rfl) rfl rfl rfl rfl) (hp755084 (hp755085 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755087 := hp755009 (BSN.cos_quad_nat0 176 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 168389863 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl rfl (hp755086 rfl rfl rfl rfl rfl) hp755070

noncomputable def hp755088 := nat_lit 34613575021619152636086921610000

noncomputable def hp755089 := BSN.sin_dyadic_bound_f 76702870 536870912 2 1 536870912 268435456 hp755088 hp708890 hp755088 hp755088 hp708891

noncomputable def hp755090 := @BSN.binarySplit_of_base (BSN.sinEvenP 76702870) (BSN.sinEvenQ 536870912) 0 1 hp755088 hp708890 hp755088 rfl rfl rfl

noncomputable def hp755091 := hp755089 hp755088 76442194 rfl rfl rfl rfl rfl rfl rfl rfl (hp755090 rfl)

noncomputable def hp755092 := @BSN.binarySplit_of_base (BSN.sinOddP 76702870) (BSN.sinOddQ 536870912) 0 1 hp755088 hp708891 hp755088 rfl rfl rfl

noncomputable def hp755093 := nat_lit 28137431878963465695434066470154294870626000799152639592713119116399187492245749987188395569545056280466803140625

noncomputable def hp755094 := nat_lit 8485865632970421471126058757475077560939430666532000615876298976171005985432789985097862027197109619140625

noncomputable def hp755095 := nat_lit 170534309214557417865801660008419744384098250021295774449517622932238249488817084608594032453341992635789068740625

noncomputable def hp755096 := BSN.cos_dyadic_bound_f 672034155 536870912 4 3 536870912 268435456 hp755093 hp716712 hp755094 hp755095 hp716714

noncomputable def hp755097 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 672034155) (BSN.cosEvenQ 536870912) 0 3 hp755093 hp716712 hp755094 rfl rfl rfl

noncomputable def hp755098 := hp755096 hp755094 168389863 rfl rfl rfl rfl rfl rfl rfl rfl (hp755097 rfl)

noncomputable def hp755099 := @BSN.binarySplit_of_base3 (BSN.cosOddP 672034155) (BSN.cosOddQ 536870912) 0 3 hp755095 hp716714 hp755094 rfl rfl rfl

noncomputable def hp755100 := hp755087 hd4920 hd4922 hd4924 hd4926 hd4918 (hp755091 (hp755092 rfl) rfl rfl rfl rfl) (hp755098 (hp755099 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755101 := hp755004 (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 421914851 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl rfl (hp755100 rfl rfl rfl rfl rfl) hp755070

noncomputable def hp755102 := nat_lit 215085647165055861819418644010000

noncomputable def hp755103 := BSN.cos_dyadic_bound_f 121102430 536870912 2 1 536870912 268435456 hp755102 hp708767 hp755102 hp755102 hp708768

noncomputable def hp755104 := @BSN.binarySplit_of_base (BSN.cosEvenP 121102430) (BSN.cosEvenQ 536870912) 0 1 hp755102 hp708767 hp755102 rfl rfl rfl

noncomputable def hp755105 := hp755103 hp755102 523270139 rfl rfl rfl rfl rfl rfl rfl rfl (hp755104 rfl)

noncomputable def hp755106 := @BSN.binarySplit_of_base (BSN.cosOddP 121102430) (BSN.cosOddQ 536870912) 0 1 hp755102 hp708768 hp755102 rfl rfl rfl

noncomputable def hp755107 := nat_lit 13948571791120513509997047632125993938143413267181627114970064873354598305

noncomputable def hp755108 := nat_lit 3081378267271102643327693469933382395818211564383725841222929591474081

noncomputable def hp755109 := nat_lit 36526984840501953598093546580426282456972852881038116411654856591828228001

noncomputable def hp755110 := BSN.sin_dyadic_bound_f 485392573 536870912 3 2 536870912 268435456 hp755107 hp708845 hp755108 hp755109 hp708848

noncomputable def hp755111 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 485392573) (BSN.sinEvenQ 536870912) 0 2 hp755107 hp708845 hp755108 rfl rfl rfl

noncomputable def hp755112 := hp755110 hp755108 421914851 rfl rfl rfl rfl rfl rfl rfl rfl (hp755111 rfl)

noncomputable def hp755113 := @BSN.binarySplit_of_base2 (BSN.sinOddP 485392573) (BSN.sinOddQ 536870912) 0 2 hp755109 hp708848 hp755108 rfl rfl rfl

noncomputable def hp755114 := hp755101 hd4928 hd4930 hd4932 hd4934 hd4918 (hp755105 (hp755106 rfl) rfl rfl rfl rfl) (hp755112 (hp755113 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755115 := hp754999 (BSN.cos_quad_nat2 134 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 162904214 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl rfl (hp755114 rfl rfl rfl rfl rfl) hp755070

noncomputable def hp755116 := nat_lit 1238924614171134214428528380062658469256656484689344076713573010607094721

noncomputable def hp755117 := nat_lit 78787435910170511518807311950215413249893518209513005859437691976641

noncomputable def hp755118 := nat_lit 3716616267641582302262547525564074976943469667031613204129000156437330881

noncomputable def hp755119 := BSN.cos_dyadic_bound_f 306942567 536870912 3 2 536870912 268435456 hp755116 hp708868 hp755117 hp755118 hp708870

noncomputable def hp755120 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 306942567) (BSN.cosEvenQ 536870912) 0 2 hp755116 hp708868 hp755117 rfl rfl rfl

noncomputable def hp755121 := hp755119 hp755117 451491693 rfl rfl rfl rfl rfl rfl rfl rfl (hp755120 rfl)

noncomputable def hp755122 := @BSN.binarySplit_of_base2 (BSN.cosOddP 306942567) (BSN.cosOddQ 536870912) 0 2 hp755118 hp708870 hp755117 rfl rfl rfl

noncomputable def hp755123 := nat_lit 29117257815988503009112566984549185547303664976685205573131759922080010056950077579378405551195221228638559010816

noncomputable def hp755124 := nat_lit 9402169195125769340937547739494031342841645799158845752515986263892982255428758875290568328321633181761536

noncomputable def hp755125 := nat_lit 176466832680608422137352454484664350474836769627993787949346394950783837242391535580538448485199401409300471480320

noncomputable def hp755126 := BSN.cos_dyadic_bound_f 677801208 536870912 4 3 536870912 268435456 hp755123 hp716712 hp755124 hp755125 hp716714

noncomputable def hp755127 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 677801208) (BSN.cosEvenQ 536870912) 0 3 hp755123 hp716712 hp755124 rfl rfl rfl

noncomputable def hp755128 := hp755126 hp755124 162904214 rfl rfl rfl rfl rfl rfl rfl rfl (hp755127 rfl)

noncomputable def hp755129 := @BSN.binarySplit_of_base3 (BSN.cosOddP 677801208) (BSN.cosOddQ 536870912) 0 3 hp755125 hp716714 hp755124 rfl rfl rfl

noncomputable def hp755130 := hp755115 hd4936 hd4938 hd4940 hd4942 hd4918 (hp755121 (hp755122 rfl) rfl rfl rfl rfl) (hp755128 (hp755129 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755131 := hp754994 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 153322251 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl rfl (hp755130 rfl rfl rfl rfl rfl) hp755070

noncomputable def hp755132 := nat_lit 13071350213370647727843786514971257404456100635190225345920389744480470106015696067362843297252270407099658392401

noncomputable def hp755133 := nat_lit 852750897917862410264966492195672726063782752401099835577632705011650975224292089211215401166779253379921

noncomputable def hp755134 := nat_lit 79263625116159350291920197347062888972520210050741343586067846714846588127707818685816935694394064219064717398865

noncomputable def hp755135 := BSN.cos_dyadic_bound_f 554926139 536870912 4 3 536870912 268435456 hp755132 hp716712 hp755133 hp755134 hp716714

noncomputable def hp755136 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 554926139) (BSN.cosEvenQ 536870912) 0 3 hp755132 hp716712 hp755133 rfl rfl rfl

noncomputable def hp755137 := hp755135 hp755133 274718483 rfl rfl rfl rfl rfl rfl rfl rfl (hp755136 rfl)

noncomputable def hp755138 := @BSN.binarySplit_of_base3 (BSN.cosOddP 554926139) (BSN.cosOddQ 536870912) 0 3 hp755134 hp716714 hp755133 rfl rfl rfl

noncomputable def hp755139 := nat_lit 584486045960615025264095443661056

noncomputable def hp755140 := BSN.sin_dyadic_bound_f 155486804 536870912 2 1 536870912 268435456 hp755139 hp708890 hp755139 hp755139 hp708891

noncomputable def hp755141 := @BSN.binarySplit_of_base (BSN.sinEvenP 155486804) (BSN.sinEvenQ 536870912) 0 1 hp755139 hp708890 hp755139 rfl rfl rfl

noncomputable def hp755142 := hp755140 hp755139 153322251 rfl rfl rfl rfl rfl rfl rfl rfl (hp755141 rfl)

noncomputable def hp755143 := @BSN.binarySplit_of_base (BSN.sinOddP 155486804) (BSN.sinOddQ 536870912) 0 1 hp755139 hp708891 hp755139 rfl rfl rfl

noncomputable def hp755144 := hp755131 hd4944 hd4946 hd4961 hd4963 hd4918 (hp755137 (hp755138 rfl) rfl rfl rfl rfl) (hp755142 (hp755143 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755145 := @hp754989 202063 268435456 (hp755144 rfl rfl rfl rfl rfl) (hp755144 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp755146 := @hp754987 Bool.true 395041281 268435456 202063 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 832719 1000)) (Enclosure.sfrac Bool.false 832719 1000) 11) hp755145

noncomputable def hp755147 := @Enclosure.Real.IsNear.mulLit_tf hp754978 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1))) 9889407 33554432 1

noncomputable def hp755148 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp754977 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755149 := @hp755148 1 1 0 1 9889407 33554432 1 33554432 9889407 33554432 1

noncomputable def hp755150 := @Enclosure.Real.IsNear.of_eq (hp754977 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755151 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 832719 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755152 := @hp755150 (@Inv.inv Real Real.instInv (Real.sqrt hp754979)) Bool.false 9889407 33554432 1 33554432 (hp755151 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 832719 1000) 832719 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000))))

noncomputable def hp755153 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp754979)) Bool.false 19778814 67108864 2 67108864 9889407 33554432

noncomputable def hp755154 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp754979) Bool.false 227698167 67108864 7 67108864 227698167 67108864 7 67108864

noncomputable def hp755155 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 832719 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755156 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 832719 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755157 := @hp755156 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 832719 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8894027652333

noncomputable def hp755158 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 832719 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 832719 1000 0

noncomputable def hp755159 := @hp755158 1 10680707 67108864 1 67108864 8894027652333 67108864000 832719 67108864000 (Enclosure.Real.IsNear.const Bool.false 832719 1000) hd4949

noncomputable def hp755160 := @hp755157 67108864000 832719 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 832719 1000) 832719 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000))) (hp755159 rfl)

noncomputable def hp755161 := @hp755155 8894027652333 67108864000 832719 67108864000 386286175 386286212 33554432 hp755160 rfl rfl rfl

noncomputable def hp755162 := @Enclosure.Real.IsNear.recentre' hp754979 Bool.false 772572387 67108864 37 67108864 772572387 67108864 37 67108864 (hp755161 rfl rfl rfl)

noncomputable def hp755163 := @Enclosure.Real.IsNear.sqrt_image hp754979 772572387 67108864 37 67108864 113849080 113849087 33554432 (hp755162 rfl) rfl rfl

noncomputable def hp755164 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp754979) 227698167 67108864 7 67108864 9889406 9889408 33554432 (hp755154 (hp755163 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp755165 := @hp755149 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp755152 (@hp755153 1 33554432 (hp755164 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp755166 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755167 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp755168 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1))) (hp755166 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755167 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp755169 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 832719 1000) 832719 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl

noncomputable def hp755170 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755171 := @hp755170 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755167 (Enclosure.sfrac Bool.false 1 16)))) 16826837

noncomputable def hp755172 := @hp755171 16777216 121 33554432 12811607 33554432 40681163 5709496320000 215578822697059 562949953421312 1306281996318743 153263124818952192000

noncomputable def hp755173 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755174 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755175 := @hp755173 (@Neg.neg Real Real.instNeg hp755174) Bool.true 16826837 16777216 121 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755176 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755177 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp755178 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp755179 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 215983759) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp755180 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1))) Bool.false 30397011880020079709065

noncomputable def hp755181 := nat_lit 199696958085981535683780903

noncomputable def hp755182 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp755183 := @Enclosure.Real.IsNear.subLit_ff_p hp754979 (Enclosure.sfrac Bool.false 11 1) 772572387 67108864 37 67108864 11 1 0

noncomputable def hp755184 := @hp755182 500000000000000 34374883 67108864 37 67108864 30397011880020079709065 9444732965739290427392 hp755181 hp645312 hd4948 (@hp755183 1 34374883 34374883 67108864 37 67108864 (hp755162 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755185 := @hp755179 215983759 67108864 117 33554432 Bool.true 66910965 67108864 1 10890000 (@hp755180 9444732965739290427392 hp755181 hp645312 215983759 67108864 117 33554432 (hp755184 rfl) rfl) (Enclosure.sfrac_false_div 215983759 67108864)

noncomputable def hp755186 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 215983759) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 742920260524620914884608) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp755187 := BSN.sin_reduce_arg_pos_rat_q2 215983759 67108864 226375608064910080 72057594037927936 0 742920260524620914884608 hp617687 rfl rfl rfl rfl

noncomputable def hp755188 := nat_lit 12423661422365308840501736214611898231361

noncomputable def hp755189 := nat_lit 8563486156235759286349715816696970818296479744

noncomputable def hp755190 := nat_lit 128452292343536389295245737250454562274447196160

noncomputable def hp755191 := BSN.cos_dyadic_bound_f 10557531887 137438953472 2 1 67108864 21801270 hp755188 hp755189 hp755188 hp755188 hp755190

noncomputable def hp755192 := @BSN.binarySplit_of_base (BSN.cosEvenP 10557531887) (BSN.cosEvenQ 137438953472) 0 1 hp755188 hp755189 hp755188 rfl rfl rfl

noncomputable def hp755193 := hp755191 hp755188 66910965 rfl rfl rfl rfl rfl rfl rfl rfl (hp755192 rfl)

noncomputable def hp755194 := @BSN.binarySplit_of_base (BSN.cosOddP 10557531887) (BSN.cosOddQ 137438953472) 0 1 hp755188 hp755190 hp755188 rfl rfl rfl

noncomputable def hp755195 := @BSN.cos_arg_round Bool.false 66910965 67108864 742920260524620914884608 hp617687 10557531887 137438953472 21801270 21780000 (hp755193 (hp755194 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755196 := hp755186 66910965 67108864 0 1000000000000000 21780000 10890000 hp755187 BSN.pi_near_15 hp755195 rfl rfl

noncomputable def hp755197 := @hp755177 66910965 67108864 81730277 22837985280000 (@hp755178 66910965 67108864 1307684432 365407764480000 66910965 67108864 81730277 22837985280000 (hp755185 (hp755196 rfl rfl) rfl rfl) rfl)

noncomputable def hp755198 := @hp755176 66910965 67108864 81730277 22837985280000 33653553 33653795 33554432 hp755197 rfl rfl rfl

noncomputable def hp755199 := @Enclosure.Real.IsNear.recentre' hp755174 Bool.false 67307348 67108864 242 67108864 16826837 16777216 121 33554432 (hp755198 rfl rfl rfl)

noncomputable def hp755200 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755167 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp755201 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755167 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65852461)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp755202 := nat_lit 1243917822649582644342889619845

noncomputable def hp755203 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755167 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp755202

noncomputable def hp755204 := nat_lit 135652812619549015082506780340552961

noncomputable def hp755205 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755167 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp755206 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp755207 := @hp755206 (Enclosure.sfrac Bool.false 1 16) 1125226766999223 4503599627370496 5026770679 4503599627370496 1 16 0

noncomputable def hp755208 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)) 1181632581263689

noncomputable def hp755209 := @hp755208 4503599627370496 2543742711 4503599627370496 34374883 67108864 37 67108864 75512690075710544412672 1125226766999223 4503599627370496 5026770679

noncomputable def hp755210 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)) 34374883 67108864 37

noncomputable def hp755211 := @hp755210 67108864 34374883 67108864 37 67108864 1181632581263689 4503599627370496 2543742711 4503599627370496 (@hp755183 1 34374883 34374883 67108864 37 67108864 (hp755162 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755212 := hp755211 (@hp755183 1 34374883 34374883 67108864 37 67108864 (hp755162 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755213 := @hp755209 4503599627370496 (hp755212 rfl) (@hp755183 1 34374883 34374883 67108864 37 67108864 (hp755162 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755214 := @hp755205 500000000000000 1406701743709879 4503599627370496 5026770679 4503599627370496 hp755202 hp627574 hp755204 hp738055 hd4948 (@hp755207 1 22507227899358064 1406701743709879 4503599627370496 5026770679 4503599627370496 (hp755213 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp755215 := @hp755201 65852461 33554432 59 8388608 Bool.true 12811607 33554432 1 10890000 (@hp755203 hp627574 hp755204 hp738055 65852461 33554432 59 8388608 (hp755214 rfl) rfl) (Enclosure.sfrac_true_div 65852461 33554432)

noncomputable def hp755216 := nat_lit 608465265945195715087599986231328805234068426080867643286617307288899372034519846645202288815978801

noncomputable def hp755217 := nat_lit 6650650376217100874040494108154729672199293344820142958429554775425278760261516367136017955121

noncomputable def hp755218 := nat_lit 3669781989184869947716501386409833202707888649353121720041720276558521920249450569571941334218783025

noncomputable def hp755219 := BSN.cos_dyadic_bound_t 65852461 33554432 4 3 33554432 10890000 hp755216 hp681868 hp755217 hp755218 hp681871

noncomputable def hp755220 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 65852461) (BSN.cosEvenQ 33554432) 0 3 hp755216 hp681868 hp755217 rfl rfl rfl

noncomputable def hp755221 := hp755219 hp755217 12811607 rfl rfl rfl rfl rfl rfl rfl rfl (hp755220 rfl)

noncomputable def hp755222 := @BSN.binarySplit_of_base3 (BSN.cosOddP 65852461) (BSN.cosOddQ 33554432) 0 3 hp755218 hp681871 hp755217 rfl rfl rfl

noncomputable def hp755223 := hp755215 (BSN.cos_neg_of_bound 65852461 33554432 Bool.true 12811607 33554432 1 10890000 (hp755221 (hp755222 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp755224 := hp755172 (hp755175 (@Enclosure.Real.IsNear.neg hp755174 Bool.false 16826837 16777216 121 33554432 (hp755199 rfl))) (@hp755200 12811607 33554432 650898608 91351941120000 12811607 33554432 40681163 5709496320000 (hp755223 rfl) rfl)

noncomputable def hp755225 := @hp755147 33554432 215578822697059 562949953421312 1306281996318743 153263124818952192000 2131946718232054154013 18889465931478580854784 6488523479564910943447 hp754729 (hp755165 rfl) (@hp755168 Bool.false 215578822697059 562949953421312 1306281996318743 153263124818952192000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754979 (Enclosure.sfrac Bool.false 11 1)) (hp755169 rfl (hp754982 rfl rfl))) (hp755224 rfl))

noncomputable def hp755226 := @hp754976 hp754974 hp754729 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 832719 1000))) (@hp754981 hp754974 hp754729 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 832719 1000) 11 (hp754982 rfl rfl)) (@hp754985 hp754974 hp754729 hp755146 (hp755225 rfl) rfl rfl))

theorem hd5030 : hp754975 hp754729 := hp755226

noncomputable def hp755227 := nat_lit 77804606614532358781230799

noncomputable def hp755228 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 834004 1000)) Bool.false 664356483192670713703121 151115727451828646838272 hp755227

noncomputable def hp755229 := nat_lit 102853141996900872754298880000

noncomputable def hp755230 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 834004 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 834004 1000)) Bool.false 664356483192670713703121 151115727451828646838272

noncomputable def hp755231 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 834004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755232 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp755231 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755233 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 834004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755234 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp755232 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp755235 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 834004 1000)) hp755234 Bool.false 664356483192670713703121 151115727451828646838272

noncomputable def hp755236 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 834004 1000) 834004 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl

noncomputable def hp755237 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp755232 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp755238 := nat_lit 178336835512380898890742734258176

noncomputable def hp755239 := @hp755237 1149808111 268435456 202377 268435456 17072060661773975841489 151115727451828646838272 262278085819639380270799 hp755229 hp755238 664356483192670713703121 151115727451828646838272

noncomputable def hp755240 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) 11)

noncomputable def hp755241 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) 11) hp755240

noncomputable def hp755242 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) 11)

noncomputable def hp755243 := @hp755242 1149808111 536870912 202377 536870912 1149808111 536870912 202377 536870912 1234597058355134464 1149808111 268435456

noncomputable def hp755244 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp755245 := hp755244 BSN.quadSignNeg 9 10 11 834004 1000 190 241 536870912 268435456 9007199254740992

noncomputable def hp755246 := hp755245 Bool.false 870300871131 3800 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp755247 := hp755246 Bool.false 1298581469 173735 Bool.true 457508195 Bool.true 123821365 28296951008113761 1 Bool.false 353447480

noncomputable def hp755248 := hp755247 Bool.true Bool.false 122726550 Bool.true Bool.false 1149808111 202377 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 353447480 536870912) BSN.abs_quadSignNeg

noncomputable def hp755249 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp755250 := hp755249 BSN.quadSignNeg 7 8 9 834004 1000 72 134 536870912 268435456 9007199254740992

noncomputable def hp755251 := hp755250 Bool.false 870300871131 3800 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp755252 := hp755251 Bool.false 1214512335 141889 Bool.true 55582549 Bool.true 507697229 28296951008113761 1 Bool.false 533996234

noncomputable def hp755253 := hp755252 Bool.false Bool.false 314181153 Bool.true Bool.false 1298581469 173735 BSN.abs_quadSignPos (BSN.cos_quad_nat0 72 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 533996234 536870912) BSN.abs_quadSignNeg

noncomputable def hp755254 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp755255 := hp755254 BSN.quadSignNeg 5 6 7 834004 1000 80 1 536870912 268435456 9007199254740992

noncomputable def hp755256 := hp755255 Bool.false 870300871131 3800 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp755257 := hp755256 Bool.false 1161036014 105441 Bool.false 570928312 Bool.true 141912016 28296951008113761 1 Bool.false 260850030

noncomputable def hp755258 := hp755257 Bool.false Bool.false 140265184 Bool.true Bool.false 1214512335 141889 BSN.abs_quadSignPos (BSN.cos_quad_nat0 80 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 260850030 536870912) BSN.abs_quadSignNeg

noncomputable def hp755259 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp755260 := hp755259 BSN.quadSignNeg 3 4 5 834004 1000 295 177 536870912 268435456 9007199254740992

noncomputable def hp755261 := hp755260 Bool.false 870300871131 3800 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp755262 := hp755261 Bool.false 1057445008 62322 Bool.false 806250673 Bool.false 404325027 28296951008113761 1 Bool.false 535592012

noncomputable def hp755263 := hp755262 Bool.false Bool.false 367173515 Bool.true Bool.false 1161036014 105441 BSN.abs_quadSignPos (BSN.cos_quad_nat3 295 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535592012 536870912) BSN.abs_quadSignNeg

noncomputable def hp755264 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp755265 := hp755264 BSN.quadSignPos 1 2 3 834004 1000 663 448 536870912 268435456 9007199254740992

noncomputable def hp755266 := hp755265 Bool.false 870300871131 3800 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp755267 := hp755266 Bool.false 536870904 3858 Bool.false 824759031 Bool.false 589434168 28296951008113761 1 Bool.false 536550272

noncomputable def hp755268 := hp755267 Bool.false Bool.false 244523599 Bool.false Bool.false 1057445008 62322 BSN.abs_quadSignPos (BSN.cos_quad_nat3 663 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536550272 536870912) BSN.abs_quadSignPos

noncomputable def hp755269 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) 1) Bool.false

noncomputable def hp755270 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)))

noncomputable def hp755271 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000))) Bool.false 67108863 67108864

noncomputable def hp755272 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 108787608891) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 108787608891 67108864

noncomputable def hp755273 := nat_lit 674778385385475246549694604394945492931713542084217851

noncomputable def hp755274 := nat_lit 416257066006009289127097778673965351353668599808000

noncomputable def hp755275 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) Bool.false hp755273 hp755274 3507267793841836347

noncomputable def hp755276 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 834004 4000) (Real.log (Enclosure.sfrac Bool.false 2782251688064 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1668008))))))

noncomputable def hp755277 := nat_lit 193678895919915040128263066091520000

noncomputable def hp755278 := nat_lit 969174006036504379303887902465568276480

noncomputable def hp755279 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp755276 (Enclosure.sfrac Bool.false 834004 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 834004 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp755277 hp755278)) Bool.false

noncomputable def hp755280 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 834004 1000) 834004 1000 2782251688064 16000000 1668008

noncomputable def hp755281 := hp755280 4000 2000 hp755277 hp755278 (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl rfl rfl rfl

noncomputable def hp755282 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp755276 (Enclosure.sfrac Bool.false 834004 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 834004 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp755277 hp755278) 7300613749978453345187 4503599627370496000

noncomputable def hp755283 := nat_lit 7075564202339600921260925694980343651963644591045008173301760

noncomputable def hp755284 := @hp755282 3507267793841836347 495616000000000000000000 hp755277 hp755278 0 1 hp755283 hp755273 hp755274 3507267793841836347 495616000000000000000000

noncomputable def hp755285 := @Enclosure.Real.IsNear.subLit_ff_p (hp755276 (Enclosure.sfrac Bool.false 834004 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 834004 2000) (Real.log Real.pi)) 9450427975883908023203 4503599627370496000 146181464450841 60500000000000000000

noncomputable def hp755286 := nat_lit 122483973815958507118124859392000

noncomputable def hp755287 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 834004 4000) (Real.log (Enclosure.sfrac Bool.false 2782251688064 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1668008))))))

noncomputable def hp755288 := @hp755287 (Enclosure.sfrac Bool.false 834004 2000) 2265687605539331919239 900719925474099200 146181464450841 60500000000000000000 834004 2000 0

noncomputable def hp755289 := nat_lit 3780171190353563209281200

noncomputable def hp755290 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 834004 4000) (Real.log (Enclosure.sfrac Bool.false 2782251688064 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1668008))))) 2266041182430742518839

noncomputable def hp755291 := nat_lit 5101874928022443280207927421301686272

noncomputable def hp755292 := @hp755290 900719925474099200 2606266359979013 1089000000000000000000 883942228526499 2251799813685248 200000001089 8712000000000000000 hp755291 2265687605539331919239 900719925474099200 146181464450841

noncomputable def hp755293 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 834004 4000) (Real.log (Enclosure.sfrac Bool.false 2782251688064 16000000)) 834004 4000 0 1 54341254536686695 4503599627370496

noncomputable def hp755294 := nat_lit 116696955529340493611663360

noncomputable def hp755295 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2782251688064) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp755294 hp617687

noncomputable def hp755296 := BSN.log_rat_reduce_isNear 2782251688064 16000000 17 5564503376128 4194304000000 75881422 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp755297 := nat_lit 303644772960479419903835688353581374648263813493191216829857227018813017902019223592885859952231364689920

noncomputable def hp755298 := nat_lit 2019286916633825355960592666827926625562066402900847267343162758539787697048484065574515500576422232064

noncomputable def hp755299 := nat_lit 5095883107173458606775836165862577177791067894619882631724110707087105837062912768688419378298880

noncomputable def hp755300 := BSN.log_dyadic_bound 685099688064 4879403688064 5 4 hp755297 268435456 87120000 hp755298 hp755299 75881422 5564503376128

noncomputable def hp755301 := hp755300 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp755302 := @BSN.binarySplit_of_base4 (BSN.artanhP 685099688064) (BSN.artanhQ 4879403688064) 0 4 hp755298 hp755297 hp755299 rfl rfl rfl

noncomputable def hp755303 := hp755296 rfl rfl rfl rfl (hp755301 (hp755302 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp755304 := @hp755293 12500018513 1089000000000000000 2266041182430742518839 900719925474099200 2606266359979013 1089000000000000000000 (Enclosure.Real.IsNear.const Bool.false 834004 4000) (BSN.isNear_log_sfrac 2782251688064 16000000 54341254536686695 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp755295 1000001481040000 87120000000000000000000 54341254536686695 4503599627370496 12500018513 1089000000000000000 (hp755303 rfl rfl rfl) rfl)) rfl

noncomputable def hp755305 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1668008)))) 1 4

noncomputable def hp755306 := @hp755305 0 1 883942228526499 562949953421312 200000001089 2178000000000000000 883942228526499 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp755307 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1668008))) 884279719003555 562949953421312 1

noncomputable def hp755308 := @hp755307 2000000000000000 20116 33554432 1 10890000 29660179399020870893568 883942228526499 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp755309 := BSN.arctan_dyadic_bound_f 1000 1668008 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp755310 := hp755309 1 20116 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1668008) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1668008) 0 0 rfl)

noncomputable def hp755311 := hp755306 (hp755308 (hp755310 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp755312 := @hp755285 8008682079261 16777216000 625503 134217728000 hp755286 7300613749978453345187 4503599627370496000 3507267793841836347 495616000000000000000000 (@hp755288 1 hp755289 9450427975883908023203 4503599627370496000 146181464450841 60500000000000000000 (@hp755292 60500000000000000000 hp755304 hp755311 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 834004 2000) rfl rfl)

noncomputable def hp755313 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 834004 2000) (Real.log Real.pi) 834004 2000 0 1 38410761 33554432

noncomputable def hp755314 := hp755312 (@hp755313 3 268435456 8008682079261 16777216000 625503 134217728000 (Enclosure.Real.IsNear.const Bool.false 834004 2000) hd4909 rfl) rfl

noncomputable def hp755315 := @hp755275 495616000000000000000000 108787608891 67108864 119 16777216 (@hp755279 hp755273 hp755274 3507267793841836347 495616000000000000000000 (hp755281 rfl rfl rfl rfl rfl) (hp755284 (hp755314 rfl) (Enclosure.Real.IsNear.const Bool.true hp755277 hp755278) rfl rfl)) rfl

noncomputable def hp755316 := nat_lit 15190714372855746613215232

noncomputable def hp755317 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 108787608891) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp755316) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp755318 := BSN.sin_reduce_arg_pos_rat_q3 108787608891 67108864 226375608064910080 72057594037927936 257 hp755316 hp617687 rfl rfl rfl rfl

noncomputable def hp755319 := nat_lit 14376226230698479803739697696256687073731992872084549798857522165773063121755937807632653248938570497141800461742172152886571623650614801596416

noncomputable def hp755320 := nat_lit 10241905587533589696654099353159799199985375541722764888125024657435635563906062517292576428742802957629216818780937347554880106230972416

noncomputable def hp755321 := nat_lit 71791835700060209285086769452961410688949708289904477144381557865450088323082630143791104815732183506615590790158763861916638084383835240267776

noncomputable def hp755322 := BSN.sin_dyadic_bound_f 215873034972 137438953472 4 3 67108864 21801270 hp755319 hp737934 hp755320 hp755321 hp737937

noncomputable def hp755323 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215873034972) (BSN.sinEvenQ 137438953472) 0 3 hp755319 hp737934 hp755320 rfl rfl rfl

noncomputable def hp755324 := hp755322 hp755320 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (hp755323 rfl)

noncomputable def hp755325 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215873034972) (BSN.sinOddQ 137438953472) 0 3 hp755321 hp737937 hp755320 rfl rfl rfl

noncomputable def hp755326 := @BSN.sin_arg_round Bool.false 67108863 67108864 hp755316 hp617687 215873034972 137438953472 21801270 21780000 (hp755324 (hp755325 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755327 := hp755317 67108863 67108864 257 1000000000000000 21780000 10890000 hp755318 BSN.pi_near_15 hp755326 rfl rfl

noncomputable def hp755328 := @hp755272 119 16777216 Bool.false 67108863 67108864 1 10890000 hp755315 (Enclosure.sfrac_false_div 108787608891 67108864) (hp755327 rfl rfl) rfl

noncomputable def hp755329 := @hp755269 67108863 67108864 82042951 11418992640000 536870904 536870912 3858 536870912 (@hp755270 Bool.false 67108863 67108864 82042951 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000)) (@hp755271 1312687216 182703882240000 67108863 67108864 82042951 11418992640000 (hp755328 rfl) rfl))

noncomputable def hp755330 := @hp755275 495616000000000000000000 870300871131 536870912 3800 536870912 (@hp755279 hp755273 hp755274 3507267793841836347 495616000000000000000000 (hp755281 rfl rfl rfl rfl rfl) (hp755284 (hp755314 rfl) (Enclosure.Real.IsNear.const Bool.true hp755277 hp755278) rfl rfl)) rfl

noncomputable def hp755331 := hp755268 (BSN.cos_quad_nat0 448 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 244523599 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl rfl (hp755329 rfl) hp755330

noncomputable def hp755332 := nat_lit 166022060134157049850271661681917044080906334287171427371995378398427699517036394442515093336564849997360360027361

noncomputable def hp755333 := nat_lit 99066074985238522032802277302881951358727526062513987384156790016626697644321077572480185511421878063297761

noncomputable def hp755334 := nat_lit 829166496199257185544940773883498005442612816052997926604040883823243330411308282413984459299339605116429872362721

noncomputable def hp755335 := BSN.sin_dyadic_bound_f 824759031 536870912 4 3 536870912 268435456 hp755332 hp642702 hp755333 hp755334 hp642705

noncomputable def hp755336 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 824759031) (BSN.sinEvenQ 536870912) 0 3 hp755332 hp642702 hp755333 rfl rfl rfl

noncomputable def hp755337 := hp755335 hp755333 536550272 rfl rfl rfl rfl rfl rfl rfl rfl (hp755336 rfl)

noncomputable def hp755338 := @BSN.binarySplit_of_base3 (BSN.sinOddP 824759031) (BSN.sinOddQ 536870912) 0 3 hp755334 hp642705 hp755333 rfl rfl rfl

noncomputable def hp755339 := nat_lit 16641843684855321352136918920457816437951962203965328478208459945641299115144125663839448777247821783395630841856

noncomputable def hp755340 := nat_lit 1758829277519667375373678821680216744143896937154948919689278154431843818252485108601356556809546577739776

noncomputable def hp755341 := nat_lit 100902347719625084980557418430894231985970267385506571850007301291162377984896087789539305314256578042945286963200

noncomputable def hp755342 := BSN.cos_dyadic_bound_f 589434168 536870912 4 3 536870912 268435456 hp755339 hp716712 hp755340 hp755341 hp716714

noncomputable def hp755343 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 589434168) (BSN.cosEvenQ 536870912) 0 3 hp755339 hp716712 hp755340 rfl rfl rfl

noncomputable def hp755344 := hp755342 hp755340 244523599 rfl rfl rfl rfl rfl rfl rfl rfl (hp755343 rfl)

noncomputable def hp755345 := @BSN.binarySplit_of_base3 (BSN.cosOddP 589434168) (BSN.cosOddQ 536870912) 0 3 hp755341 hp716714 hp755340 rfl rfl rfl

noncomputable def hp755346 := hp755331 hd4911 hd4913 hd4915 hd4917 hd4918 (hp755337 (hp755338 rfl) rfl rfl rfl rfl) (hp755344 (hp755345 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755347 := hp755263 (BSN.cos_quad_nat1 177 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 367173515 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl rfl (hp755346 rfl rfl rfl rfl rfl) hp755330

noncomputable def hp755348 := nat_lit 151589283153969239509731700998668956017624012557260701382568417497927466727900832370043141148902875145551898630721

noncomputable def hp755349 := nat_lit 75446844750177775013764862729063398005426992906959490305538245903331479268955507644922011147179555134265921

noncomputable def hp755350 := nat_lit 757159351333838742655428245721025701095320436453711967476583381521916907019541040418310365518799371511286160841281

noncomputable def hp755351 := BSN.sin_dyadic_bound_f 806250673 536870912 4 3 536870912 268435456 hp755348 hp642702 hp755349 hp755350 hp642705

noncomputable def hp755352 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 806250673) (BSN.sinEvenQ 536870912) 0 3 hp755348 hp642702 hp755349 rfl rfl rfl

noncomputable def hp755353 := hp755351 hp755349 535592012 rfl rfl rfl rfl rfl rfl rfl rfl (hp755352 rfl)

noncomputable def hp755354 := @BSN.binarySplit_of_base3 (BSN.sinOddP 806250673) (BSN.sinOddQ 536870912) 0 3 hp755350 hp642705 hp755349 rfl rfl rfl

noncomputable def hp755355 := nat_lit 6714752021921945024215054676347839524497220156680969798348636074633785505

noncomputable def hp755356 := nat_lit 714241357103547940151776788578303680153292059359256414021170353336481

noncomputable def hp755357 := nat_lit 17585098904741212176279183180396167215343899842258815437671345919659274401

noncomputable def hp755358 := BSN.sin_dyadic_bound_f 404325027 536870912 3 2 536870912 268435456 hp755355 hp708845 hp755356 hp755357 hp708848

noncomputable def hp755359 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 404325027) (BSN.sinEvenQ 536870912) 0 2 hp755355 hp708845 hp755356 rfl rfl rfl

noncomputable def hp755360 := hp755358 hp755356 367173515 rfl rfl rfl rfl rfl rfl rfl rfl (hp755359 rfl)

noncomputable def hp755361 := @BSN.binarySplit_of_base2 (BSN.sinOddP 404325027) (BSN.sinOddQ 536870912) 0 2 hp755357 hp708848 hp755356 rfl rfl rfl

noncomputable def hp755362 := hp755347 hd4920 hd4922 hd4924 hd4926 hd4918 (hp755353 (hp755354 rfl) rfl rfl rfl rfl) (hp755360 (hp755361 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755363 := hp755258 (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 140265184 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl rfl (hp755362 rfl rfl rfl rfl rfl) hp755330

noncomputable def hp755364 := nat_lit 14646759836140969244207647759499920847120774428167448352851453705708678653288097103860371233399166557805384564736

noncomputable def hp755365 := nat_lit 1199441191462748379561135295354988935587005512911254845171086660123525302653885097847708873077448094253056

noncomputable def hp755366 := nat_lit 88811941907916731347847119308245495141059280073972051315712637546331849126999145599311661827165736897411505192960

noncomputable def hp755367 := BSN.cos_dyadic_bound_f 570928312 536870912 4 3 536870912 268435456 hp755364 hp716712 hp755365 hp755366 hp716714

noncomputable def hp755368 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 570928312) (BSN.cosEvenQ 536870912) 0 3 hp755364 hp716712 hp755365 rfl rfl rfl

noncomputable def hp755369 := hp755367 hp755365 260850030 rfl rfl rfl rfl rfl rfl rfl rfl (hp755368 rfl)

noncomputable def hp755370 := @BSN.binarySplit_of_base3 (BSN.cosOddP 570928312) (BSN.cosOddQ 536870912) 0 3 hp755366 hp716714 hp755365 rfl rfl rfl

noncomputable def hp755371 := nat_lit 405580138047062951868299870273536

noncomputable def hp755372 := BSN.sin_dyadic_bound_f 141912016 536870912 2 1 536870912 268435456 hp755371 hp708890 hp755371 hp755371 hp708891

noncomputable def hp755373 := @BSN.binarySplit_of_base (BSN.sinEvenP 141912016) (BSN.sinEvenQ 536870912) 0 1 hp755371 hp708890 hp755371 rfl rfl rfl

noncomputable def hp755374 := hp755372 hp755371 140265184 rfl rfl rfl rfl rfl rfl rfl rfl (hp755373 rfl)

noncomputable def hp755375 := @BSN.binarySplit_of_base (BSN.sinOddP 141912016) (BSN.sinOddQ 536870912) 0 1 hp755371 hp708891 hp755371 rfl rfl rfl

noncomputable def hp755376 := hp755363 hd4928 hd4930 hd4932 hd4934 hd4918 (hp755369 (hp755370 rfl) rfl rfl rfl rfl) (hp755374 (hp755375 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755377 := hp755253 (BSN.cos_quad_nat2 134 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 314181153 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl rfl (hp755376 rfl rfl rfl rfl rfl) hp755330

noncomputable def hp755378 := nat_lit 9544514412311327637277745434801

noncomputable def hp755379 := BSN.cos_dyadic_bound_f 55582549 536870912 2 1 536870912 268435456 hp755378 hp708767 hp755378 hp755378 hp708768

noncomputable def hp755380 := @BSN.binarySplit_of_base (BSN.cosEvenP 55582549) (BSN.cosEvenQ 536870912) 0 1 hp755378 hp708767 hp755378 rfl rfl rfl

noncomputable def hp755381 := hp755379 hp755378 533996234 rfl rfl rfl rfl rfl rfl rfl rfl (hp755380 rfl)

noncomputable def hp755382 := @BSN.binarySplit_of_base (BSN.cosOddP 55582549) (BSN.cosOddQ 536870912) 0 1 hp755378 hp708768 hp755378 rfl rfl rfl

noncomputable def hp755383 := nat_lit 9156101294026805274754370614425163282571564864098363358987621353499797292206519274923386259753246655036814905521

noncomputable def hp755384 := nat_lit 293263164444927707425202243146487587264946128954055686697017633322802188757011399916770877729502814654641

noncomputable def hp755385 := nat_lit 55529393548422353703791692261356350533613786556682716661622984646637859519588996687299940422127002403607111651505

noncomputable def hp755386 := BSN.cos_dyadic_bound_f 507697229 536870912 4 3 536870912 268435456 hp755383 hp716712 hp755384 hp755385 hp716714

noncomputable def hp755387 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 507697229) (BSN.cosEvenQ 536870912) 0 3 hp755383 hp716712 hp755384 rfl rfl rfl

noncomputable def hp755388 := hp755386 hp755384 314181153 rfl rfl rfl rfl rfl rfl rfl rfl (hp755387 rfl)

noncomputable def hp755389 := @BSN.binarySplit_of_base3 (BSN.cosOddP 507697229) (BSN.cosOddQ 536870912) 0 3 hp755385 hp716714 hp755384 rfl rfl rfl

noncomputable def hp755390 := hp755377 hd4936 hd4938 hd4940 hd4942 hd4918 (hp755381 (hp755382 rfl) rfl rfl rfl rfl) (hp755388 (hp755389 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755391 := hp755248 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 122726550 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl rfl (hp755390 rfl rfl rfl rfl rfl) hp755330

noncomputable def hp755392 := nat_lit 6116748130083299940040515775350955399066835968062631898447146169000190625

noncomputable def hp755393 := nat_lit 1919512838914206660297260846363543883639486481972251310521574875390625

noncomputable def hp755394 := nat_lit 18346405364572071406800952804360139109433228931223951192720395357249790625

noncomputable def hp755395 := BSN.cos_dyadic_bound_f 457508195 536870912 3 2 536870912 268435456 hp755392 hp708868 hp755393 hp755394 hp708870

noncomputable def hp755396 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 457508195) (BSN.cosEvenQ 536870912) 0 2 hp755392 hp708868 hp755393 rfl rfl rfl

noncomputable def hp755397 := hp755395 hp755393 353447480 rfl rfl rfl rfl rfl rfl rfl rfl (hp755396 rfl)

noncomputable def hp755398 := @BSN.binarySplit_of_base2 (BSN.cosOddP 457508195) (BSN.cosOddQ 536870912) 0 2 hp755394 hp708870 hp755393 rfl rfl rfl

noncomputable def hp755399 := nat_lit 235061957992392066557088077400625

noncomputable def hp755400 := BSN.sin_dyadic_bound_f 123821365 536870912 2 1 536870912 268435456 hp755399 hp708890 hp755399 hp755399 hp708891

noncomputable def hp755401 := @BSN.binarySplit_of_base (BSN.sinEvenP 123821365) (BSN.sinEvenQ 536870912) 0 1 hp755399 hp708890 hp755399 rfl rfl rfl

noncomputable def hp755402 := hp755400 hp755399 122726550 rfl rfl rfl rfl rfl rfl rfl rfl (hp755401 rfl)

noncomputable def hp755403 := @BSN.binarySplit_of_base (BSN.sinOddP 123821365) (BSN.sinOddQ 536870912) 0 1 hp755399 hp708891 hp755399 rfl rfl rfl

noncomputable def hp755404 := hp755391 hd4944 hd4946 hd4961 hd4963 hd4918 (hp755397 (hp755398 rfl) rfl rfl rfl rfl) (hp755402 (hp755403 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755405 := @hp755243 202377 268435456 (hp755404 rfl rfl rfl rfl rfl) (hp755404 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp755406 := @hp755241 Bool.false 1149808111 268435456 202377 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 834004 1000)) (Enclosure.sfrac Bool.false 834004 1000) 11) hp755405

noncomputable def hp755407 := @Enclosure.Real.IsNear.mulLit_tf hp755232 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1))) 19771191 67108864 1

noncomputable def hp755408 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp755231 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755409 := @hp755408 1 1 0 1 19771191 67108864 1 67108864 19771191 67108864 1

noncomputable def hp755410 := @Enclosure.Real.IsNear.of_eq (hp755231 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755411 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 834004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755412 := @hp755410 (@Inv.inv Real Real.instInv (Real.sqrt hp755233)) Bool.false 19771191 67108864 1 67108864 (hp755411 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 834004 1000) 834004 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000))))

noncomputable def hp755413 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp755233)) Bool.false 19771191 67108864 1 67108864 19771191 67108864

noncomputable def hp755414 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp755233) Bool.false 227785958 67108864 6 67108864 113892979 33554432 3 33554432

noncomputable def hp755415 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 834004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755416 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 834004 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755417 := @hp755416 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 834004 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2226938090207

noncomputable def hp755418 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 834004 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 834004 1000 0

noncomputable def hp755419 := @hp755418 1 10680707 67108864 1 67108864 2226938090207 16777216000 208501 16777216000 (Enclosure.Real.IsNear.const Bool.false 834004 1000) hd4949

noncomputable def hp755420 := @hp755417 16777216000 208501 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 834004 1000) 834004 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000))) (hp755419 rfl)

noncomputable def hp755421 := @hp755415 2226938090207 16777216000 208501 16777216000 386584106 386584143 33554432 hp755420 rfl rfl rfl

noncomputable def hp755422 := @Enclosure.Real.IsNear.recentre' hp755233 Bool.false 773168249 67108864 37 67108864 773168249 67108864 37 67108864 (hp755421 rfl rfl rfl)

noncomputable def hp755423 := @Enclosure.Real.IsNear.sqrt_image hp755233 773168249 67108864 37 67108864 113892976 113892982 33554432 (hp755422 rfl) rfl rfl

noncomputable def hp755424 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp755233) 113892979 33554432 3 33554432 9885595 9885596 33554432 (hp755414 (hp755423 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp755425 := @hp755409 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp755412 (@hp755413 1 67108864 (hp755424 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp755426 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755427 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp755428 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1))) (hp755426 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755427 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp755429 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 834004 1000) 834004 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl

noncomputable def hp755430 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755431 := @hp755430 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755427 (Enclosure.sfrac Bool.false 1 16)))) 67703241

noncomputable def hp755432 := @hp755431 67108864 245 67108864 12753919 33554432 82042951 11418992640000 863481651751479 2251799813685248 13235943418101247 1532631248189521920000

noncomputable def hp755433 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755434 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755435 := @hp755433 (@Neg.neg Real Real.instNeg hp755434) Bool.true 67703241 67108864 245 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755436 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755437 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp755438 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp755439 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 219727671) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp755440 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1))) Bool.false 30923920561944975998475

noncomputable def hp755441 := nat_lit 998484790435026094024762819

noncomputable def hp755442 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp755443 := @Enclosure.Real.IsNear.subLit_ff_p hp755233 (Enclosure.sfrac Bool.false 11 1) 773168249 67108864 37 67108864 11 1 0

noncomputable def hp755444 := @hp755442 500000000000000 34970745 67108864 37 67108864 30923920561944975998475 9444732965739290427392 hp755441 hp738031 hd4948 (@hp755443 1 34970745 34970745 67108864 37 67108864 (hp755422 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755445 := @hp755439 219727671 67108864 233 67108864 Bool.true 66519705 67108864 1 10890000 (@hp755440 9444732965739290427392 hp755441 hp738031 219727671 67108864 233 67108864 (hp755444 rfl) rfl) (Enclosure.sfrac_false_div 219727671 67108864)

noncomputable def hp755446 := nat_lit 1282474842544074624335872

noncomputable def hp755447 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 219727671) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp755446) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp755448 := BSN.sin_reduce_arg_pos_rat_q2 219727671 67108864 226375608064910080 72057594037927936 0 hp755446 hp617687 rfl rfl rfl rfl

noncomputable def hp755449 := nat_lit 110325579217879788443443840472681117149761

noncomputable def hp755450 := BSN.cos_dyadic_bound_f 18225063663 137438953472 2 1 67108864 21801270 hp755449 hp755189 hp755449 hp755449 hp755190

noncomputable def hp755451 := @BSN.binarySplit_of_base (BSN.cosEvenP 18225063663) (BSN.cosEvenQ 137438953472) 0 1 hp755449 hp755189 hp755449 rfl rfl rfl

noncomputable def hp755452 := hp755450 hp755449 66519705 rfl rfl rfl rfl rfl rfl rfl rfl (hp755451 rfl)

noncomputable def hp755453 := @BSN.binarySplit_of_base (BSN.cosOddP 18225063663) (BSN.cosOddQ 137438953472) 0 1 hp755449 hp755190 hp755449 rfl rfl rfl

noncomputable def hp755454 := @BSN.cos_arg_round Bool.false 66519705 67108864 hp755446 hp617687 18225063663 137438953472 21801270 21780000 (hp755452 (hp755453 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755455 := hp755447 66519705 67108864 0 1000000000000000 21780000 10890000 hp755448 BSN.pi_near_15 hp755454 rfl rfl

noncomputable def hp755456 := @hp755437 66519705 67108864 162779929 45675970560000 (@hp755438 66519705 67108864 2604478864 730815528960000 66519705 67108864 162779929 45675970560000 (hp755445 (hp755455 rfl rfl) rfl rfl) rfl)

noncomputable def hp755457 := @hp755436 66519705 67108864 162779929 45675970560000 33851498 33851743 33554432 hp755456 rfl rfl rfl

noncomputable def hp755458 := @Enclosure.Real.IsNear.recentre' hp755434 Bool.false 67703241 67108864 245 67108864 67703241 67108864 245 67108864 (hp755457 rfl rfl rfl)

noncomputable def hp755459 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755427 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp755460 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755427 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 16447517)) (@Nat.cast Real Real.instNatCast 8388608)) Bool.true

noncomputable def hp755461 := nat_lit 1242739252278565585619003750605

noncomputable def hp755462 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755427 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp755461

noncomputable def hp755463 := nat_lit 136842730907575967817705142232141701

noncomputable def hp755464 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755427 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp755465 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp755466 := @hp755465 (Enclosure.sfrac Bool.false 1 16) 1123893964328655 4503599627370496 5070864467 4503599627370496 1 16 0

noncomputable def hp755467 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)) 1222953005855025

noncomputable def hp755468 := @hp755467 4503599627370496 2587836499 4503599627370496 34970745 67108864 37 67108864 75423247202552559697920 1123893964328655 4503599627370496 5070864467

noncomputable def hp755469 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)) 34970745 67108864 37

noncomputable def hp755470 := @hp755469 67108864 34970745 67108864 37 67108864 1222953005855025 4503599627370496 2587836499 4503599627370496 (@hp755443 1 34970745 34970745 67108864 37 67108864 (hp755422 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755471 := hp755470 (@hp755443 1 34970745 34970745 67108864 37 67108864 (hp755422 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755472 := @hp755468 4503599627370496 (hp755471 rfl) (@hp755443 1 34970745 34970745 67108864 37 67108864 (hp755422 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755473 := @hp755464 500000000000000 1405368941039311 4503599627370496 5070864467 4503599627370496 hp755461 hp627574 hp755463 hp738055 hd4948 (@hp755466 1 22485903056628976 1405368941039311 4503599627370496 5070864467 4503599627370496 (hp755472 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp755474 := @hp755460 16447517 8388608 119 16777216 Bool.true 12753919 33554432 1 10890000 (@hp755462 hp627574 hp755463 hp738055 16447517 8388608 119 16777216 (hp755473 rfl) rfl) (Enclosure.sfrac_true_div 16447517 8388608)

noncomputable def hp755475 := nat_lit 36128903022893227310245690142878019400127909015502937905445375135051115590249178625802537841

noncomputable def hp755476 := nat_lit 391926047204388943658609875923538972268963109267178399897371005582665555121633474939761

noncomputable def hp755477 := nat_lit 217905825717554743081719388104668298664631382405823859035750979117643335356338481744845769585

noncomputable def hp755478 := BSN.cos_dyadic_bound_t 16447517 8388608 4 3 33554432 10890000 hp755475 hp633059 hp755476 hp755477 hp633062

noncomputable def hp755479 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 16447517) (BSN.cosEvenQ 8388608) 0 3 hp755475 hp633059 hp755476 rfl rfl rfl

noncomputable def hp755480 := hp755478 hp755476 12753919 rfl rfl rfl rfl rfl rfl rfl rfl (hp755479 rfl)

noncomputable def hp755481 := @BSN.binarySplit_of_base3 (BSN.cosOddP 16447517) (BSN.cosOddQ 8388608) 0 3 hp755477 hp633062 hp755476 rfl rfl rfl

noncomputable def hp755482 := hp755474 (BSN.cos_neg_of_bound 16447517 8388608 Bool.true 12753919 33554432 1 10890000 (hp755480 (hp755481 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp755483 := hp755432 (hp755435 (@Enclosure.Real.IsNear.neg hp755434 Bool.false 67703241 67108864 245 67108864 (hp755458 rfl))) (@hp755459 12753919 33554432 1312687216 182703882240000 12753919 33554432 82042951 11418992640000 (hp755482 rfl) rfl)

noncomputable def hp755484 := @hp755407 67108864 863481651751479 2251799813685248 13235943418101247 1532631248189521920000 17072060661773975841489 151115727451828646838272 262278085819639380270799 hp755229 (hp755425 rfl) (@hp755428 Bool.false 863481651751479 2251799813685248 13235943418101247 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755233 (Enclosure.sfrac Bool.false 11 1)) (hp755429 rfl (hp755236 rfl rfl))) (hp755483 rfl))

noncomputable def hp755485 := @hp755230 hp755227 hp755229 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 834004 1000))) (@hp755235 hp755227 hp755229 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 834004 1000) 11 (hp755236 rfl rfl)) (@hp755239 hp755227 hp755229 hp755406 (hp755484 rfl) rfl rfl))

theorem hd5031 : hp755228 hp755229 := hp755485

noncomputable def hp755486 := nat_lit 2599702426684680519130243

noncomputable def hp755487 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 835932 1000)) Bool.true 299924172146550985982823 75557863725914323419136 hp755486

noncomputable def hp755488 := nat_lit 3428438066563362425143296000

noncomputable def hp755489 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 835932 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 835932 1000)) Bool.true 299924172146550985982823 75557863725914323419136

noncomputable def hp755490 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 835932 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755491 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp755490 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755492 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 835932 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755493 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp755491 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp755494 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 835932 1000)) hp755493 Bool.true 299924172146550985982823 75557863725914323419136

noncomputable def hp755495 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 835932 1000) 835932 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl

noncomputable def hp755496 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp755491 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp755497 := nat_lit 80510281915581912749548700172288

noncomputable def hp755498 := @hp755496 1095955623 268435456 101423 134217728 8559911313286501235865 75557863725914323419136 8968108599249157594243 hp755488 hp755497 299924172146550985982823 75557863725914323419136

noncomputable def hp755499 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) 11)

noncomputable def hp755500 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) 11) hp755499

noncomputable def hp755501 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) 11)

noncomputable def hp755502 := @hp755501 1095955623 536870912 202846 536870912 1095955623 536870912 202846 536870912 1176773389663076352 1095955623 268435456

noncomputable def hp755503 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp755504 := hp755503 BSN.quadSignNeg 9 10 11 835932 1000 190 241 536870912 268435456 9007199254740992

noncomputable def hp755505 := hp755504 Bool.false 872831408714 3809 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp755506 := hp755505 Bool.true 931133050 174138 Bool.true 310346775 Bool.true 75314286 28296951008113761 1 Bool.false 449640668

noncomputable def hp755507 := hp755506 Bool.true Bool.false 75067503 Bool.true Bool.true 1095955623 202846 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 449640668 536870912) BSN.abs_quadSignNeg

noncomputable def hp755508 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp755509 := hp755508 BSN.quadSignNeg 7 8 9 835932 1000 71 134 536870912 268435456 9007199254740992

noncomputable def hp755510 := hp755509 Bool.false 872831408714 3809 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp755511 := hp755510 Bool.true 928025733 142218 Bool.true 520762974 Bool.true 251478474 28296951008113761 1 Bool.false 442856121

noncomputable def hp755512 := hp755511 Bool.false Bool.false 479041819 Bool.true Bool.true 931133050 174138 BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 442856121 536870912) BSN.abs_quadSignNeg

noncomputable def hp755513 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp755514 := hp755513 BSN.quadSignPos 5 6 7 835932 1000 81 0 536870912 268435456 9007199254740992

noncomputable def hp755515 := hp755514 Bool.false 872831408714 3809 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp755516 := hp755515 Bool.true 908693365 105685 Bool.false 403523907 Bool.true 468875789 28296951008113761 1 Bool.false 366588639

noncomputable def hp755517 := hp755516 Bool.true Bool.false 344812340 Bool.false Bool.true 928025733 142218 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 366588639 536870912) BSN.abs_quadSignPos

noncomputable def hp755518 := hp755513 BSN.quadSignNeg 3 4 5 835932 1000 297 178 536870912 268435456 9007199254740992

noncomputable def hp755519 := hp755518 Bool.false 872831408714 3809 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp755520 := hp755519 Bool.true 635431428 62466 Bool.false 215223134 Bool.false 425639333 28296951008113761 1 Bool.false 209504589

noncomputable def hp755521 := hp755520 Bool.true Bool.false 376799014 Bool.true Bool.true 908693365 105685 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 297 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 209504589 536870912) BSN.abs_quadSignNeg

noncomputable def hp755522 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp755523 := hp755522 BSN.quadSignNeg 1 2 3 835932 1000 666 450 536870912 268435456 9007199254740992

noncomputable def hp755524 := hp755523 Bool.false 872831408714 3809 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp755525 := hp755524 Bool.false 532200 3866 Bool.false 107884356 Bool.false 296182620 28296951008113761 1 Bool.false 526067644

noncomputable def hp755526 := hp755525 Bool.true Bool.false 457222659 Bool.true Bool.true 635431428 62466 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 666 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 526067644 536870912) BSN.abs_quadSignNeg

noncomputable def hp755527 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) 1) Bool.false

noncomputable def hp755528 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)))

noncomputable def hp755529 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000))) Bool.false 66525 67108864

noncomputable def hp755530 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 109103926089) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 109103926089 67108864

noncomputable def hp755531 := nat_lit 15248477970688131290579058596033747578085367830095009

noncomputable def hp755532 := nat_lit 9379204498141796684023078064189853014567786905600

noncomputable def hp755533 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) Bool.false hp755531 hp755532 31638144428294193409

noncomputable def hp755534 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 835932 4000) (Real.log (Enclosure.sfrac Bool.false 2795130234496 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1671864))))))

noncomputable def hp755535 := nat_lit 195927945305455808026129990287360000

noncomputable def hp755536 := nat_lit 982694799118630706288475806099696517120

noncomputable def hp755537 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp755534 (Enclosure.sfrac Bool.false 835932 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 835932 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp755535 hp755536)) Bool.false

noncomputable def hp755538 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 835932 1000) 835932 1000 2795130234496 16000000 1671864

noncomputable def hp755539 := hp755538 4000 2000 hp755535 hp755536 (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl rfl rfl rfl

noncomputable def hp755540 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp755534 (Enclosure.sfrac Bool.false 835932 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 835932 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp755535 hp755536) 1464368287142822525213 900719925474099200

noncomputable def hp755541 := nat_lit 1439026923293305016053520425175521461039459839202873374146560

noncomputable def hp755542 := @hp755540 31638144428294193409 hp739140 hp755535 hp755536 0 1 hp755541 hp755531 hp755532 31638144428294193409 hp739140

noncomputable def hp755543 := @Enclosure.Real.IsNear.subLit_ff_p (hp755534 (Enclosure.sfrac Bool.false 835932 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 835932 2000) (Real.log Real.pi)) 9476625472109140155793 4503599627370496000 659322842259601 272250000000000000000

noncomputable def hp755544 := nat_lit 122840115284725781775819735040000

noncomputable def hp755545 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 835932 4000) (Real.log (Enclosure.sfrac Bool.false 2795130234496 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1671864))))))

noncomputable def hp755546 := @hp755545 (Enclosure.sfrac Bool.false 835932 2000) 11358976993962676886929 4503599627370496000 659322842259601 272250000000000000000 835932 2000 0

noncomputable def hp755547 := nat_lit 18953250944218280311586000

noncomputable def hp755548 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 835932 4000) (Real.log (Enclosure.sfrac Bool.false 2795130234496 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1671864))))) 11360744879963233756929

noncomputable def hp755549 := nat_lit 25578142278660174210125080755691323392

noncomputable def hp755550 := @hp755548 4503599627370496000 870763789634093 363000000000000000000 883943000278435 2251799813685248 200000001089 8712000000000000000 hp755549 11358976993962676886929 4503599627370496000 659322842259601

noncomputable def hp755551 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 835932 4000) (Real.log (Enclosure.sfrac Bool.false 2795130234496 16000000)) 835932 4000 0 1 54362052798377063 4503599627370496

noncomputable def hp755552 := nat_lit 116741619456227383730765824

noncomputable def hp755553 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2795130234496) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp755552 hp617687

noncomputable def hp755554 := BSN.log_rat_reduce_isNear 2795130234496 16000000 17 5590260468992 4194304000000 77121095 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp755555 := nat_lit 310115758834293946687330132443346104226294022079637089099088230180903943330082312961266282947430339051520

noncomputable def hp755556 := nat_lit 2130161357593531477089474859185918232832036026878364905939779022644870426888451696556306063257747062784

noncomputable def hp755557 := nat_lit 5914585832688669232675415930000873815894239058260339208872859979488285552342284199664377166561280

noncomputable def hp755558 := BSN.log_dyadic_bound 697978234496 4892282234496 5 4 hp755555 268435456 87120000 hp755556 hp755557 77121095 5590260468992

noncomputable def hp755559 := hp755558 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp755560 := @BSN.binarySplit_of_base4 (BSN.artanhP 697978234496) (BSN.artanhQ 4892282234496) 0 4 hp755556 hp755555 hp755557 rfl rfl rfl

noncomputable def hp755561 := hp755554 rfl rfl rfl rfl (hp755559 (hp755560 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp755562 := @hp755551 12500018513 1089000000000000000 11360744879963233756929 4503599627370496000 870763789634093 363000000000000000000 (Enclosure.Real.IsNear.const Bool.false 835932 4000) (BSN.isNear_log_sfrac 2795130234496 16000000 54362052798377063 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp755553 1000001481040000 87120000000000000000000 54362052798377063 4503599627370496 12500018513 1089000000000000000 (hp755561 rfl rfl rfl) rfl)) rfl

noncomputable def hp755563 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1671864)))) 1 4

noncomputable def hp755564 := @hp755563 0 1 883943000278435 562949953421312 200000001089 2178000000000000000 883943000278435 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp755565 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1671864))) 884279719003555 562949953421312 1

noncomputable def hp755566 := @hp755565 2000000000000000 20070 33554432 1 10890000 29660205294718728273920 883943000278435 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp755567 := BSN.arctan_dyadic_bound_f 1000 1671864 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp755568 := hp755567 1 20070 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1671864) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1671864) 0 0 rfl)

noncomputable def hp755569 := hp755564 (hp755566 (hp755568 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp755570 := @hp755543 8027196066063 16777216000 626949 134217728000 hp755544 1464368287142822525213 900719925474099200 31638144428294193409 hp739140 (@hp755546 1 hp755547 9476625472109140155793 4503599627370496000 659322842259601 272250000000000000000 (@hp755550 272250000000000000000 hp755562 hp755569 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 835932 2000) rfl rfl)

noncomputable def hp755571 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 835932 2000) (Real.log Real.pi) 835932 2000 0 1 38410761 33554432

noncomputable def hp755572 := hp755570 (@hp755571 3 268435456 8027196066063 16777216000 626949 134217728000 (Enclosure.Real.IsNear.const Bool.false 835932 2000) hd4909 rfl) rfl

noncomputable def hp755573 := @hp755533 hp739140 109103926089 67108864 477 67108864 (@hp755537 hp755531 hp755532 31638144428294193409 hp739140 (hp755539 rfl rfl rfl rfl rfl) (hp755542 (hp755572 rfl) (Enclosure.Real.IsNear.const Bool.true hp755535 hp755536) rfl rfl)) rfl

noncomputable def hp755574 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 109103926089) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 9587276072072572305408) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp755575 := BSN.sin_reduce_arg_pos_rat_q3 109103926089 67108864 226375608064910080 72057594037927936 258 9587276072072572305408 hp617687 rfl rfl rfl rfl

noncomputable def hp755576 := BSN.sin_dyadic_bound_f 136243387 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp755577 := hp755576 1 66525 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 136243387) (BSN.sinEvenQ 137438953472) 0 0 rfl)

noncomputable def hp755578 := hp755577 (@BSN.binarySplit_of_le (BSN.sinOddP 136243387) (BSN.sinOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp755579 := @BSN.sin_arg_round Bool.false 66525 67108864 9587276072072572305408 hp617687 136243387 137438953472 21801270 21780000 hp755578 rfl

noncomputable def hp755580 := hp755574 66525 67108864 258 1000000000000000 21780000 10890000 hp755575 BSN.pi_near_15 hp755579 rfl rfl

noncomputable def hp755581 := @hp755530 477 67108864 Bool.false 66525 67108864 1 10890000 hp755573 (Enclosure.sfrac_false_div 109103926089 67108864) (hp755580 rfl rfl) rfl

noncomputable def hp755582 := @hp755527 66525 67108864 328852429 45675970560000 532200 536870912 3866 536870912 (@hp755528 Bool.false 66525 67108864 328852429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000)) (@hp755529 5261638864 730815528960000 66525 67108864 328852429 45675970560000 (hp755581 rfl) rfl))

noncomputable def hp755583 := @hp755533 hp739140 872831408714 536870912 3809 536870912 (@hp755537 hp755531 hp755532 31638144428294193409 hp739140 (hp755539 rfl rfl rfl rfl rfl) (hp755542 (hp755572 rfl) (Enclosure.Real.IsNear.const Bool.true hp755535 hp755536) rfl rfl)) rfl

noncomputable def hp755584 := hp755526 (BSN.cos_quad_nat2 450 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 457222659 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl rfl (hp755582 rfl) hp755583

noncomputable def hp755585 := nat_lit 135467118727403985619021910589696

noncomputable def hp755586 := BSN.cos_dyadic_bound_f 107884356 536870912 2 1 536870912 268435456 hp755585 hp708767 hp755585 hp755585 hp708768

noncomputable def hp755587 := @BSN.binarySplit_of_base (BSN.cosEvenP 107884356) (BSN.cosEvenQ 536870912) 0 1 hp755585 hp708767 hp755585 rfl rfl rfl

noncomputable def hp755588 := hp755586 hp755585 526067644 rfl rfl rfl rfl rfl rfl rfl rfl (hp755587 rfl)

noncomputable def hp755589 := @BSN.binarySplit_of_base (BSN.cosOddP 107884356) (BSN.cosOddQ 536870912) 0 1 hp755585 hp708768 hp755585 rfl rfl rfl

noncomputable def hp755590 := nat_lit 1074115555736689319089549540666061618921470428902981582410599805132800000

noncomputable def hp755591 := nat_lit 59221112859190544751818457909815657147185326378108359634969600000000

noncomputable def hp755592 := nat_lit 3222228224984349576179144985082365225450116916056188530512529476198400000

noncomputable def hp755593 := BSN.cos_dyadic_bound_f 296182620 536870912 3 2 536870912 268435456 hp755590 hp708868 hp755591 hp755592 hp708870

noncomputable def hp755594 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 296182620) (BSN.cosEvenQ 536870912) 0 2 hp755590 hp708868 hp755591 rfl rfl rfl

noncomputable def hp755595 := hp755593 hp755591 457222659 rfl rfl rfl rfl rfl rfl rfl rfl (hp755594 rfl)

noncomputable def hp755596 := @BSN.binarySplit_of_base2 (BSN.cosOddP 296182620) (BSN.cosOddQ 536870912) 0 2 hp755592 hp708870 hp755591 rfl rfl rfl

noncomputable def hp755597 := hp755584 hd4911 hd4913 hd4915 hd4917 hd4918 (hp755588 (hp755589 rfl) rfl rfl rfl rfl) (hp755595 (hp755596 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755598 := hp755521 (BSN.cos_quad_nat2 178 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 376799014 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl rfl (hp755597 rfl rfl rfl rfl rfl) hp755583

noncomputable def hp755599 := nat_lit 2145634800944384682162951551185936

noncomputable def hp755600 := BSN.sin_dyadic_bound_f 215223134 536870912 2 1 536870912 268435456 hp755599 hp708890 hp755599 hp755599 hp708891

noncomputable def hp755601 := @BSN.binarySplit_of_base (BSN.sinEvenP 215223134) (BSN.sinEvenQ 536870912) 0 1 hp755599 hp708890 hp755599 rfl rfl rfl

noncomputable def hp755602 := hp755600 hp755599 209504589 rfl rfl rfl rfl rfl rfl rfl rfl (hp755601 rfl)

noncomputable def hp755603 := @BSN.binarySplit_of_base (BSN.sinOddP 215223134) (BSN.sinOddQ 536870912) 0 1 hp755599 hp708891 hp755599 rfl rfl rfl

noncomputable def hp755604 := nat_lit 4582029856616847352669080744490544050303787325636898274999831382914961121

noncomputable def hp755605 := nat_lit 1077293480598408651362698978537093449831162955229656644537979088867041

noncomputable def hp755606 := nat_lit 13743934982889345240704516835514557964011699651000235511710418190567149281

noncomputable def hp755607 := BSN.cos_dyadic_bound_f 425639333 536870912 3 2 536870912 268435456 hp755604 hp708868 hp755605 hp755606 hp708870

noncomputable def hp755608 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 425639333) (BSN.cosEvenQ 536870912) 0 2 hp755604 hp708868 hp755605 rfl rfl rfl

noncomputable def hp755609 := hp755607 hp755605 376799014 rfl rfl rfl rfl rfl rfl rfl rfl (hp755608 rfl)

noncomputable def hp755610 := @BSN.binarySplit_of_base2 (BSN.cosOddP 425639333) (BSN.cosOddQ 536870912) 0 2 hp755606 hp708870 hp755605 rfl rfl rfl

noncomputable def hp755611 := hp755598 hd4920 hd4922 hd4924 hd4926 hd4918 (hp755602 (hp755603 rfl) rfl rfl rfl rfl) (hp755609 (hp755610 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755612 := hp755517 (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 344812340 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl rfl (hp755611 rfl rfl rfl rfl rfl) hp755583

noncomputable def hp755613 := nat_lit 6661686580164532379589302658012019646033097713638351154229943457997916065

noncomputable def hp755614 := nat_lit 702998112096275118556466544287483211773713932601521429621348307306401

noncomputable def hp755615 := nat_lit 17446136189201809882065748872769300290600955617923850559716179254639855521

noncomputable def hp755616 := BSN.sin_dyadic_bound_f 403523907 536870912 3 2 536870912 268435456 hp755613 hp708845 hp755614 hp755615 hp708848

noncomputable def hp755617 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 403523907) (BSN.sinEvenQ 536870912) 0 2 hp755613 hp708845 hp755614 rfl rfl rfl

noncomputable def hp755618 := hp755616 hp755614 366588639 rfl rfl rfl rfl rfl rfl rfl rfl (hp755617 rfl)

noncomputable def hp755619 := @BSN.binarySplit_of_base2 (BSN.sinOddP 403523907) (BSN.sinOddQ 536870912) 0 2 hp755615 hp708848 hp755614 rfl rfl rfl

noncomputable def hp755620 := nat_lit 6747927024897746664940510742213345173998625423508635918142729834841776161

noncomputable def hp755621 := nat_lit 2335944196836840182708283175171023847702685357030329963374100276584481

noncomputable def hp755622 := nat_lit 20239109186299566314456115660289693474300470899811847094501441303972159521

noncomputable def hp755623 := BSN.cos_dyadic_bound_f 468875789 536870912 3 2 536870912 268435456 hp755620 hp708868 hp755621 hp755622 hp708870

noncomputable def hp755624 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 468875789) (BSN.cosEvenQ 536870912) 0 2 hp755620 hp708868 hp755621 rfl rfl rfl

noncomputable def hp755625 := hp755623 hp755621 344812340 rfl rfl rfl rfl rfl rfl rfl rfl (hp755624 rfl)

noncomputable def hp755626 := @BSN.binarySplit_of_base2 (BSN.cosOddP 468875789) (BSN.cosOddQ 536870912) 0 2 hp755622 hp708870 hp755621 rfl rfl rfl

noncomputable def hp755627 := hp755612 hd4928 hd4930 hd4932 hd4934 hd4918 (hp755618 (hp755619 rfl) rfl rfl rfl rfl) (hp755625 (hp755626 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755628 := hp755512 (BSN.cos_quad_nat2 134 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 479041819 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl rfl (hp755627 rfl rfl rfl rfl rfl) hp755583

noncomputable def hp755629 := nat_lit 18481992927032035307229357967029056285120328854621049748429836696886083840

noncomputable def hp755630 := nat_lit 5409047412319165255239550030475872577359230357040863176805383384760576

noncomputable def hp755631 := nat_lit 48396462065463956679949359213598186476856565389143730800744268347316797696

noncomputable def hp755632 := BSN.sin_dyadic_bound_f 520762974 536870912 3 2 536870912 268435456 hp755629 hp708845 hp755630 hp755631 hp708848

noncomputable def hp755633 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 520762974) (BSN.sinEvenQ 536870912) 0 2 hp755629 hp708845 hp755630 rfl rfl rfl

noncomputable def hp755634 := hp755632 hp755630 442856121 rfl rfl rfl rfl rfl rfl rfl rfl (hp755633 rfl)

noncomputable def hp755635 := @BSN.binarySplit_of_base2 (BSN.sinOddP 520762974) (BSN.sinOddQ 536870912) 0 2 hp755631 hp708848 hp755630 rfl rfl rfl

noncomputable def hp755636 := nat_lit 558218838849255882847494376805384041965266799423564098695033555261645056

noncomputable def hp755637 := nat_lit 15995820821462866499884809457940710262313138988392790186462833336576

noncomputable def hp755638 := nat_lit 1674624524906124722809483360797236244475275771992715510504727740118262016

noncomputable def hp755639 := BSN.cos_dyadic_bound_f 251478474 536870912 3 2 536870912 268435456 hp755636 hp708868 hp755637 hp755638 hp708870

noncomputable def hp755640 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 251478474) (BSN.cosEvenQ 536870912) 0 2 hp755636 hp708868 hp755637 rfl rfl rfl

noncomputable def hp755641 := hp755639 hp755637 479041819 rfl rfl rfl rfl rfl rfl rfl rfl (hp755640 rfl)

noncomputable def hp755642 := @BSN.binarySplit_of_base2 (BSN.cosOddP 251478474) (BSN.cosOddQ 536870912) 0 2 hp755638 hp708870 hp755637 rfl rfl rfl

noncomputable def hp755643 := hp755628 hd4936 hd4938 hd4940 hd4942 hd4918 (hp755634 (hp755635 rfl) rfl rfl rfl rfl) (hp755641 (hp755642 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755644 := hp755507 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 75067503 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl rfl (hp755643 rfl rfl rfl rfl rfl) hp755583

noncomputable def hp755645 := nat_lit 1294811626970955922896380000020458340529126679011227537608693606837890625

noncomputable def hp755646 := nat_lit 86055353676690366669773112047464024711469093769132008691558837890625

noncomputable def hp755647 := nat_lit 3884262770205514387955800453837280093537957098846144348808697702837890625

noncomputable def hp755648 := BSN.cos_dyadic_bound_f 310346775 536870912 3 2 536870912 268435456 hp755645 hp708868 hp755646 hp755647 hp708870

noncomputable def hp755649 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 310346775) (BSN.cosEvenQ 536870912) 0 2 hp755645 hp708868 hp755646 rfl rfl rfl

noncomputable def hp755650 := hp755648 hp755646 449640668 rfl rfl rfl rfl rfl rfl rfl rfl (hp755649 rfl)

noncomputable def hp755651 := @BSN.binarySplit_of_base2 (BSN.cosOddP 310346775) (BSN.cosOddQ 536870912) 0 2 hp755647 hp708870 hp755646 rfl rfl rfl

noncomputable def hp755652 := nat_lit 32174325627432184862372418521616

noncomputable def hp755653 := BSN.sin_dyadic_bound_f 75314286 536870912 2 1 536870912 268435456 hp755652 hp708890 hp755652 hp755652 hp708891

noncomputable def hp755654 := @BSN.binarySplit_of_base (BSN.sinEvenP 75314286) (BSN.sinEvenQ 536870912) 0 1 hp755652 hp708890 hp755652 rfl rfl rfl

noncomputable def hp755655 := hp755653 hp755652 75067503 rfl rfl rfl rfl rfl rfl rfl rfl (hp755654 rfl)

noncomputable def hp755656 := @BSN.binarySplit_of_base (BSN.sinOddP 75314286) (BSN.sinOddQ 536870912) 0 1 hp755652 hp708891 hp755652 rfl rfl rfl

noncomputable def hp755657 := hp755644 hd4944 hd4946 hd4961 hd4963 hd4918 (hp755650 (hp755651 rfl) rfl rfl rfl rfl) (hp755655 (hp755656 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755658 := @hp755502 101423 134217728 (hp755657 rfl rfl rfl rfl rfl) (hp755657 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp755659 := @hp755500 Bool.true 1095955623 268435456 101423 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 835932 1000)) (Enclosure.sfrac Bool.false 835932 1000) 11) hp755658

noncomputable def hp755660 := @Enclosure.Real.IsNear.mulLit_tf hp755491 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1))) 19759781 67108864 1

noncomputable def hp755661 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp755490 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755662 := @hp755661 1 1 0 1 19759781 67108864 1 67108864 19759781 67108864 1

noncomputable def hp755663 := @Enclosure.Real.IsNear.of_eq (hp755490 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755664 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 835932 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755665 := @hp755663 (@Inv.inv Real Real.instInv (Real.sqrt hp755492)) Bool.false 19759781 67108864 1 67108864 (hp755664 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 835932 1000) 835932 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000))))

noncomputable def hp755666 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp755492)) Bool.false 19759781 67108864 1 67108864 19759781 67108864

noncomputable def hp755667 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp755492) Bool.false 227917490 67108864 6 67108864 113958745 33554432 3 33554432

noncomputable def hp755668 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 835932 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755669 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 835932 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755670 := @hp755669 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 835932 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2232086190981

noncomputable def hp755671 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 835932 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 835932 1000 0

noncomputable def hp755672 := @hp755671 1 10680707 67108864 1 67108864 2232086190981 16777216000 208983 16777216000 (Enclosure.Real.IsNear.const Bool.false 835932 1000) hd4949

noncomputable def hp755673 := @hp755670 16777216000 208983 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 835932 1000) 835932 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000))) (hp755672 rfl)

noncomputable def hp755674 := @hp755668 2232086190981 16777216000 208983 16777216000 387030689 387030726 33554432 hp755673 rfl rfl rfl

noncomputable def hp755675 := @Enclosure.Real.IsNear.recentre' hp755492 Bool.false 774061415 67108864 37 67108864 774061415 67108864 37 67108864 (hp755674 rfl rfl rfl)

noncomputable def hp755676 := @Enclosure.Real.IsNear.sqrt_image hp755492 774061415 67108864 37 67108864 113958742 113958748 33554432 (hp755675 rfl) rfl rfl

noncomputable def hp755677 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp755492) 113958745 33554432 3 33554432 9879890 9879891 33554432 (hp755667 (hp755676 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp755678 := @hp755662 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp755665 (@hp755666 1 67108864 (hp755677 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp755679 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755680 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp755681 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1))) (hp755679 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755680 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp755682 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 835932 1000) 835932 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl

noncomputable def hp755683 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755684 := @hp755683 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755680 (Enclosure.sfrac Bool.false 1 16)))) 68708857

noncomputable def hp755685 := @hp755684 67108864 253 67108864 6304845 16777216 166127777 22837985280000 433198693512165 1125899906842624 339646416969493 38315781204738048000

noncomputable def hp755686 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755687 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755688 := @hp755686 (@Neg.neg Real Real.instNeg hp755687) Bool.true 68708857 67108864 253 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755689 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755690 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp755691 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp755692 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 112669799) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp755693 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1))) Bool.false 31713729141448505203605

noncomputable def hp755694 := nat_lit 998484790442698331544561091

noncomputable def hp755695 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp755696 := @Enclosure.Real.IsNear.subLit_ff_p hp755492 (Enclosure.sfrac Bool.false 11 1) 774061415 67108864 37 67108864 11 1 0

noncomputable def hp755697 := @hp755695 500000000000000 35863911 67108864 37 67108864 31713729141448505203605 9444732965739290427392 hp755694 hp738031 hd4948 (@hp755696 1 35863911 35863911 67108864 37 67108864 (hp755675 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755698 := @hp755692 112669799 33554432 117 33554432 Bool.true 65546129 67108864 1 10890000 (@hp755693 9444732965739290427392 hp755694 hp738031 112669799 33554432 117 33554432 (hp755697 rfl) rfl) (Enclosure.sfrac_false_div 112669799 33554432)

noncomputable def hp755699 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 112669799) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1045619378808524120260608) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp755700 := BSN.sin_reduce_arg_pos_rat_q2 112669799 33554432 226375608064910080 72057594037927936 0 1045619378808524120260608 hp619237 rfl rfl rfl rfl

noncomputable def hp755701 := nat_lit 780001207022619579640252066494578154768961

noncomputable def hp755702 := BSN.cos_dyadic_bound_f 29718290159 137438953472 2 1 67108864 21801270 hp755701 hp755189 hp755701 hp755701 hp755190

noncomputable def hp755703 := @BSN.binarySplit_of_base (BSN.cosEvenP 29718290159) (BSN.cosEvenQ 137438953472) 0 1 hp755701 hp755189 hp755701 rfl rfl rfl

noncomputable def hp755704 := hp755702 hp755701 65546129 rfl rfl rfl rfl rfl rfl rfl rfl (hp755703 rfl)

noncomputable def hp755705 := @BSN.binarySplit_of_base (BSN.cosOddP 29718290159) (BSN.cosOddQ 137438953472) 0 1 hp755701 hp755190 hp755701 rfl rfl rfl

noncomputable def hp755706 := @BSN.cos_arg_round Bool.false 65546129 67108864 1045619378808524120260608 hp619237 29718290159 137438953472 21801270 21780000 (hp755704 (hp755705 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755707 := hp755699 65546129 67108864 0 1000000000000000 21780000 10890000 hp755700 BSN.pi_near_15 hp755706 rfl rfl

noncomputable def hp755708 := @hp755690 65546129 67108864 81730277 22837985280000 (@hp755691 65546129 67108864 1307684432 365407764480000 65546129 67108864 81730277 22837985280000 (hp755698 (hp755707 rfl rfl) rfl rfl) rfl)

noncomputable def hp755709 := @hp755689 65546129 67108864 81730277 22837985280000 34354302 34354555 33554432 hp755708 rfl rfl rfl

noncomputable def hp755710 := @Enclosure.Real.IsNear.recentre' hp755687 Bool.false 68708857 67108864 253 67108864 68708857 67108864 253 67108864 (hp755709 rfl rfl rfl)

noncomputable def hp755711 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755680 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp755712 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755680 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 131268569)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp755713 := nat_lit 1239796589791519972534764037645

noncomputable def hp755714 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755680 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp755713

noncomputable def hp755715 := nat_lit 27725271247935631193070924992318981

noncomputable def hp755716 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755680 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp755717 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp755718 := @hp755717 (Enclosure.sfrac Bool.false 1 16) 1120566213591183 4503599627370496 5136958751 4503599627370496 1 16 0

noncomputable def hp755719 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)) 1286220112215921

noncomputable def hp755720 := @hp755719 4503599627370496 2653930783 4503599627370496 35863911 67108864 37 67108864 75199925630885651546112 1120566213591183 4503599627370496 5136958751

noncomputable def hp755721 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)) 35863911 67108864 37

noncomputable def hp755722 := @hp755721 67108864 35863911 67108864 37 67108864 1286220112215921 4503599627370496 2653930783 4503599627370496 (@hp755696 1 35863911 35863911 67108864 37 67108864 (hp755675 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755723 := hp755722 (@hp755696 1 35863911 35863911 67108864 37 67108864 (hp755675 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755724 := @hp755720 4503599627370496 (hp755723 rfl) (@hp755696 1 35863911 35863911 67108864 37 67108864 (hp755675 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755725 := @hp755716 500000000000000 1402041190301839 4503599627370496 5136958751 4503599627370496 hp755713 hp627574 hp755715 hp742826 hd4948 (@hp755718 1 22432659044829424 1402041190301839 4503599627370496 5136958751 4503599627370496 (hp755724 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp755726 := @hp755712 131268569 67108864 241 33554432 Bool.true 12609690 33554432 1 10890000 (@hp755714 hp627574 hp755715 hp742826 131268569 67108864 241 33554432 (hp755725 rfl) rfl) (Enclosure.sfrac_true_div 131268569 67108864)

noncomputable def hp755727 := nat_lit 2459124215400179835972889820778678126415516644069518666912722577825842967259914105087829089899776750241

noncomputable def hp755728 := nat_lit 26177550776077304974130565193329122406367445776905303817821002335638076578029652046586119006630561

noncomputable def hp755729 := nat_lit 14832636924301145347393911631247364235351659661821177155445121015962013941715273797395712570375669461665

noncomputable def hp755730 := BSN.cos_dyadic_bound_t 131268569 67108864 4 3 33554432 10890000 hp755727 hp745658 hp755728 hp755729 hp745661

noncomputable def hp755731 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 131268569) (BSN.cosEvenQ 67108864) 0 3 hp755727 hp745658 hp755728 rfl rfl rfl

noncomputable def hp755732 := hp755730 hp755728 12609690 rfl rfl rfl rfl rfl rfl rfl rfl (hp755731 rfl)

noncomputable def hp755733 := @BSN.binarySplit_of_base3 (BSN.cosOddP 131268569) (BSN.cosOddQ 67108864) 0 3 hp755729 hp745661 hp755728 rfl rfl rfl

noncomputable def hp755734 := hp755726 (BSN.cos_neg_of_bound 131268569 67108864 Bool.true 12609690 33554432 1 10890000 (hp755732 (hp755733 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp755735 := hp755685 (hp755688 (@Enclosure.Real.IsNear.neg hp755687 Bool.false 68708857 67108864 253 67108864 (hp755710 rfl))) (@hp755711 12609690 33554432 2658044432 365407764480000 6304845 16777216 166127777 22837985280000 (hp755734 rfl) rfl)

noncomputable def hp755736 := @hp755660 67108864 433198693512165 1125899906842624 339646416969493 38315781204738048000 8559911313286501235865 75557863725914323419136 8968108599249157594243 hp755488 (hp755678 rfl) (@hp755681 Bool.false 433198693512165 1125899906842624 339646416969493 38315781204738048000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755492 (Enclosure.sfrac Bool.false 11 1)) (hp755682 rfl (hp755495 rfl rfl))) (hp755735 rfl))

noncomputable def hp755737 := @hp755489 hp755486 hp755488 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 835932 1000))) (@hp755494 hp755486 hp755488 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 835932 1000) 11 (hp755495 rfl rfl)) (@hp755498 hp755486 hp755488 hp755659 (hp755736 rfl) rfl rfl))

theorem hd5032 : hp755487 hp755488 := hp755737

noncomputable def hp755738 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 836975 1000)) Bool.false 1809654454223218690565 4722366482869645213696 35497466644823495963647

noncomputable def hp755739 := nat_lit 46751428180409487615590400

noncomputable def hp755740 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 836975 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 836975 1000)) Bool.false 1809654454223218690565 4722366482869645213696

noncomputable def hp755741 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 836975 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755742 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp755741 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755743 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 836975 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755744 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp755742 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp755745 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 836975 1000)) hp755744 Bool.false 1809654454223218690565 4722366482869645213696

noncomputable def hp755746 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 836975 1000) 836975 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl

noncomputable def hp755747 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp755742 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp755748 := nat_lit 485775418621840834989538672640

noncomputable def hp755749 := @hp755747 72389671 268435456 203103 268435456 536161894297153063429 4722366482869645213696 124511599251169768447 hp755739 hp755748 1809654454223218690565 4722366482869645213696

noncomputable def hp755750 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) 11)

noncomputable def hp755751 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) 11) hp755750

noncomputable def hp755752 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) 11)

noncomputable def hp755753 := @hp755752 72389671 536870912 203103 536870912 72389671 536870912 203103 536870912 77727817378299904 72389671 268435456

noncomputable def hp755754 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp755755 := hp755754 BSN.quadSignNeg 9 10 11 836975 1000 190 241 536870912 268435456 9007199254740992

noncomputable def hp755756 := hp755755 Bool.false 874200863835 3814 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp755757 := hp755756 Bool.false 241415226 174359 Bool.true 230238821 Bool.true 48575875 28296951008113761 1 Bool.false 488253605

noncomputable def hp755758 := hp755757 Bool.true Bool.false 48509623 Bool.true Bool.false 72389671 203103 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 488253605 536870912) BSN.abs_quadSignNeg

noncomputable def hp755759 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp755760 := hp755759 BSN.quadSignNeg 7 8 9 836975 1000 71 134 536870912 268435456 9007199254740992

noncomputable def hp755761 := hp755760 Bool.false 874200863835 3814 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp755762 := hp755761 Bool.false 311170539 142399 Bool.true 315704371 Bool.true 112373216 28296951008113761 1 Bool.false 297821434

noncomputable def hp755763 := hp755762 Bool.false Bool.false 525153287 Bool.true Bool.false 241415226 174359 BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 297821434 536870912) BSN.abs_quadSignNeg

noncomputable def hp755764 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp755765 := hp755764 BSN.quadSignPos 5 6 7 836975 1000 81 0 536870912 268435456 9007199254740992

noncomputable def hp755766 := hp755765 Bool.false 874200863835 3814 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp755767 := hp755766 Bool.false 337820907 105820 Bool.false 769671923 Bool.true 189045418 28296951008113761 1 Bool.false 531828001

noncomputable def hp755768 := hp755767 Bool.true Bool.false 503929638 Bool.false Bool.false 311170539 142399 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 81 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 531828001 536870912) BSN.abs_quadSignPos

noncomputable def hp755769 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp755770 := hp755769 BSN.quadSignPos 3 4 5 836975 1000 297 179 536870912 268435456 9007199254740992

noncomputable def hp755771 := hp755770 Bool.false 874200863835 3814 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp755772 := hp755771 Bool.false 583109577 62547 Bool.false 808413924 Bool.false 50564617 28296951008113761 1 Bool.false 535736890

noncomputable def hp755773 := hp755772 Bool.true Bool.false 50489893 Bool.false Bool.false 337820907 105820 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 297 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535736890 536870912) BSN.abs_quadSignPos

noncomputable def hp755774 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp755775 := hp755774 BSN.quadSignPos 1 2 3 836975 1000 667 451 536870912 268435456 9007199254740992

noncomputable def hp755776 := hp755775 Bool.false 874200863835 3814 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp755777 := hp755776 Bool.false 298601432 3874 Bool.false 245892463 Bool.false 207147951 28296951008113761 1 Bool.false 237385229

noncomputable def hp755778 := hp755777 Bool.false Bool.false 202046219 Bool.false Bool.false 583109577 62547 BSN.abs_quadSignPos (BSN.cos_quad_nat3 667 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 237385229 536870912) BSN.abs_quadSignPos

noncomputable def hp755779 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) 1) Bool.false

noncomputable def hp755780 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)))

noncomputable def hp755781 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000))) Bool.false 37325179 67108864

noncomputable def hp755782 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 109275107979) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 109275107979 67108864

noncomputable def hp755783 := nat_lit 2973917719119755816921161382890895986919657078149

noncomputable def hp755784 := nat_lit 1826365065656624577957775998796112211851870208

noncomputable def hp755785 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) Bool.false hp755783 hp755784 5068398698395745297

noncomputable def hp755786 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 836975 4000) (Real.log (Enclosure.sfrac Bool.false 2802109602500 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1673950))))))

noncomputable def hp755787 := nat_lit 197153304276263267444932812500000000

noncomputable def hp755788 := nat_lit 990074485968271655551503975703125000000

noncomputable def hp755789 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp755786 (Enclosure.sfrac Bool.false 836975 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 836975 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp755787 hp755788)) Bool.false

noncomputable def hp755790 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 836975 1000) 836975 1000 2802109602500 16000000 1673950

noncomputable def hp755791 := hp755790 4000 2000 hp755787 hp755788 (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl rfl rfl rfl

noncomputable def hp755792 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp755786 (Enclosure.sfrac Bool.false 836975 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 836975 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp755787 hp755788) 234666536217015524061 144115188075855872

noncomputable def hp755793 := nat_lit 232337321806230923196965733038351248978098209230390625000000

noncomputable def hp755794 := @hp755792 5068398698395745297 713687040000000000000000 hp755787 hp755788 0 1 hp755793 hp755783 hp755784 5068398698395745297 713687040000000000000000

noncomputable def hp755795 := @Enclosure.Real.IsNear.subLit_ff_p (hp755786 (Enclosure.sfrac Bool.false 836975 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 836975 2000) (Real.log Real.pi)) 1518528293907503973969 720575940379279360 422488119818507 174240000000000000000

noncomputable def hp755796 := nat_lit 3149640932867753858019675340800

noncomputable def hp755797 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 836975 4000) (Real.log (Enclosure.sfrac Bool.false 2802109602500 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1673950))))))

noncomputable def hp755798 := @hp755797 (Enclosure.sfrac Bool.false 836975 2000) 1820080317756977645137 720575940379279360 422488119818507 174240000000000000000 836975 2000 0

noncomputable def hp755799 := nat_lit 3037056587815007947938000

noncomputable def hp755800 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 836975 4000) (Real.log (Enclosure.sfrac Bool.false 2802109602500 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1673950))))) 1820363179651284472337

noncomputable def hp755801 := nat_lit 4098456520417349238347010376755838976

noncomputable def hp755802 := @hp755800 720575940379279360 418488119796727 174240000000000000000 883943419708835 2251799813685248 200000001089 8712000000000000000 hp755801 1820080317756977645137 720575940379279360 422488119818507

noncomputable def hp755803 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 836975 4000) (Real.log (Enclosure.sfrac Bool.false 2802109602500 16000000)) 836975 4000 0 1 54373284137856103 4503599627370496

noncomputable def hp755804 := nat_lit 116765738574103758969503744

noncomputable def hp755805 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2802109602500) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp755804 hp617687

noncomputable def hp755806 := BSN.log_rat_reduce_isNear 2802109602500 16000000 17 5604219205000 4194304000000 77790535 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp755807 := nat_lit 313672790052757618403982682500740094023792452002041937766289844487162165489723205566406250000000000000000

noncomputable def hp755808 := nat_lit 2192109651116987110178301046040482053524016852360173294077520406481633782385253906250000000000000000000

noncomputable def hp755809 := nat_lit 6404618815205401062412525898353149999019379918211951252999520062832191467285156250000000000000000

noncomputable def hp755810 := BSN.log_dyadic_bound 704957602500 4899261602500 5 4 hp755807 268435456 87120000 hp755808 hp755809 77790535 5604219205000

noncomputable def hp755811 := hp755810 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp755812 := @BSN.binarySplit_of_base4 (BSN.artanhP 704957602500) (BSN.artanhQ 4899261602500) 0 4 hp755808 hp755807 hp755809 rfl rfl rfl

noncomputable def hp755813 := hp755806 rfl rfl rfl rfl (hp755811 (hp755812 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp755814 := @hp755803 12500018513 1089000000000000000 1820363179651284472337 720575940379279360 418488119796727 174240000000000000000 (Enclosure.Real.IsNear.const Bool.false 836975 4000) (BSN.isNear_log_sfrac 2802109602500 16000000 54373284137856103 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp755805 1000001481040000 87120000000000000000000 54373284137856103 4503599627370496 12500018513 1089000000000000000 (hp755813 rfl rfl rfl) rfl)) rfl

noncomputable def hp755815 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1673950)))) 1 4

noncomputable def hp755816 := @hp755815 0 1 883943419708835 562949953421312 200000001089 2178000000000000000 883943419708835 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp755817 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1673950))) 884279719003555 562949953421312 1

noncomputable def hp755818 := @hp755817 2000000000000000 20045 33554432 1 10890000 29660219368467563806720 883943419708835 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp755819 := BSN.arctan_dyadic_bound_f 1000 1673950 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp755820 := hp755819 1 20045 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1673950) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1673950) 0 0 rfl)

noncomputable def hp755821 := hp755816 (hp755818 (hp755820 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp755822 := @hp755795 1285953867519 2684354560 100437 21474836480 hp755796 234666536217015524061 144115188075855872 5068398698395745297 713687040000000000000000 (@hp755798 1 hp755799 1518528293907503973969 720575940379279360 422488119818507 174240000000000000000 (@hp755802 174240000000000000000 hp755814 hp755821 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 836975 2000) rfl rfl)

noncomputable def hp755823 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 836975 2000) (Real.log Real.pi) 836975 2000 0 1 38410761 33554432

noncomputable def hp755824 := hp755822 (@hp755823 3 268435456 1285953867519 2684354560 100437 21474836480 (Enclosure.Real.IsNear.const Bool.false 836975 2000) hd4909 rfl) rfl

noncomputable def hp755825 := @hp755785 713687040000000000000000 109275107979 67108864 239 33554432 (@hp755789 hp755783 hp755784 5068398698395745297 713687040000000000000000 (hp755791 rfl rfl rfl rfl rfl) (hp755794 (hp755824 rfl) (Enclosure.Real.IsNear.const Bool.true hp755787 hp755788) rfl rfl)) rfl

noncomputable def hp755826 := nat_lit 9487687654057190377914368

noncomputable def hp755827 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 109275107979) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp755826) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp755828 := BSN.sin_reduce_arg_pos_rat_q0 109275107979 67108864 226375608064910080 72057594037927936 259 hp755826 hp617687 rfl rfl rfl rfl

noncomputable def hp755829 := nat_lit 198203037372752603632991108634038685012318889983339134681634702137273795086084755509830190625

noncomputable def hp755830 := nat_lit 109205528704670755102709093587734201644965355354477486153163496558803308856711349625390625

noncomputable def hp755831 := nat_lit 594390701060848469388767907714940586633666739239308449072597779418703778640540843830239790625

noncomputable def hp755832 := BSN.cos_dyadic_bound_f 134828150835 137438953472 3 2 67108864 21801270 hp755829 hp746621 hp755830 hp755831 hp746624

noncomputable def hp755833 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 134828150835) (BSN.cosEvenQ 137438953472) 0 2 hp755829 hp746621 hp755830 rfl rfl rfl

noncomputable def hp755834 := hp755832 hp755830 37325179 rfl rfl rfl rfl rfl rfl rfl rfl (hp755833 rfl)

noncomputable def hp755835 := @BSN.binarySplit_of_base2 (BSN.cosOddP 134828150835) (BSN.cosOddQ 137438953472) 0 2 hp755831 hp746624 hp755830 rfl rfl rfl

noncomputable def hp755836 := @BSN.cos_arg_round Bool.false 37325179 67108864 hp755826 hp617687 134828150835 137438953472 21801270 21780000 (hp755834 (hp755835 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755837 := hp755827 37325179 67108864 259 1000000000000000 21780000 10890000 hp755828 BSN.pi_near_15 hp755836 rfl rfl

noncomputable def hp755838 := @hp755782 239 33554432 Bool.false 37325179 67108864 1 10890000 hp755825 (Enclosure.sfrac_false_div 109275107979 67108864) (hp755837 rfl rfl) rfl

noncomputable def hp755839 := @hp755779 37325179 67108864 164766527 22837985280000 298601432 536870912 3874 536870912 (@hp755780 Bool.false 37325179 67108864 164766527 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000)) (@hp755781 2636264432 365407764480000 37325179 67108864 164766527 22837985280000 (hp755838 rfl) rfl))

noncomputable def hp755840 := @hp755785 713687040000000000000000 874200863835 536870912 3814 536870912 (@hp755789 hp755783 hp755784 5068398698395745297 713687040000000000000000 (hp755791 rfl rfl rfl rfl rfl) (hp755794 (hp755824 rfl) (Enclosure.Real.IsNear.const Bool.true hp755787 hp755788) rfl rfl)) rfl

noncomputable def hp755841 := hp755778 (BSN.cos_quad_nat3 451 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 202046219 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl rfl (hp755839 rfl) hp755840

noncomputable def hp755842 := nat_lit 918435098310746610124521155450325025874517071968052418963801723879633025

noncomputable def hp755843 := nat_lit 13364777623853726583733053295931020640675100394301911882741244833921

noncomputable def hp755844 := nat_lit 2405403619269135834768800791712181655637936000229975084666908648145498241

noncomputable def hp755845 := BSN.sin_dyadic_bound_f 245892463 536870912 3 2 536870912 268435456 hp755842 hp708845 hp755843 hp755844 hp708848

noncomputable def hp755846 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 245892463) (BSN.sinEvenQ 536870912) 0 2 hp755842 hp708845 hp755843 rfl rfl rfl

noncomputable def hp755847 := hp755845 hp755843 237385229 rfl rfl rfl rfl rfl rfl rfl rfl (hp755846 rfl)

noncomputable def hp755848 := @BSN.binarySplit_of_base2 (BSN.sinOddP 245892463) (BSN.sinOddQ 536870912) 0 2 hp755844 hp708848 hp755843 rfl rfl rfl

noncomputable def hp755849 := nat_lit 1841291580727091648157266009556801

noncomputable def hp755850 := BSN.sin_dyadic_bound_f 207147951 536870912 2 1 536870912 268435456 hp755849 hp708890 hp755849 hp755849 hp708891

noncomputable def hp755851 := @BSN.binarySplit_of_base (BSN.sinEvenP 207147951) (BSN.sinEvenQ 536870912) 0 1 hp755849 hp708890 hp755849 rfl rfl rfl

noncomputable def hp755852 := hp755850 hp755849 202046219 rfl rfl rfl rfl rfl rfl rfl rfl (hp755851 rfl)

noncomputable def hp755853 := @BSN.binarySplit_of_base (BSN.sinOddP 207147951) (BSN.sinOddQ 536870912) 0 1 hp755849 hp708891 hp755849 rfl rfl rfl

noncomputable def hp755854 := hp755841 hd4911 hd4913 hd4915 hd4917 hd4918 (hp755847 (hp755848 rfl) rfl rfl rfl rfl) (hp755852 (hp755853 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755855 := hp755773 (BSN.cos_quad_nat3 179 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 50489893 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl rfl (hp755854 rfl rfl rfl rfl rfl) hp755840

noncomputable def hp755856 := nat_lit 153225533387143788940926081915858983917697165687270340236319554719111831926837106917415253456574021326865407410176

noncomputable def hp755857 := nat_lit 77912191731439978352178488136970159516961735554162015484110332590317852808750828952514340862859244287819776

noncomputable def hp755858 := nat_lit 765323545493090673660843797691695929380713213245984820654361959698586726582541685356330666799079118342651522318336

noncomputable def hp755859 := BSN.sin_dyadic_bound_f 808413924 536870912 4 3 536870912 268435456 hp755856 hp642702 hp755857 hp755858 hp642705

noncomputable def hp755860 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 808413924) (BSN.sinEvenQ 536870912) 0 3 hp755856 hp642702 hp755857 rfl rfl rfl

noncomputable def hp755861 := hp755859 hp755857 535736890 rfl rfl rfl rfl rfl rfl rfl rfl (hp755860 rfl)

noncomputable def hp755862 := @BSN.binarySplit_of_base3 (BSN.sinOddP 808413924) (BSN.sinOddQ 536870912) 0 3 hp755858 hp642705 hp755857 rfl rfl rfl

noncomputable def hp755863 := nat_lit 6537126486095713017949203042721

noncomputable def hp755864 := BSN.sin_dyadic_bound_f 50564617 536870912 2 1 536870912 268435456 hp755863 hp708890 hp755863 hp755863 hp708891

noncomputable def hp755865 := @BSN.binarySplit_of_base (BSN.sinEvenP 50564617) (BSN.sinEvenQ 536870912) 0 1 hp755863 hp708890 hp755863 rfl rfl rfl

noncomputable def hp755866 := hp755864 hp755863 50489893 rfl rfl rfl rfl rfl rfl rfl rfl (hp755865 rfl)

noncomputable def hp755867 := @BSN.binarySplit_of_base (BSN.sinOddP 50564617) (BSN.sinOddQ 536870912) 0 1 hp755863 hp708891 hp755863 rfl rfl rfl

noncomputable def hp755868 := hp755855 hd4920 hd4922 hd4924 hd4926 hd4918 (hp755861 (hp755862 rfl) rfl rfl rfl rfl) (hp755866 (hp755867 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755869 := hp755768 (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 503929638 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl rfl (hp755868 rfl rfl rfl rfl rfl) hp755840

noncomputable def hp755870 := nat_lit 125859797047642988065630279646282060624112705872830616990112396602899322384773600684451977131724926896347436940721

noncomputable def hp755871 := nat_lit 43218304963634580163705919119543295443809264002637335344292094000442855859914688908127785602129469213375921

noncomputable def hp755872 := nat_lit 628756151921329415662477835918638876736400393784505835296784373760158050092157059481355050707760350521611734351281

noncomputable def hp755873 := BSN.sin_dyadic_bound_f 769671923 536870912 4 3 536870912 268435456 hp755870 hp642702 hp755871 hp755872 hp642705

noncomputable def hp755874 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 769671923) (BSN.sinEvenQ 536870912) 0 3 hp755870 hp642702 hp755871 rfl rfl rfl

noncomputable def hp755875 := hp755873 hp755871 531828001 rfl rfl rfl rfl rfl rfl rfl rfl (hp755874 rfl)

noncomputable def hp755876 := @BSN.binarySplit_of_base3 (BSN.sinOddP 769671923) (BSN.sinOddQ 536870912) 0 3 hp755872 hp642705 hp755871 rfl rfl rfl

noncomputable def hp755877 := nat_lit 178261425605029267046183457534257432947423124005912504197011751268147456

noncomputable def hp755878 := nat_lit 1631282753495025662847441229578307922415503181236130505437987102976

noncomputable def hp755879 := nat_lit 534781014249580811087224677720313142226424541011375040330024377830236416

noncomputable def hp755880 := BSN.cos_dyadic_bound_f 189045418 536870912 3 2 536870912 268435456 hp755877 hp708868 hp755878 hp755879 hp708870

noncomputable def hp755881 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 189045418) (BSN.cosEvenQ 536870912) 0 2 hp755877 hp708868 hp755878 rfl rfl rfl

noncomputable def hp755882 := hp755880 hp755878 503929638 rfl rfl rfl rfl rfl rfl rfl rfl (hp755881 rfl)

noncomputable def hp755883 := @BSN.binarySplit_of_base2 (BSN.cosOddP 189045418) (BSN.cosOddQ 536870912) 0 2 hp755879 hp708870 hp755878 rfl rfl rfl

noncomputable def hp755884 := hp755869 hd4928 hd4930 hd4932 hd4934 hd4918 (hp755875 (hp755876 rfl) rfl rfl rfl rfl) (hp755882 (hp755883 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755885 := hp755763 (BSN.cos_quad_nat2 134 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 525153287 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl rfl (hp755884 rfl rfl rfl rfl rfl) hp755840

noncomputable def hp755886 := nat_lit 2495748598164854299399810721338240482519123884973430098932140660577101345

noncomputable def hp755887 := nat_lit 98683548751908803635975842312302237539756704452558559126875221616161

noncomputable def hp755888 := nat_lit 6536324650400448646079331737855457536308355330742250878583686789247886881

noncomputable def hp755889 := BSN.sin_dyadic_bound_f 315704371 536870912 3 2 536870912 268435456 hp755886 hp708845 hp755887 hp755888 hp708848

noncomputable def hp755890 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 315704371) (BSN.sinEvenQ 536870912) 0 2 hp755886 hp708845 hp755887 rfl rfl rfl

noncomputable def hp755891 := hp755889 hp755887 297821434 rfl rfl rfl rfl rfl rfl rfl rfl (hp755890 rfl)

noncomputable def hp755892 := @BSN.binarySplit_of_base2 (BSN.sinOddP 315704371) (BSN.sinOddQ 536870912) 0 2 hp755888 hp708848 hp755887 rfl rfl rfl

noncomputable def hp755893 := nat_lit 159459809278926691111821651214336

noncomputable def hp755894 := BSN.cos_dyadic_bound_f 112373216 536870912 2 1 536870912 268435456 hp755893 hp708767 hp755893 hp755893 hp708768

noncomputable def hp755895 := @BSN.binarySplit_of_base (BSN.cosEvenP 112373216) (BSN.cosEvenQ 536870912) 0 1 hp755893 hp708767 hp755893 rfl rfl rfl

noncomputable def hp755896 := hp755894 hp755893 525153287 rfl rfl rfl rfl rfl rfl rfl rfl (hp755895 rfl)

noncomputable def hp755897 := @BSN.binarySplit_of_base (BSN.cosOddP 112373216) (BSN.cosOddQ 536870912) 0 1 hp755893 hp708768 hp755893 rfl rfl rfl

noncomputable def hp755898 := hp755885 hd4936 hd4938 hd4940 hd4942 hd4918 (hp755891 (hp755892 rfl) rfl rfl rfl rfl) (hp755896 (hp755897 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755899 := hp755758 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 48509623 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl rfl (hp755898 rfl rfl rfl rfl rfl) hp755840

noncomputable def hp755900 := nat_lit 392203742377987345045498970155397977043404097605367269864694508472892641

noncomputable def hp755901 := nat_lit 7896386937444796907677389900737791262630660434949557616703354305761

noncomputable def hp755902 := nat_lit 1176595434360087145542681555686392455547687031495231910478850118710066401

noncomputable def hp755903 := BSN.cos_dyadic_bound_f 230238821 536870912 3 2 536870912 268435456 hp755900 hp708868 hp755901 hp755902 hp708870

noncomputable def hp755904 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 230238821) (BSN.cosEvenQ 536870912) 0 2 hp755900 hp708868 hp755901 rfl rfl rfl

noncomputable def hp755905 := hp755903 hp755901 488253605 rfl rfl rfl rfl rfl rfl rfl rfl (hp755904 rfl)

noncomputable def hp755906 := @BSN.binarySplit_of_base2 (BSN.cosOddP 230238821) (BSN.cosOddQ 536870912) 0 2 hp755902 hp708870 hp755901 rfl rfl rfl

noncomputable def hp755907 := nat_lit 5567785930852497412500244140625

noncomputable def hp755908 := BSN.sin_dyadic_bound_f 48575875 536870912 2 1 536870912 268435456 hp755907 hp708890 hp755907 hp755907 hp708891

noncomputable def hp755909 := @BSN.binarySplit_of_base (BSN.sinEvenP 48575875) (BSN.sinEvenQ 536870912) 0 1 hp755907 hp708890 hp755907 rfl rfl rfl

noncomputable def hp755910 := hp755908 hp755907 48509623 rfl rfl rfl rfl rfl rfl rfl rfl (hp755909 rfl)

noncomputable def hp755911 := @BSN.binarySplit_of_base (BSN.sinOddP 48575875) (BSN.sinOddQ 536870912) 0 1 hp755907 hp708891 hp755907 rfl rfl rfl

noncomputable def hp755912 := hp755899 hd4944 hd4946 hd4961 hd4963 hd4918 (hp755905 (hp755906 rfl) rfl rfl rfl rfl) (hp755910 (hp755911 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755913 := @hp755753 203103 268435456 (hp755912 rfl rfl rfl rfl rfl) (hp755912 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp755914 := @hp755751 Bool.false 72389671 268435456 203103 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 836975 1000)) (Enclosure.sfrac Bool.false 836975 1000) 11) hp755913

noncomputable def hp755915 := @Enclosure.Real.IsNear.mulLit_tf hp755742 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1))) 9876811 33554432 1

noncomputable def hp755916 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp755741 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755917 := @hp755916 1 1 0 1 9876811 33554432 1 33554432 9876811 33554432 1

noncomputable def hp755918 := @Enclosure.Real.IsNear.of_eq (hp755741 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755919 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 836975 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755920 := @hp755918 (@Inv.inv Real Real.instInv (Real.sqrt hp755743)) Bool.false 9876811 33554432 1 33554432 (hp755919 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 836975 1000) 836975 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000))))

noncomputable def hp755921 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp755743)) Bool.false 19753622 67108864 2 67108864 9876811 33554432

noncomputable def hp755922 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp755743) Bool.false 227988550 67108864 6 67108864 113994275 33554432 3 33554432

noncomputable def hp755923 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 836975 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755924 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 836975 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755925 := @hp755924 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 836975 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 357579389653

noncomputable def hp755926 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 836975 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 836975 1000 0

noncomputable def hp755927 := @hp755926 1 10680707 67108864 1 67108864 357579389653 2684354560 33479 2684354560 (Enclosure.Real.IsNear.const Bool.false 836975 1000) hd4949

noncomputable def hp755928 := @hp755925 2684354560 33479 2684354560 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 836975 1000) 836975 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000))) (hp755927 rfl)

noncomputable def hp755929 := @hp755923 357579389653 2684354560 33479 2684354560 387272065 387272102 33554432 hp755928 rfl rfl rfl

noncomputable def hp755930 := @Enclosure.Real.IsNear.recentre' hp755743 Bool.false 774544167 67108864 37 67108864 774544167 67108864 37 67108864 (hp755929 rfl rfl rfl)

noncomputable def hp755931 := @Enclosure.Real.IsNear.sqrt_image hp755743 774544167 67108864 37 67108864 113994272 113994278 33554432 (hp755930 rfl) rfl rfl

noncomputable def hp755932 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp755743) 113994275 33554432 3 33554432 9876810 9876812 33554432 (hp755922 (hp755931 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp755933 := @hp755917 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp755920 (@hp755921 1 33554432 (hp755932 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp755934 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755935 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp755936 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1))) (hp755934 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755935 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp755937 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 836975 1000) 836975 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl

noncomputable def hp755938 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755939 := @hp755938 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755935 (Enclosure.sfrac Bool.false 1 16)))) 17367323

noncomputable def hp755940 := @hp755939 16777216 129 33554432 3125693 8388608 334297429 45675970560000 54284919929839 140737488355328 552289934842339 61305249927580876800

noncomputable def hp755941 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755942 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755943 := @hp755941 (@Neg.neg Real Real.instNeg hp755942) Bool.true 17367323 16777216 129 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755944 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp755945 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp755946 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp755947 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 114186409) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp755948 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1))) Bool.false 32140616944356909386965

noncomputable def hp755949 := nat_lit 39939391617873805585948731

noncomputable def hp755950 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp755951 := @Enclosure.Real.IsNear.subLit_ff_p hp755743 (Enclosure.sfrac Bool.false 11 1) 774544167 67108864 37 67108864 11 1 0

noncomputable def hp755952 := @hp755950 500000000000000 36346663 67108864 37 67108864 32140616944356909386965 9444732965739290427392 hp755949 hp754162 hd4948 (@hp755951 1 36346663 36346663 67108864 37 67108864 (hp755930 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755953 := @hp755947 114186409 33554432 117 33554432 Bool.true 64828639 67108864 1 10890000 (@hp755948 9444732965739290427392 hp755949 hp754162 114186409 33554432 117 33554432 (hp755952 rfl) rfl) (Enclosure.sfrac_false_div 114186409 33554432)

noncomputable def hp755954 := nat_lit 1264185914196247894294528

noncomputable def hp755955 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 114186409) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp755954) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp755956 := BSN.sin_reduce_arg_pos_rat_q2 114186409 33554432 226375608064910080 72057594037927936 0 hp755954 hp619237 rfl rfl rfl rfl

noncomputable def hp755957 := nat_lit 1666650621392233274151573023406943011539521

noncomputable def hp755958 := BSN.cos_dyadic_bound_f 35930324719 137438953472 2 1 67108864 21801270 hp755957 hp755189 hp755957 hp755957 hp755190

noncomputable def hp755959 := @BSN.binarySplit_of_base (BSN.cosEvenP 35930324719) (BSN.cosEvenQ 137438953472) 0 1 hp755957 hp755189 hp755957 rfl rfl rfl

noncomputable def hp755960 := hp755958 hp755957 64828639 rfl rfl rfl rfl rfl rfl rfl rfl (hp755959 rfl)

noncomputable def hp755961 := @BSN.binarySplit_of_base (BSN.cosOddP 35930324719) (BSN.cosOddQ 137438953472) 0 1 hp755957 hp755190 hp755957 rfl rfl rfl

noncomputable def hp755962 := @BSN.cos_arg_round Bool.false 64828639 67108864 hp755954 hp619237 35930324719 137438953472 21801270 21780000 (hp755960 (hp755961 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp755963 := hp755955 64828639 67108864 0 1000000000000000 21780000 10890000 hp755956 BSN.pi_near_15 hp755962 rfl rfl

noncomputable def hp755964 := @hp755945 64828639 67108864 81730277 22837985280000 (@hp755946 64828639 67108864 1307684432 365407764480000 64828639 67108864 81730277 22837985280000 (hp755953 (hp755963 rfl rfl) rfl rfl) rfl)

noncomputable def hp755965 := @hp755944 64828639 67108864 81730277 22837985280000 34734517 34734775 33554432 hp755964 rfl rfl rfl

noncomputable def hp755966 := @Enclosure.Real.IsNear.recentre' hp755942 Bool.false 69469292 67108864 258 67108864 17367323 16777216 129 33554432 (hp755965 rfl rfl rfl)

noncomputable def hp755967 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755935 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp755968 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755935 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32759495)) (@Nat.cast Real Real.instNatCast 16777216)) Bool.true

noncomputable def hp755969 := nat_lit 1237618732018544137828474492045

noncomputable def hp755970 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755935 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp755969

noncomputable def hp755971 := nat_lit 139590397298471145649318021172041881

noncomputable def hp755972 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp755935 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp755973 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp755974 := @hp755973 (Enclosure.sfrac Bool.false 1 16) 1118103352885263 4503599627370496 5172682399 4503599627370496 1 16 0

noncomputable def hp755975 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)) 1321079911235569

noncomputable def hp755976 := @hp755975 4503599627370496 2689654431 4503599627370496 36346663 67108864 37 67108864 75034645846721122271232 1118103352885263 4503599627370496 5172682399

noncomputable def hp755977 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)) 36346663 67108864 37

noncomputable def hp755978 := @hp755977 67108864 36346663 67108864 37 67108864 1321079911235569 4503599627370496 2689654431 4503599627370496 (@hp755951 1 36346663 36346663 67108864 37 67108864 (hp755930 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755979 := hp755978 (@hp755951 1 36346663 36346663 67108864 37 67108864 (hp755930 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755980 := @hp755976 4503599627370496 (hp755979 rfl) (@hp755951 1 36346663 36346663 67108864 37 67108864 (hp755930 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp755981 := @hp755972 500000000000000 1399578329595919 4503599627370496 5172682399 4503599627370496 hp755969 hp627574 hp755971 hp738055 hd4948 (@hp755974 1 22393253273534704 1399578329595919 4503599627370496 5172682399 4503599627370496 (hp755980 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp755982 := @hp755968 32759495 16777216 485 67108864 Bool.true 12502772 33554432 1 10890000 (@hp755970 hp627574 hp755971 hp738055 32759495 16777216 485 67108864 (hp755981 rfl) rfl) (Enclosure.sfrac_true_div 32759495 16777216)

noncomputable def hp755983 := nat_lit 145539194994796806307752939051682499817529689398577971440846813979825320007272413230120829390625

noncomputable def hp755984 := nat_lit 1527729201386623022639952635109757069497398154314541898370009457993848261332919238525390625

noncomputable def hp755985 := nat_lit 877880494702457372898830246850929444183473529630244988558324839997266498859598803075815702990625

noncomputable def hp755986 := BSN.cos_dyadic_bound_t 32759495 16777216 4 3 33554432 10890000 hp755983 hp633087 hp755984 hp755985 hp633090

noncomputable def hp755987 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 32759495) (BSN.cosEvenQ 16777216) 0 3 hp755983 hp633087 hp755984 rfl rfl rfl

noncomputable def hp755988 := hp755986 hp755984 12502772 rfl rfl rfl rfl rfl rfl rfl rfl (hp755987 rfl)

noncomputable def hp755989 := @BSN.binarySplit_of_base3 (BSN.cosOddP 32759495) (BSN.cosOddQ 16777216) 0 3 hp755985 hp633090 hp755984 rfl rfl rfl

noncomputable def hp755990 := hp755982 (BSN.cos_neg_of_bound 32759495 16777216 Bool.true 12502772 33554432 1 10890000 (hp755988 (hp755989 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp755991 := hp755940 (hp755943 (@Enclosure.Real.IsNear.neg hp755942 Bool.false 17367323 16777216 129 33554432 (hp755966 rfl))) (@hp755967 12502772 33554432 5348758864 730815528960000 3125693 8388608 334297429 45675970560000 (hp755990 rfl) rfl)

noncomputable def hp755992 := @hp755915 33554432 54284919929839 140737488355328 552289934842339 61305249927580876800 536161894297153063429 4722366482869645213696 124511599251169768447 hp755739 (hp755933 rfl) (@hp755936 Bool.false 54284919929839 140737488355328 552289934842339 61305249927580876800 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755743 (Enclosure.sfrac Bool.false 11 1)) (hp755937 rfl (hp755746 rfl rfl))) (hp755991 rfl))

noncomputable def hp755993 := @hp755740 35497466644823495963647 hp755739 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 836975 1000))) (@hp755745 35497466644823495963647 hp755739 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 836975 1000) 11 (hp755746 rfl rfl)) (@hp755749 35497466644823495963647 hp755739 hp755914 (hp755992 rfl) rfl rfl))

theorem hd5033 : hp755738 hp755739 := hp755993

noncomputable def hp755994 := nat_lit 19540764584093979846146119

noncomputable def hp755995 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 837617 1000)) Bool.true 15461606859136740593409 37778931862957161709568 hp755994

noncomputable def hp755996 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 837617 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 837617 1000)) Bool.true 15461606859136740593409 37778931862957161709568

noncomputable def hp755997 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 837617 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp755998 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp755997 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp755999 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 837617 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756000 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp755998 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp756001 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 837617 1000)) hp756000 Bool.true 15461606859136740593409 37778931862957161709568

noncomputable def hp756002 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 837617 1000) 837617 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl

noncomputable def hp756003 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp755998 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp756004 := nat_lit 4150443487725098727545455509504

noncomputable def hp756005 := @hp756003 140386599 268435456 203255 268435456 4296050482869860856063 37778931862957161709568 71079312171399980546119 hp740088 hp756004 15461606859136740593409 37778931862957161709568

noncomputable def hp756006 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) 11)

noncomputable def hp756007 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) 11) hp756006

noncomputable def hp756008 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) 11)

noncomputable def hp756009 := @hp756008 140386599 536870912 203255 536870912 140386599 536870912 203255 536870912 150738962875416576 140386599 268435456

noncomputable def hp756010 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp756011 := hp756010 BSN.quadSignNeg 9 10 11 837617 1000 190 241 536870912 268435456 9007199254740992

noncomputable def hp756012 := hp756011 Bool.false 875043981295 3817 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp756013 := hp756012 Bool.false 29480706 174489 Bool.true 180755955 Bool.true 31943676 28296951008113761 1 Bool.false 506728432

noncomputable def hp756014 := hp756013 Bool.true Bool.false 31924831 Bool.true Bool.true 140386599 203255 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 506728432 536870912) BSN.abs_quadSignNeg

noncomputable def hp756015 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp756016 := hp756015 BSN.quadSignNeg 7 8 9 837617 1000 71 134 536870912 268435456 9007199254740992

noncomputable def hp756017 := hp756016 Bool.false 875043981295 3817 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp756018 := hp756017 Bool.false 142665579 142505 Bool.true 189310367 Bool.true 26575615 28296951008113761 1 Bool.false 185411559

noncomputable def hp756019 := hp756018 Bool.false Bool.false 536213287 Bool.true Bool.false 29480706 174489 BSN.abs_quadSignPos (BSN.cos_quad_nat3 71 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 185411559 536870912) BSN.abs_quadSignNeg

noncomputable def hp756020 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp756021 := hp756020 BSN.quadSignPos 5 6 7 837617 1000 82 0 536870912 268435456 9007199254740992

noncomputable def hp756022 := hp756021 Bool.false 875043981295 3817 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp756023 := hp756022 Bool.false 150306141 105898 Bool.false 151906778 Bool.true 16626989 28296951008113761 1 Bool.false 515523017

noncomputable def hp756024 := hp756023 Bool.true Bool.false 536613462 Bool.false Bool.false 142665579 142505 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 515523017 536870912) BSN.abs_quadSignPos

noncomputable def hp756025 := hp756010 BSN.quadSignPos 3 4 5 837617 1000 298 179 536870912 268435456 9007199254740992

noncomputable def hp756026 := hp756025 Bool.false 875043981295 3817 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp756027 := hp756026 Bool.false 227778343 62592 Bool.false 330400899 Bool.false 338955310 28296951008113761 1 Bool.false 438371884

noncomputable def hp756028 := hp756027 Bool.true Bool.false 316881535 Bool.false Bool.false 150306141 105898 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 298 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 438371884 536870912) BSN.abs_quadSignPos

noncomputable def hp756029 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp756030 := hp756029 BSN.quadSignPos 1 2 3 837617 1000 668 451 536870912 268435456 9007199254740992

noncomputable def hp756031 := hp756030 Bool.false 875043981295 3817 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp756032 := hp756031 Bool.true 446060048 3874 Bool.false 6787257 Bool.false 671605480 28296951008113761 1 Bool.false 536828009

noncomputable def hp756033 := hp756032 Bool.false Bool.false 509644973 Bool.false Bool.false 227778343 62592 BSN.abs_quadSignPos (BSN.cos_quad_nat0 668 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536828009 536870912) BSN.abs_quadSignPos

noncomputable def hp756034 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) 1) Bool.true

noncomputable def hp756035 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)))

noncomputable def hp756036 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000))) Bool.true 55757506 67108864

noncomputable def hp756037 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 109380497661) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 109380497661 67108864

noncomputable def hp756038 := nat_lit 91263190141871706882756077998256603289343854997790367948191

noncomputable def hp756039 := nat_lit 55993245106300334902986360100635471661717812374667264000

noncomputable def hp756040 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) Bool.false hp756038 hp756039 126806845904181478391

noncomputable def hp756041 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 837617 4000) (Real.log (Enclosure.sfrac Bool.false 2806409954756 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1675234))))))

noncomputable def hp756042 := nat_lit 197910595107489810643693312571360000

noncomputable def hp756043 := nat_lit 994639839047912042655254795786765094720

noncomputable def hp756044 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp756041 (Enclosure.sfrac Bool.false 837617 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 837617 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp756042 hp756043)) Bool.false

noncomputable def hp756045 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 837617 1000) 837617 1000 2806409954756 16000000 1675234

noncomputable def hp756046 := hp756045 4000 2000 hp756042 hp756043 (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl rfl rfl rfl

noncomputable def hp756047 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp756041 (Enclosure.sfrac Bool.false 837617 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 837617 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp756042 hp756043) 29361607351857239586871 18014398509481984000

noncomputable def hp756048 := nat_lit 29204220845398946202481944959442113052590033599292917743421120

noncomputable def hp756049 := @hp756047 126806845904181478391 hp738659 hp756042 hp756043 0 1 hp756048 hp756038 hp756039 126806845904181478391 hp738659

noncomputable def hp756050 := @Enclosure.Real.IsNear.subLit_ff_p (hp756041 (Enclosure.sfrac Bool.false 837617 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 837617 2000) (Real.log Real.pi)) 37998117212530566002743 18014398509481984000 10570228007348021 4356000000000000000000

noncomputable def hp756051 := nat_lit 1970424114597187638850742124544000

noncomputable def hp756052 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 837617 4000) (Real.log (Enclosure.sfrac Bool.false 2806409954756 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1675234))))))

noncomputable def hp756053 := @hp756052 (Enclosure.sfrac Bool.false 837617 2000) 45542700430688951498807 18014398509481984000 10570228007348021 4356000000000000000000 837617 2000 0

noncomputable def hp756054 := nat_lit 75996234425061132005486000

noncomputable def hp756055 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 837617 4000) (Real.log (Enclosure.sfrac Bool.false 2806409954756 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1675234))))) 45549771980194105826807

noncomputable def hp756056 := nat_lit 102553044344548444830908414959745499136

noncomputable def hp756057 := @hp756055 18014398509481984000 951838909709411 396000000000000000000 883943688144291 2251799813685248 200000001089 8712000000000000000 hp756056 45542700430688951498807 18014398509481984000 10570228007348021

noncomputable def hp756058 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 837617 4000) (Real.log (Enclosure.sfrac Bool.false 2806409954756 16000000)) 837617 4000 0 1 54380190445268071 4503599627370496

noncomputable def hp756059 := nat_lit 116780569756339021449003008

noncomputable def hp756060 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2806409954756) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp756059 hp617687

noncomputable def hp756061 := BSN.log_rat_reduce_isNear 2806409954756 16000000 17 5612819909512 4194304000000 78202183 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp756062 := nat_lit 315882192052636699233770663611297654568597828345978613037952308192855734374266827103040288292518660997120

noncomputable def hp756063 := nat_lit 2230942461033793144281876696162323148343151562855942876497292968703177668029803069505105688404758626304

noncomputable def hp756064 := nat_lit 6723927499512482136562460740436818191401474014464170584104243092604794733015725443916720668999680

noncomputable def hp756065 := BSN.log_dyadic_bound 709257954756 4903561954756 5 4 hp756062 268435456 87120000 hp756063 hp756064 78202183 5612819909512

noncomputable def hp756066 := hp756065 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp756067 := @BSN.binarySplit_of_base4 (BSN.artanhP 709257954756) (BSN.artanhQ 4903561954756) 0 4 hp756063 hp756062 hp756064 rfl rfl rfl

noncomputable def hp756068 := hp756061 rfl rfl rfl rfl (hp756066 (hp756067 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp756069 := @hp756058 12500018513 1089000000000000000 45549771980194105826807 18014398509481984000 951838909709411 396000000000000000000 (Enclosure.Real.IsNear.const Bool.false 837617 4000) (BSN.isNear_log_sfrac 2806409954756 16000000 54380190445268071 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp756060 1000001481040000 87120000000000000000000 54380190445268071 4503599627370496 12500018513 1089000000000000000 (hp756068 rfl rfl rfl) rfl)) rfl

noncomputable def hp756070 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1675234)))) 1 4

noncomputable def hp756071 := @hp756070 0 1 883943688144291 562949953421312 200000001089 2178000000000000000 883943688144291 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp756072 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1675234))) 884279719003555 562949953421312 1

noncomputable def hp756073 := @hp756072 2000000000000000 20029 33554432 1 10890000 29660228375666818547712 883943688144291 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp756074 := BSN.arctan_dyadic_bound_f 1000 1675234 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp756075 := hp756074 1 20029 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1675234) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1675234) 0 0 rfl)

noncomputable def hp756076 := hp756071 (hp756073 (hp756075 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp756077 := @hp756050 32173506396537 67108864000 2512851 536870912000 hp756051 29361607351857239586871 18014398509481984000 126806845904181478391 hp738659 (@hp756053 1 hp756054 37998117212530566002743 18014398509481984000 10570228007348021 4356000000000000000000 (@hp756057 4356000000000000000000 hp756069 hp756076 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 837617 2000) rfl rfl)

noncomputable def hp756078 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 837617 2000) (Real.log Real.pi) 837617 2000 0 1 38410761 33554432

noncomputable def hp756079 := hp756077 (@hp756078 3 268435456 32173506396537 67108864000 2512851 536870912000 (Enclosure.Real.IsNear.const Bool.false 837617 2000) hd4909 rfl) rfl

noncomputable def hp756080 := @hp756040 hp738659 109380497661 67108864 239 33554432 (@hp756044 hp756038 hp756039 126806845904181478391 hp738659 (hp756046 rfl rfl rfl rfl rfl) (hp756049 (hp756079 rfl) (Enclosure.Real.IsNear.const Bool.true hp756042 hp756043) rfl rfl)) rfl

noncomputable def hp756081 := nat_lit 9484131602196478874877952

noncomputable def hp756082 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 109380497661) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp756081) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp756083 := BSN.sin_reduce_arg_pos_rat_q1 109380497661 67108864 226375608064910080 72057594037927936 259 hp756081 hp617687 rfl rfl rfl rfl

noncomputable def hp756084 := nat_lit 356143498200775808718032005008889768043744477999968880629213946674643467665008119647489122560

noncomputable def hp756085 := nat_lit 108878509949646892936640241640431058478951981673016544310615604533004437389231303133389056

noncomputable def hp756086 := nat_lit 932580501509732451672948309870150599353221996315305041528581244597679455747819653157398405376

noncomputable def hp756087 := BSN.sin_dyadic_bound_f 134777616298 137438953472 3 2 67108864 21801270 hp756084 hp738039 hp756085 hp756086 hp738042

noncomputable def hp756088 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 134777616298) (BSN.sinEvenQ 137438953472) 0 2 hp756084 hp738039 hp756085 rfl rfl rfl

noncomputable def hp756089 := hp756087 hp756085 55757506 rfl rfl rfl rfl rfl rfl rfl rfl (hp756088 rfl)

noncomputable def hp756090 := @BSN.binarySplit_of_base2 (BSN.sinOddP 134777616298) (BSN.sinOddQ 137438953472) 0 2 hp756086 hp738042 hp756085 rfl rfl rfl

noncomputable def hp756091 := @BSN.sin_arg_round Bool.false 55757506 67108864 hp756081 hp617687 134777616298 137438953472 21801270 21780000 (hp756089 (hp756090 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756092 := hp756082 55757506 67108864 259 1000000000000000 21780000 10890000 hp756083 BSN.pi_near_15 hp756091 rfl rfl

noncomputable def hp756093 := @hp756037 239 33554432 Bool.true 55757506 67108864 1 10890000 hp756080 (Enclosure.sfrac_false_div 109380497661 67108864) (hp756092 rfl rfl) rfl

noncomputable def hp756094 := @hp756034 27878753 33554432 164766527 22837985280000 446060048 536870912 3874 536870912 (@hp756035 Bool.true 27878753 33554432 164766527 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000)) (@hp756036 2636264432 365407764480000 27878753 33554432 164766527 22837985280000 (hp756093 rfl) rfl))

noncomputable def hp756095 := @hp756040 hp738659 875043981295 536870912 3817 536870912 (@hp756044 hp756038 hp756039 126806845904181478391 hp738659 (hp756046 rfl rfl rfl rfl rfl) (hp756049 (hp756079 rfl) (Enclosure.Real.IsNear.const Bool.true hp756042 hp756043) rfl rfl)) rfl

noncomputable def hp756096 := hp756033 (BSN.cos_quad_nat3 451 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 509644973 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl rfl (hp756094 rfl) hp756095

noncomputable def hp756097 := nat_lit 2122155367669052869099234401

noncomputable def hp756098 := BSN.cos_dyadic_bound_f 6787257 536870912 2 1 536870912 268435456 hp756097 hp708767 hp756097 hp756097 hp708768

noncomputable def hp756099 := @BSN.binarySplit_of_base (BSN.cosEvenP 6787257) (BSN.cosEvenQ 536870912) 0 1 hp756097 hp708767 hp756097 rfl rfl rfl

noncomputable def hp756100 := hp756098 hp756097 536828009 rfl rfl rfl rfl rfl rfl rfl rfl (hp756099 rfl)

noncomputable def hp756101 := @BSN.binarySplit_of_base (BSN.cosOddP 6787257) (BSN.cosOddQ 536870912) 0 1 hp756097 hp708768 hp756097 rfl rfl rfl

noncomputable def hp756102 := nat_lit 72923348575792502801391125745053071326415774837946942441720784641419990717244024334179678032797211476518502400000

noncomputable def hp756103 := nat_lit 8421137790713617780429058140927267280231948254994704071093519943725853765053750116639410487296000000000000

noncomputable def hp756104 := nat_lit 364434320942263474751936575171924595522039531020746868375075517869575471324981975099119720478509302401728512000000

noncomputable def hp756105 := BSN.sin_dyadic_bound_f 671605480 536870912 4 3 536870912 268435456 hp756102 hp642702 hp756103 hp756104 hp642705

noncomputable def hp756106 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 671605480) (BSN.sinEvenQ 536870912) 0 3 hp756102 hp642702 hp756103 rfl rfl rfl

noncomputable def hp756107 := hp756105 hp756103 509644973 rfl rfl rfl rfl rfl rfl rfl rfl (hp756106 rfl)

noncomputable def hp756108 := @BSN.binarySplit_of_base3 (BSN.sinOddP 671605480) (BSN.sinOddQ 536870912) 0 3 hp756104 hp642705 hp756103 rfl rfl rfl

noncomputable def hp756109 := hp756096 hd4911 hd4913 hd4915 hd4917 hd4918 (hp756100 (hp756101 rfl) rfl rfl rfl rfl) (hp756107 (hp756108 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756110 := hp756028 (BSN.cos_quad_nat3 179 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 316881535 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl rfl (hp756109 rfl rfl rfl rfl rfl) hp756095

noncomputable def hp756111 := nat_lit 1663377184648714165417355052426344975197886692665058558826693419586725281

noncomputable def hp756112 := nat_lit 142013543072947799176118808392414589016193399381354366834743715472801

noncomputable def hp756113 := nat_lit 4989847526859996600653712919662250096415627691196412967746410771329230241

noncomputable def hp756114 := BSN.cos_dyadic_bound_f 330400899 536870912 3 2 536870912 268435456 hp756111 hp708868 hp756112 hp756113 hp708870

noncomputable def hp756115 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 330400899) (BSN.cosEvenQ 536870912) 0 2 hp756111 hp708868 hp756112 rfl rfl rfl

noncomputable def hp756116 := hp756114 hp756112 438371884 rfl rfl rfl rfl rfl rfl rfl rfl (hp756115 rfl)

noncomputable def hp756117 := @BSN.binarySplit_of_base2 (BSN.cosOddP 330400899) (BSN.cosOddQ 536870912) 0 2 hp756113 hp708870 hp756112 rfl rfl rfl

noncomputable def hp756118 := nat_lit 3316300447322815398640462883010327103027837351603981652037949227041440000

noncomputable def hp756119 := nat_lit 174236659010721878792718226440901608107778653121078801324144100000000

noncomputable def hp756120 := nat_lit 8685266693159451541968881245041380952945494755429184484897246980375200000

noncomputable def hp756121 := BSN.sin_dyadic_bound_f 338955310 536870912 3 2 536870912 268435456 hp756118 hp708845 hp756119 hp756120 hp708848

noncomputable def hp756122 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 338955310) (BSN.sinEvenQ 536870912) 0 2 hp756118 hp708845 hp756119 rfl rfl rfl

noncomputable def hp756123 := hp756121 hp756119 316881535 rfl rfl rfl rfl rfl rfl rfl rfl (hp756122 rfl)

noncomputable def hp756124 := @BSN.binarySplit_of_base2 (BSN.sinOddP 338955310) (BSN.sinOddQ 536870912) 0 2 hp756120 hp708848 hp756119 rfl rfl rfl

noncomputable def hp756125 := hp756110 hd4920 hd4922 hd4924 hd4926 hd4918 (hp756116 (hp756117 rfl) rfl rfl rfl rfl) (hp756123 (hp756124 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756126 := hp756024 (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536613462 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl rfl (hp756125 rfl rfl rfl rfl rfl) hp756095

noncomputable def hp756127 := nat_lit 74318860950607862217136196638268229962598852316035642609569127895081216

noncomputable def hp756128 := nat_lit 283541882411717776791211989179532635302769071343640598370352046336

noncomputable def hp756129 := nat_lit 222956015768058763215855007490826330822525951409964240547510642981150976

noncomputable def hp756130 := BSN.cos_dyadic_bound_f 151906778 536870912 3 2 536870912 268435456 hp756127 hp708868 hp756128 hp756129 hp708870

noncomputable def hp756131 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 151906778) (BSN.cosEvenQ 536870912) 0 2 hp756127 hp708868 hp756128 rfl rfl rfl

noncomputable def hp756132 := hp756130 hp756128 515523017 rfl rfl rfl rfl rfl rfl rfl rfl (hp756131 rfl)

noncomputable def hp756133 := @BSN.binarySplit_of_base2 (BSN.cosOddP 151906778) (BSN.cosOddQ 536870912) 0 2 hp756129 hp708870 hp756128 rfl rfl rfl

noncomputable def hp756134 := nat_lit 76428341922405257935131866641

noncomputable def hp756135 := BSN.cos_dyadic_bound_f 16626989 536870912 2 1 536870912 268435456 hp756134 hp708767 hp756134 hp756134 hp708768

noncomputable def hp756136 := @BSN.binarySplit_of_base (BSN.cosEvenP 16626989) (BSN.cosEvenQ 536870912) 0 1 hp756134 hp708767 hp756134 rfl rfl rfl

noncomputable def hp756137 := hp756135 hp756134 536613462 rfl rfl rfl rfl rfl rfl rfl rfl (hp756136 rfl)

noncomputable def hp756138 := @BSN.binarySplit_of_base (BSN.cosOddP 16626989) (BSN.cosOddQ 536870912) 0 1 hp756134 hp708768 hp756134 rfl rfl rfl

noncomputable def hp756139 := hp756126 hd4928 hd4930 hd4932 hd4934 hd4918 (hp756132 (hp756133 rfl) rfl rfl rfl rfl) (hp756137 (hp756138 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756140 := hp756019 (BSN.cos_quad_nat2 134 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536213287 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl rfl (hp756139 rfl rfl rfl rfl rfl) hp756095

noncomputable def hp756141 := nat_lit 1284391993559456561636842239246721

noncomputable def hp756142 := BSN.sin_dyadic_bound_f 189310367 536870912 2 1 536870912 268435456 hp756141 hp708890 hp756141 hp756141 hp708891

noncomputable def hp756143 := @BSN.binarySplit_of_base (BSN.sinEvenP 189310367) (BSN.sinEvenQ 536870912) 0 1 hp756141 hp708890 hp756141 rfl rfl rfl

noncomputable def hp756144 := hp756142 hp756141 185411559 rfl rfl rfl rfl rfl rfl rfl rfl (hp756143 rfl)

noncomputable def hp756145 := @BSN.binarySplit_of_base (BSN.sinOddP 189310367) (BSN.sinOddQ 536870912) 0 1 hp756141 hp708891 hp756141 rfl rfl rfl

noncomputable def hp756146 := nat_lit 498807866764593882757066650625

noncomputable def hp756147 := BSN.cos_dyadic_bound_f 26575615 536870912 2 1 536870912 268435456 hp756146 hp708767 hp756146 hp756146 hp708768

noncomputable def hp756148 := @BSN.binarySplit_of_base (BSN.cosEvenP 26575615) (BSN.cosEvenQ 536870912) 0 1 hp756146 hp708767 hp756146 rfl rfl rfl

noncomputable def hp756149 := hp756147 hp756146 536213287 rfl rfl rfl rfl rfl rfl rfl rfl (hp756148 rfl)

noncomputable def hp756150 := @BSN.binarySplit_of_base (BSN.cosOddP 26575615) (BSN.cosOddQ 536870912) 0 1 hp756146 hp708768 hp756146 rfl rfl rfl

noncomputable def hp756151 := hp756140 hd4936 hd4938 hd4940 hd4942 hd4918 (hp756144 (hp756145 rfl) rfl rfl rfl rfl) (hp756149 (hp756150 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756152 := hp756014 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 31924831 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl rfl (hp756151 rfl rfl rfl rfl rfl) hp756095

noncomputable def hp756153 := nat_lit 148991865039088871934321328693546748411588254418257120898107022446190625

noncomputable def hp756154 := nat_lit 1139569749605095771535347575377140639717409340543326578462625390625

noncomputable def hp756155 := nat_lit 446973315977767405611420915385489490953485328436090276041164142087790625

noncomputable def hp756156 := BSN.cos_dyadic_bound_f 180755955 536870912 3 2 536870912 268435456 hp756153 hp708868 hp756154 hp756155 hp708870

noncomputable def hp756157 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 180755955) (BSN.cosEvenQ 536870912) 0 2 hp756153 hp708868 hp756154 rfl rfl rfl

noncomputable def hp756158 := hp756156 hp756154 506728432 rfl rfl rfl rfl rfl rfl rfl rfl (hp756157 rfl)

noncomputable def hp756159 := @BSN.binarySplit_of_base2 (BSN.cosOddP 180755955) (BSN.cosOddQ 536870912) 0 2 hp756155 hp708870 hp756154 rfl rfl rfl

noncomputable def hp756160 := nat_lit 1041212968993230287725502136576

noncomputable def hp756161 := BSN.sin_dyadic_bound_f 31943676 536870912 2 1 536870912 268435456 hp756160 hp708890 hp756160 hp756160 hp708891

noncomputable def hp756162 := @BSN.binarySplit_of_base (BSN.sinEvenP 31943676) (BSN.sinEvenQ 536870912) 0 1 hp756160 hp708890 hp756160 rfl rfl rfl

noncomputable def hp756163 := hp756161 hp756160 31924831 rfl rfl rfl rfl rfl rfl rfl rfl (hp756162 rfl)

noncomputable def hp756164 := @BSN.binarySplit_of_base (BSN.sinOddP 31943676) (BSN.sinOddQ 536870912) 0 1 hp756160 hp708891 hp756160 rfl rfl rfl

noncomputable def hp756165 := hp756152 hd4944 hd4946 hd4961 hd4963 hd4918 (hp756158 (hp756159 rfl) rfl rfl rfl rfl) (hp756163 (hp756164 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756166 := @hp756009 203255 268435456 (hp756165 rfl rfl rfl rfl rfl) (hp756165 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp756167 := @hp756007 Bool.true 140386599 268435456 203255 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 837617 1000)) (Enclosure.sfrac Bool.false 837617 1000) 11) hp756166

noncomputable def hp756168 := @Enclosure.Real.IsNear.mulLit_tf hp755998 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1))) 4937459 16777216 1

noncomputable def hp756169 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp755997 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756170 := @hp756169 1 1 0 1 4937459 16777216 1 33554432 4937459 16777216 1

noncomputable def hp756171 := @Enclosure.Real.IsNear.of_eq (hp755997 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756172 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 837617 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756173 := @hp756171 (@Inv.inv Real Real.instInv (Real.sqrt hp755999)) Bool.false 4937459 16777216 1 33554432 (hp756172 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 837617 1000) 837617 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000))))

noncomputable def hp756174 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp755999)) Bool.false 19749836 67108864 2 67108864 4937459 16777216

noncomputable def hp756175 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp755999) Bool.false 228032257 67108864 7 67108864 228032257 67108864 7 67108864

noncomputable def hp756176 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 837617 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756177 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 837617 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756178 := @hp756177 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 837617 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8946341755219

noncomputable def hp756179 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 837617 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 837617 1000 0

noncomputable def hp756180 := @hp756179 1 10680707 67108864 1 67108864 8946341755219 67108864000 837617 67108864000 (Enclosure.Real.IsNear.const Bool.false 837617 1000) hd4949

noncomputable def hp756181 := @hp756178 67108864000 837617 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 837617 1000) 837617 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000))) (hp756180 rfl)

noncomputable def hp756182 := @hp756176 8946341755219 67108864000 837617 67108864000 387420564 387420602 33554432 hp756181 rfl rfl rfl

noncomputable def hp756183 := @Enclosure.Real.IsNear.recentre' hp755999 Bool.false 774841166 67108864 38 67108864 387420583 33554432 19 33554432 (hp756182 rfl rfl rfl)

noncomputable def hp756184 := @Enclosure.Real.IsNear.sqrt_image hp755999 387420583 33554432 19 33554432 114016125 114016132 33554432 (hp756183 rfl) rfl rfl

noncomputable def hp756185 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp755999) 228032257 67108864 7 67108864 9874917 9874919 33554432 (hp756175 (hp756184 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp756186 := @hp756170 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp756173 (@hp756174 1 33554432 (hp756185 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp756187 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756188 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp756189 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1))) (hp756187 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756188 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp756190 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 837617 1000) 837617 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl

noncomputable def hp756191 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756192 := @hp756191 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756188 (Enclosure.sfrac Bool.false 1 16)))) 70017207

noncomputable def hp756193 := @hp756192 67108864 269 67108864 12426851 33554432 86126701 11418992640000 870093398825157 2251799813685248 14335957289697727 1532631248189521920000

noncomputable def hp756194 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756195 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756196 := @hp756194 (@Neg.neg Real Real.instNeg hp756195) Bool.true 70017207 67108864 269 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756197 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756198 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp756199 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp756200 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 115119459) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp756201 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1))) Bool.false 16201623568310623109205

noncomputable def hp756202 := nat_lit 20509417317168807741755533

noncomputable def hp756203 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp756204 := @Enclosure.Real.IsNear.subLit_ff_p hp755999 (Enclosure.sfrac Bool.false 11 1) 387420583 33554432 19 33554432 11 1 0

noncomputable def hp756205 := @hp756203 500000000000000 18321831 33554432 19 33554432 16201623568310623109205 4722366482869645213696 hp756202 hp684593 hd4948 (@hp756204 1 18321831 18321831 33554432 19 33554432 (hp756183 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756206 := @hp756200 115119459 33554432 15 4194304 Bool.true 64321327 67108864 1 10890000 (@hp756201 4722366482869645213696 hp756202 hp684593 115119459 33554432 15 4194304 (hp756205 rfl) rfl) (Enclosure.sfrac_false_div 115119459 33554432)

noncomputable def hp756207 := nat_lit 1398652590430425215664128

noncomputable def hp756208 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 115119459) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp756207) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp756209 := BSN.sin_reduce_arg_pos_rat_q2 115119459 33554432 226375608064910080 72057594037927936 0 hp756207 hp619237 rfl rfl rfl rfl

noncomputable def hp756210 := nat_lit 2497124505184717069618123906657844084640321

noncomputable def hp756211 := BSN.cos_dyadic_bound_f 39752097519 137438953472 2 1 67108864 21801270 hp756210 hp755189 hp756210 hp756210 hp755190

noncomputable def hp756212 := @BSN.binarySplit_of_base (BSN.cosEvenP 39752097519) (BSN.cosEvenQ 137438953472) 0 1 hp756210 hp755189 hp756210 rfl rfl rfl

noncomputable def hp756213 := hp756211 hp756210 64321327 rfl rfl rfl rfl rfl rfl rfl rfl (hp756212 rfl)

noncomputable def hp756214 := @BSN.binarySplit_of_base (BSN.cosOddP 39752097519) (BSN.cosOddQ 137438953472) 0 1 hp756210 hp755190 hp756210 rfl rfl rfl

noncomputable def hp756215 := @BSN.cos_arg_round Bool.false 64321327 67108864 hp756207 hp619237 39752097519 137438953472 21801270 21780000 (hp756213 (hp756214 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756216 := hp756208 64321327 67108864 0 1000000000000000 21780000 10890000 hp756209 BSN.pi_near_15 hp756215 rfl rfl

noncomputable def hp756217 := @hp756198 64321327 67108864 10471519 2854748160000 (@hp756199 64321327 67108864 167544304 45675970560000 64321327 67108864 10471519 2854748160000 (hp756206 (hp756216 rfl rfl) rfl rfl) rfl)

noncomputable def hp756218 := @hp756197 64321327 67108864 10471519 2854748160000 35008469 35008738 33554432 hp756217 rfl rfl rfl

noncomputable def hp756219 := @Enclosure.Real.IsNear.recentre' hp756195 Bool.false 70017207 67108864 269 67108864 70017207 67108864 269 67108864 (hp756218 rfl rfl rfl)

noncomputable def hp756220 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756188 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp756221 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756188 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65437217)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp756222 := nat_lit 309018520696329734765866787725

noncomputable def hp756223 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756188 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp756222

noncomputable def hp756224 := nat_lit 35993059851823127750102212466292389

noncomputable def hp756225 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756188 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp756226 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp756227 := @hp756226 (Enclosure.sfrac Bool.false 1 16) 279089141212431 1125899906842624 1333764147 1125899906842624 1 16 0

noncomputable def hp756228 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)) 335689491192561

noncomputable def hp756229 := @hp756228 1125899906842624 696229939 1125899906842624 18321831 33554432 19 33554432 9364677610750913544192 279089141212431 1125899906842624 1333764147

noncomputable def hp756230 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)) 18321831 33554432 19

noncomputable def hp756231 := @hp756230 33554432 18321831 33554432 19 33554432 335689491192561 1125899906842624 696229939 1125899906842624 (@hp756204 1 18321831 18321831 33554432 19 33554432 (hp756183 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756232 := hp756231 (@hp756204 1 18321831 18321831 33554432 19 33554432 (hp756183 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756233 := @hp756229 1125899906842624 (hp756232 rfl) (@hp756204 1 18321831 18321831 33554432 19 33554432 (hp756183 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756234 := @hp756225 500000000000000 349457885390095 1125899906842624 1333764147 1125899906842624 hp756222 hp682141 hp756224 hp682143 hd4948 (@hp756227 1 5591326166241520 349457885390095 1125899906842624 1333764147 1125899906842624 (hp756233 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp756235 := @hp756221 65437217 33554432 125 16777216 Bool.true 12426851 33554432 1 10890000 (@hp756223 hp682141 hp756224 hp682143 65437217 33554432 125 16777216 (hp756234 rfl) rfl) (Enclosure.sfrac_true_div 65437217 33554432)

noncomputable def hp756236 := nat_lit 593132625546143335697757475046773094560478451086126870362789725080536795589885394626305191086125441

noncomputable def hp756237 := nat_lit 6164499897714176404242622318185268861217873895042998953421129165770209713341725720153217560961

noncomputable def hp756238 := nat_lit 3577829359256862226600792127125499525188800196461552857046377346623895037456431618571699578939371905

noncomputable def hp756239 := BSN.cos_dyadic_bound_t 65437217 33554432 4 3 33554432 10890000 hp756236 hp681868 hp756237 hp756238 hp681871

noncomputable def hp756240 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 65437217) (BSN.cosEvenQ 33554432) 0 3 hp756236 hp681868 hp756237 rfl rfl rfl

noncomputable def hp756241 := hp756239 hp756237 12426851 rfl rfl rfl rfl rfl rfl rfl rfl (hp756240 rfl)

noncomputable def hp756242 := @BSN.binarySplit_of_base3 (BSN.cosOddP 65437217) (BSN.cosOddQ 33554432) 0 3 hp756238 hp681871 hp756237 rfl rfl rfl

noncomputable def hp756243 := hp756235 (BSN.cos_neg_of_bound 65437217 33554432 Bool.true 12426851 33554432 1 10890000 (hp756241 (hp756242 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp756244 := hp756193 (hp756196 (@Enclosure.Real.IsNear.neg hp756195 Bool.false 70017207 67108864 269 67108864 (hp756219 rfl))) (@hp756220 12426851 33554432 1378027216 182703882240000 12426851 33554432 86126701 11418992640000 (hp756243 rfl) rfl)

noncomputable def hp756245 := @hp756168 33554432 870093398825157 2251799813685248 14335957289697727 1532631248189521920000 4296050482869860856063 37778931862957161709568 71079312171399980546119 hp740088 (hp756186 rfl) (@hp756189 Bool.false 870093398825157 2251799813685248 14335957289697727 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp755999 (Enclosure.sfrac Bool.false 11 1)) (hp756190 rfl (hp756002 rfl rfl))) (hp756244 rfl))

noncomputable def hp756246 := @hp755996 hp755994 hp740088 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 837617 1000))) (@hp756001 hp755994 hp740088 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 837617 1000) 11 (hp756002 rfl rfl)) (@hp756005 hp755994 hp740088 hp756167 (hp756245 rfl) rfl rfl))

theorem hd5034 : hp755995 hp740088 := hp756246

noncomputable def hp756247 := nat_lit 1305081000313955254095157

noncomputable def hp756248 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 839142 1000)) Bool.false 9880340082090028839003 9444732965739290427392 hp756247

noncomputable def hp756249 := nat_lit 1714219033281681212571648000

noncomputable def hp756250 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 839142 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 839142 1000)) Bool.false 9880340082090028839003 9444732965739290427392

noncomputable def hp756251 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 839142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756252 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp756251 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756253 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 839142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756254 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp756252 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp756255 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 839142 1000)) hp756254 Bool.false 9880340082090028839003 9444732965739290427392

noncomputable def hp756256 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 839142 1000) 839142 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl

noncomputable def hp756257 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp756252 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp756258 := nat_lit 2652233595370914324450920890368

noncomputable def hp756259 := @hp756257 250154981 268435456 203623 268435456 1078794150711329566811 9444732965739290427392 4751947605225996111157 hp756249 hp756258 9880340082090028839003 9444732965739290427392

noncomputable def hp756260 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) 11)

noncomputable def hp756261 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) 11) hp756260

noncomputable def hp756262 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) 11)

noncomputable def hp756263 := @hp756262 250154981 536870912 203623 536870912 250154981 536870912 203623 536870912 268601865581625344 250154981 268435456

noncomputable def hp756264 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp756265 := hp756264 BSN.quadSignPos 9 10 11 839142 1000 190 240 536870912 268435456 9007199254740992

noncomputable def hp756266 := hp756265 Bool.false 877047242597 3823 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp756267 := hp756266 Bool.false 416332383 174805 Bool.true 62685861 Bool.true 835221566 28296951008113761 1 Bool.false 533215419

noncomputable def hp756268 := hp756267 Bool.true Bool.false 8092983 Bool.false Bool.false 250154981 203623 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 190 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533215419 536870912) BSN.abs_quadSignPos

noncomputable def hp756269 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp756270 := hp756269 BSN.quadSignNeg 7 8 9 839142 1000 70 133 536870912 268435456 9007199254740992

noncomputable def hp756271 := hp756270 Bool.false 877047242597 3823 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp756272 := hp756271 Bool.false 624691941 142763 Bool.true 731861227 Bool.true 665558740 28296951008113761 1 Bool.false 110654796

noncomputable def hp756273 := hp756272 Bool.true Bool.false 507711541 Bool.true Bool.false 416332383 174805 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 110654796 536870912) BSN.abs_quadSignNeg

noncomputable def hp756274 := hp756264 BSN.quadSignPos 5 6 7 839142 1000 82 0 536870912 268435456 9007199254740992

noncomputable def hp756275 := hp756274 Bool.false 877047242597 3823 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp756276 := hp756275 Bool.false 536319506 106090 Bool.false 688204192 Bool.false 393462937 28296951008113761 1 Bool.false 152961739

noncomputable def hp756277 := hp756276 Bool.true Bool.false 399029039 Bool.false Bool.false 624691941 142763 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 82 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 152961739 536870912) BSN.abs_quadSignPos

noncomputable def hp756278 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp756279 := hp756278 BSN.quadSignPos 3 4 5 839142 1000 299 180 536870912 268435456 9007199254740992

noncomputable def hp756280 := hp756279 Bool.false 877047242597 3823 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp756281 := hp756280 Bool.false 144788101 62706 Bool.false 355349160 Bool.false 181209670 28296951008113761 1 Bool.false 329965350

noncomputable def hp756282 := hp756281 Bool.false Bool.false 506578362 Bool.false Bool.false 536319506 106090 BSN.abs_quadSignPos (BSN.cos_quad_nat3 299 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 329965350 536870912) BSN.abs_quadSignPos

noncomputable def hp756283 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp756284 := hp756283 BSN.quadSignNeg 1 2 3 839142 1000 669 453 536870912 268435456 9007199254740992

noncomputable def hp756285 := hp756284 Bool.false 877047242597 3823 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp756286 := hp756285 Bool.false 536870864 3882 Bool.false 599234623 Bool.false 88772281 28296951008113761 1 Bool.false 482336333

noncomputable def hp756287 := hp756286 Bool.true Bool.false 88368312 Bool.true Bool.false 144788101 62706 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 669 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 482336333 536870912) BSN.abs_quadSignNeg

noncomputable def hp756288 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) 1) Bool.false

noncomputable def hp756289 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)))

noncomputable def hp756290 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000))) Bool.false 67108858 67108864

noncomputable def hp756291 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 27407726331) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false 27407726331 16777216

noncomputable def hp756292 := nat_lit 80274225365464958592749486656101947048187576697941753993

noncomputable def hp756293 := nat_lit 49138626163889214582759950394443306947585488453632000

noncomputable def hp756294 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) Bool.false hp756292 hp756293 63518484967308001733

noncomputable def hp756295 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 839142 4000) (Real.log (Enclosure.sfrac Bool.false 2816638184656 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1678284))))))

noncomputable def hp756296 := nat_lit 199718787511032945724668700431360000

noncomputable def hp756297 := nat_lit 1005554703340301173841088606309289758720

noncomputable def hp756298 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp756295 (Enclosure.sfrac Bool.false 839142 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 839142 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp756296 hp756297)) Bool.false

noncomputable def hp756299 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 839142 1000) 839142 1000 2816638184656 16000000 1678284

noncomputable def hp756300 := hp756299 4000 2000 hp756296 hp756297 (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl rfl rfl rfl

noncomputable def hp756301 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp756295 (Enclosure.sfrac Bool.false 839142 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 839142 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp756296 hp756297) 14714412820226333564133 9007199254740992000

noncomputable def hp756302 := nat_lit 14796145219362501167815585380452710879921934136964624095989760

noncomputable def hp756303 := @hp756301 63518484967308001733 hp739631 hp756296 hp756297 0 1 hp756302 hp756292 hp756293 63518484967308001733 hp739631

noncomputable def hp756304 := @Enclosure.Real.IsNear.subLit_ff_p (hp756295 (Enclosure.sfrac Bool.false 839142 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 839142 2000) (Real.log Real.pi)) 19040529743298057559269 9007199254740992000 5294645267790173 2178000000000000000000

noncomputable def hp756305 := nat_lit 493733764396212734187018387456000

noncomputable def hp756306 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 839142 4000) (Real.log (Enclosure.sfrac Bool.false 2816638184656 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1678284))))))

noncomputable def hp756307 := @hp756306 (Enclosure.sfrac Bool.false 839142 2000) 22819689341808990313701 9007199254740992000 5294645267790173 2178000000000000000000 839142 2000 0

noncomputable def hp756308 := nat_lit 38081059486596115118538000

noncomputable def hp756309 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 839142 4000) (Real.log (Enclosure.sfrac Bool.false 2816638184656 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1678284))))) 22823225118977486581701

noncomputable def hp756310 := nat_lit 51385372208240723952206650132395982848

noncomputable def hp756311 := @hp756309 9007199254740992000 582738363057547 242000000000000000000 883944292124067 2251799813685248 200000001089 8712000000000000000 hp756310 22819689341808990313701 9007199254740992000 5294645267790173

noncomputable def hp756312 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 839142 4000) (Real.log (Enclosure.sfrac Bool.false 2816638184656 16000000)) 839142 4000 0 1 54396574403325031 4503599627370496

noncomputable def hp756313 := nat_lit 116815754038355860901593088

noncomputable def hp756314 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2816638184656) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp756313 hp617687

noncomputable def hp756315 := BSN.log_rat_reduce_isNear 2816638184656 16000000 17 5633276369312 4194304000000 79178743 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp756316 := nat_lit 321191967927397299244148504776473574845775205792144882004643968859812577233098234934869399375107451781120

noncomputable def hp756317 := nat_lit 2325369424794530868001396263709903292459704447586792705230256683951451382088962143961724140527082799104

noncomputable def hp756318 := nat_lit 7539958793477137725683360728009646407083686674543899958605007627697816017590871194226675867975680

noncomputable def hp756319 := BSN.log_dyadic_bound 719486184656 4913790184656 5 4 hp756316 268435456 87120000 hp756317 hp756318 79178743 5633276369312

noncomputable def hp756320 := hp756319 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp756321 := @BSN.binarySplit_of_base4 (BSN.artanhP 719486184656) (BSN.artanhQ 4913790184656) 0 4 hp756317 hp756316 hp756318 rfl rfl rfl

noncomputable def hp756322 := hp756315 rfl rfl rfl rfl (hp756320 (hp756321 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp756323 := @hp756312 12500018513 1089000000000000000 22823225118977486581701 9007199254740992000 582738363057547 242000000000000000000 (Enclosure.Real.IsNear.const Bool.false 839142 4000) (BSN.isNear_log_sfrac 2816638184656 16000000 54396574403325031 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp756314 1000001481040000 87120000000000000000000 54396574403325031 4503599627370496 12500018513 1089000000000000000 (hp756322 rfl rfl rfl) rfl)) rfl

noncomputable def hp756324 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1678284)))) 1 4

noncomputable def hp756325 := @hp756324 0 1 883944292124067 562949953421312 200000001089 2178000000000000000 883944292124067 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp756326 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1678284))) 884279719003555 562949953421312 1

noncomputable def hp756327 := @hp756326 2000000000000000 19993 33554432 1 10890000 29660248641865141714944 883944292124067 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp756328 := BSN.arctan_dyadic_bound_f 1000 1678284 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp756329 := hp756328 1 19993 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1678284) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1678284) 0 0 rfl)

noncomputable def hp756330 := hp756325 (hp756327 (hp756329 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp756331 := @hp756304 16116041403531 33554432000 1258713 268435456000 hp756305 14714412820226333564133 9007199254740992000 63518484967308001733 hp739631 (@hp756307 1 hp756308 19040529743298057559269 9007199254740992000 5294645267790173 2178000000000000000000 (@hp756311 2178000000000000000000 hp756323 hp756330 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 839142 2000) rfl rfl)

noncomputable def hp756332 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 839142 2000) (Real.log Real.pi) 839142 2000 0 1 38410761 33554432

noncomputable def hp756333 := hp756331 (@hp756332 3 268435456 16116041403531 33554432000 1258713 268435456000 (Enclosure.Real.IsNear.const Bool.false 839142 2000) hd4909 rfl) rfl

noncomputable def hp756334 := @hp756294 hp739631 27407726331 16777216 479 67108864 (@hp756298 hp756292 hp756293 63518484967308001733 hp739631 (hp756300 rfl rfl rfl rfl rfl) (hp756303 (hp756333 rfl) (Enclosure.Real.IsNear.const Bool.true hp756296 hp756297) rfl rfl)) rfl

noncomputable def hp756335 := nat_lit 3797014815496576761331712

noncomputable def hp756336 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 27407726331) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp756335) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp756337 := BSN.sin_reduce_arg_pos_rat_q3 27407726331 16777216 226375608064910080 72057594037927936 259 hp756335 hp619230 rfl rfl rfl rfl

noncomputable def hp756338 := nat_lit 14366157680052871171652898817501802255236698556750058695394106992911286953529403100937494844387850132040311663158902563109752123559014874991521

noncomputable def hp756339 := nat_lit 10220444633400932291994357501859892526038496003727137148152790838385973011206988724013634475510082428737104923293743822451195531961813921

noncomputable def hp756340 := nat_lit 71741617759205124239545645263410552174717546606062474935053732371851424973310232316518288023961411737740953310336490364939564142328701262744481

noncomputable def hp756341 := BSN.sin_dyadic_bound_f 215835303577 137438953472 4 3 67108864 21801270 hp756338 hp737934 hp756339 hp756340 hp737937

noncomputable def hp756342 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215835303577) (BSN.sinEvenQ 137438953472) 0 3 hp756338 hp737934 hp756339 rfl rfl rfl

noncomputable def hp756343 := hp756341 hp756339 67108858 rfl rfl rfl rfl rfl rfl rfl rfl (hp756342 rfl)

noncomputable def hp756344 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215835303577) (BSN.sinOddQ 137438953472) 0 3 hp756340 hp737937 hp756339 rfl rfl rfl

noncomputable def hp756345 := @BSN.sin_arg_round Bool.false 67108858 67108864 hp756335 hp619230 215835303577 137438953472 21801270 21780000 (hp756343 (hp756344 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756346 := hp756336 67108858 67108864 259 1000000000000000 21780000 10890000 hp756337 BSN.pi_near_15 hp756345 rfl rfl

noncomputable def hp756347 := @hp756291 479 67108864 Bool.false 67108858 67108864 1 10890000 hp756334 (Enclosure.sfrac_false_div 27407726331 16777216) (hp756346 rfl rfl) rfl

noncomputable def hp756348 := @hp756288 33554429 33554432 330213679 45675970560000 536870864 536870912 3882 536870912 (@hp756289 Bool.false 33554429 33554432 330213679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000)) (@hp756290 5283418864 730815528960000 33554429 33554432 330213679 45675970560000 (hp756347 rfl) rfl))

noncomputable def hp756349 := @hp756294 hp739631 877047242597 536870912 3823 536870912 (@hp756298 hp756292 hp756293 63518484967308001733 hp739631 (hp756300 rfl rfl rfl rfl rfl) (hp756303 (hp756333 rfl) (Enclosure.Real.IsNear.const Bool.true hp756296 hp756297) rfl rfl)) rfl

noncomputable def hp756350 := hp756287 (BSN.cos_quad_nat1 453 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 88368312 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl rfl (hp756348 rfl) hp756349

noncomputable def hp756351 := nat_lit 32409454443664020997728279172845879670012278883460067721452009521635720705

noncomputable def hp756352 := nat_lit 16625518062929356315856891114744818295852380065574426455045753208634881

noncomputable def hp756353 := nat_lit 84854986989875312226681724771839145620410302746098771151447093718136716801

noncomputable def hp756354 := BSN.sin_dyadic_bound_f 599234623 536870912 3 2 536870912 268435456 hp756351 hp708845 hp756352 hp756353 hp708848

noncomputable def hp756355 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 599234623) (BSN.sinEvenQ 536870912) 0 2 hp756351 hp708845 hp756352 rfl rfl rfl

noncomputable def hp756356 := hp756354 hp756352 482336333 rfl rfl rfl rfl rfl rfl rfl rfl (hp756355 rfl)

noncomputable def hp756357 := @BSN.binarySplit_of_base2 (BSN.sinOddP 599234623) (BSN.sinOddQ 536870912) 0 2 hp756353 hp708848 hp756352 rfl rfl rfl

noncomputable def hp756358 := nat_lit 62102561961534486157973081447521

noncomputable def hp756359 := BSN.sin_dyadic_bound_f 88772281 536870912 2 1 536870912 268435456 hp756358 hp708890 hp756358 hp756358 hp708891

noncomputable def hp756360 := @BSN.binarySplit_of_base (BSN.sinEvenP 88772281) (BSN.sinEvenQ 536870912) 0 1 hp756358 hp708890 hp756358 rfl rfl rfl

noncomputable def hp756361 := hp756359 hp756358 88368312 rfl rfl rfl rfl rfl rfl rfl rfl (hp756360 rfl)

noncomputable def hp756362 := @BSN.binarySplit_of_base (BSN.sinOddP 88772281) (BSN.sinOddQ 536870912) 0 1 hp756358 hp708891 hp756358 rfl rfl rfl

noncomputable def hp756363 := hp756350 hd4911 hd4913 hd4915 hd4917 hd4918 (hp756356 (hp756357 rfl) rfl rfl rfl rfl) (hp756361 (hp756362 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756364 := hp756282 (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 506578362 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl rfl (hp756363 rfl rfl rfl rfl rfl) hp756349

noncomputable def hp756365 := nat_lit 4005991465774827179424323514346517709661210246088877432678523380695040000

noncomputable def hp756366 := nat_lit 254239101656438071661134511031300067451182555160053280676249600000000

noncomputable def hp756367 := nat_lit 10491470785150436951138157843603971896622534444191086523132180640563200000

noncomputable def hp756368 := BSN.sin_dyadic_bound_f 355349160 536870912 3 2 536870912 268435456 hp756365 hp708845 hp756366 hp756367 hp708848

noncomputable def hp756369 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 355349160) (BSN.sinEvenQ 536870912) 0 2 hp756365 hp708845 hp756366 rfl rfl rfl

noncomputable def hp756370 := hp756368 hp756366 329965350 rfl rfl rfl rfl rfl rfl rfl rfl (hp756369 rfl)

noncomputable def hp756371 := @BSN.binarySplit_of_base2 (BSN.sinOddP 355349160) (BSN.sinOddQ 536870912) 0 2 hp756367 hp708848 hp756366 rfl rfl rfl

noncomputable def hp756372 := nat_lit 150493454687125135085895144774333217435941697949317535221634895920800000

noncomputable def hp756373 := nat_lit 1162655246749627742311992133747805529763522989642453088224100000000

noncomputable def hp756374 := nat_lit 451478038750881906002200810338732156696765566801973320758728239562400000

noncomputable def hp756375 := BSN.cos_dyadic_bound_f 181209670 536870912 3 2 536870912 268435456 hp756372 hp708868 hp756373 hp756374 hp708870

noncomputable def hp756376 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 181209670) (BSN.cosEvenQ 536870912) 0 2 hp756372 hp708868 hp756373 rfl rfl rfl

noncomputable def hp756377 := hp756375 hp756373 506578362 rfl rfl rfl rfl rfl rfl rfl rfl (hp756376 rfl)

noncomputable def hp756378 := @BSN.binarySplit_of_base2 (BSN.cosOddP 181209670) (BSN.cosOddQ 536870912) 0 2 hp756374 hp708870 hp756373 rfl rfl rfl

noncomputable def hp756379 := hp756364 hd4920 hd4922 hd4924 hd4926 hd4918 (hp756370 (hp756371 rfl) rfl rfl rfl rfl) (hp756377 (hp756378 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756380 := hp756277 (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 399029039 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl rfl (hp756379 rfl rfl rfl rfl rfl) hp756349

noncomputable def hp756381 := nat_lit 30949353694616166239240557766854931120435154038902554230427333470809822538741825952553358502657179781578113417216

noncomputable def hp756382 := nat_lit 11287759927274304448594562502184470609699635863765940152391902115669881073144827697174213754141958456999936

noncomputable def hp756383 := nat_lit 187558495286089667164288626681363024229114339335331348822839898053744455506095820464628598859535832249556659077120

noncomputable def hp756384 := BSN.cos_dyadic_bound_f 688204192 536870912 4 3 536870912 268435456 hp756381 hp716712 hp756382 hp756383 hp716714

noncomputable def hp756385 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 688204192) (BSN.cosEvenQ 536870912) 0 3 hp756381 hp716712 hp756382 rfl rfl rfl

noncomputable def hp756386 := hp756384 hp756382 152961739 rfl rfl rfl rfl rfl rfl rfl rfl (hp756385 rfl)

noncomputable def hp756387 := @BSN.binarySplit_of_base3 (BSN.cosOddP 688204192) (BSN.cosOddQ 536870912) 0 3 hp756383 hp716714 hp756382 rfl rfl rfl

noncomputable def hp756388 := nat_lit 3345635841276540543899034445299172011447574140959228512255232359394980801

noncomputable def hp756389 := nat_lit 574421432009265000235552993305874781814256980902186420538038645699521

noncomputable def hp756390 := nat_lit 10035758680965603101696632229910904284779093908915881163924621000893543361

noncomputable def hp756391 := BSN.cos_dyadic_bound_f 393462937 536870912 3 2 536870912 268435456 hp756388 hp708868 hp756389 hp756390 hp708870

noncomputable def hp756392 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 393462937) (BSN.cosEvenQ 536870912) 0 2 hp756388 hp708868 hp756389 rfl rfl rfl

noncomputable def hp756393 := hp756391 hp756389 399029039 rfl rfl rfl rfl rfl rfl rfl rfl (hp756392 rfl)

noncomputable def hp756394 := @BSN.binarySplit_of_base2 (BSN.cosOddP 393462937) (BSN.cosOddQ 536870912) 0 2 hp756390 hp708870 hp756389 rfl rfl rfl

noncomputable def hp756395 := hp756380 hd4928 hd4930 hd4932 hd4934 hd4918 (hp756386 (hp756387 rfl) rfl rfl rfl rfl) (hp756393 (hp756394 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756396 := hp756273 (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 507711541 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl rfl (hp756395 rfl rfl rfl rfl rfl) hp756349

noncomputable def hp756397 := nat_lit 39599684616811668910874603912010448478361581145856956775349188679375529197355807296574498678301337821759929910801

noncomputable def hp756398 := nat_lit 23612657803322977313239349646652824980233522861922385093018155794431807365906070961701197830768209186850321

noncomputable def hp756399 := nat_lit 239909429704763538437536168764346321283598459697269979781241431945720427411587462344401515613396178567402685531665

noncomputable def hp756400 := BSN.cos_dyadic_bound_f 731861227 536870912 4 3 536870912 268435456 hp756397 hp716712 hp756398 hp756399 hp716714

noncomputable def hp756401 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 731861227) (BSN.cosEvenQ 536870912) 0 3 hp756397 hp716712 hp756398 rfl rfl rfl

noncomputable def hp756402 := hp756400 hp756398 110654796 rfl rfl rfl rfl rfl rfl rfl rfl (hp756401 rfl)

noncomputable def hp756403 := @BSN.binarySplit_of_base3 (BSN.cosOddP 731861227) (BSN.cosOddQ 536870912) 0 3 hp756399 hp716714 hp756398 rfl rfl rfl

noncomputable def hp756404 := nat_lit 70330345701000775735423802304760237222047636016812807281725802151066580744982673421218793361456054217107046400000

noncomputable def hp756405 := nat_lit 7555038653794961196897622235241509506857261977410610150829261500943557033569768089514998501376000000000000

noncomputable def hp756406 := nat_lit 351482040364356721197124858741509460262145867930514742632118884498865570649403130717512369435627991322591232000000

noncomputable def hp756407 := BSN.sin_dyadic_bound_f 665558740 536870912 4 3 536870912 268435456 hp756404 hp642702 hp756405 hp756406 hp642705

noncomputable def hp756408 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 665558740) (BSN.sinEvenQ 536870912) 0 3 hp756404 hp642702 hp756405 rfl rfl rfl

noncomputable def hp756409 := hp756407 hp756405 507711541 rfl rfl rfl rfl rfl rfl rfl rfl (hp756408 rfl)

noncomputable def hp756410 := @BSN.binarySplit_of_base3 (BSN.sinOddP 665558740) (BSN.sinOddQ 536870912) 0 3 hp756406 hp642705 hp756405 rfl rfl rfl

noncomputable def hp756411 := hp756396 hd4936 hd4938 hd4940 hd4942 hd4918 (hp756402 (hp756403 rfl) rfl rfl rfl rfl) (hp756409 (hp756410 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756412 := hp756268 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 8092983 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl rfl (hp756411 rfl rfl rfl rfl rfl) hp756349

noncomputable def hp756413 := nat_lit 15441105183912456990237418765041

noncomputable def hp756414 := BSN.cos_dyadic_bound_f 62685861 536870912 2 1 536870912 268435456 hp756413 hp708767 hp756413 hp756413 hp708768

noncomputable def hp756415 := @BSN.binarySplit_of_base (BSN.cosEvenP 62685861) (BSN.cosEvenQ 536870912) 0 1 hp756413 hp708767 hp756413 rfl rfl rfl

noncomputable def hp756416 := hp756414 hp756413 533215419 rfl rfl rfl rfl rfl rfl rfl rfl (hp756415 rfl)

noncomputable def hp756417 := @BSN.binarySplit_of_base (BSN.cosOddP 62685861) (BSN.cosOddQ 536870912) 0 1 hp756413 hp708768 hp756413 rfl rfl rfl

noncomputable def hp756418 := nat_lit 67267283800947016609595802659254996486781983863104019588989635771902081964832904186019192014186749701275938983936

noncomputable def hp756419 := nat_lit 115244549631571036630976900249242090355084845244286205391017720194831939427578249603833317298283102834528256

noncomputable def hp756420 := nat_lit 407142307205992788776012943638663035412205391978012824795040162591105264152303578353347515685612077414279048335360

noncomputable def hp756421 := BSN.cos_dyadic_bound_f 835221566 536870912 4 3 536870912 268435456 hp756418 hp716712 hp756419 hp756420 hp716714

noncomputable def hp756422 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 835221566) (BSN.cosEvenQ 536870912) 0 3 hp756418 hp716712 hp756419 rfl rfl rfl

noncomputable def hp756423 := hp756421 hp756419 8092983 rfl rfl rfl rfl rfl rfl rfl rfl (hp756422 rfl)

noncomputable def hp756424 := @BSN.binarySplit_of_base3 (BSN.cosOddP 835221566) (BSN.cosOddQ 536870912) 0 3 hp756420 hp716714 hp756419 rfl rfl rfl

noncomputable def hp756425 := hp756412 hd4944 hd4946 hd4961 hd4963 hd4918 (hp756416 (hp756417 rfl) rfl rfl rfl rfl) (hp756423 (hp756424 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756426 := @hp756263 203623 268435456 (hp756425 rfl rfl rfl rfl rfl) (hp756425 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp756427 := @hp756261 Bool.false 250154981 268435456 203623 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 839142 1000)) (Enclosure.sfrac Bool.false 839142 1000) 11) hp756426

noncomputable def hp756428 := @Enclosure.Real.IsNear.mulLit_tf hp756252 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1))) 19740857 67108864 1

noncomputable def hp756429 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp756251 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756430 := @hp756429 1 1 0 1 19740857 67108864 1 67108864 19740857 67108864 1

noncomputable def hp756431 := @Enclosure.Real.IsNear.of_eq (hp756251 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756432 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 839142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756433 := @hp756431 (@Inv.inv Real Real.instInv (Real.sqrt hp756253)) Bool.false 19740857 67108864 1 67108864 (hp756432 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 839142 1000) 839142 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000))))

noncomputable def hp756434 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp756253)) Bool.false 19740857 67108864 1 67108864 19740857 67108864

noncomputable def hp756435 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp756253) Bool.false 228135978 67108864 6 67108864 114067989 33554432 3 33554432

noncomputable def hp756436 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 839142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756437 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 839142 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756438 := @hp756437 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 839142 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4481314916697

noncomputable def hp756439 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 839142 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 839142 1000 0

noncomputable def hp756440 := @hp756439 1 10680707 67108864 1 67108864 4481314916697 33554432000 419571 33554432000 (Enclosure.Real.IsNear.const Bool.false 839142 1000) hd4949

noncomputable def hp756441 := @hp756438 33554432000 419571 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 839142 1000) 839142 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000))) (hp756440 rfl)

noncomputable def hp756442 := @hp756436 4481314916697 33554432000 419571 33554432000 387773081 387773118 33554432 hp756441 rfl rfl rfl

noncomputable def hp756443 := @Enclosure.Real.IsNear.recentre' hp756253 Bool.false 775546199 67108864 37 67108864 775546199 67108864 37 67108864 (hp756442 rfl rfl rfl)

noncomputable def hp756444 := @Enclosure.Real.IsNear.sqrt_image hp756253 775546199 67108864 37 67108864 114067986 114067992 33554432 (hp756443 rfl) rfl rfl

noncomputable def hp756445 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp756253) 114067989 33554432 3 33554432 9870428 9870429 33554432 (hp756435 (hp756444 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp756446 := @hp756430 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp756433 (@hp756434 1 67108864 (hp756445 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp756447 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756448 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp756449 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1))) (hp756447 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756448 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp756450 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 839142 1000) 839142 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl

noncomputable def hp756451 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756452 := @hp756451 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756448 (Enclosure.sfrac Bool.false 1 16)))) 4473631

noncomputable def hp756453 := @hp756452 4194304 137 33554432 12215533 33554432 84765451 11418992640000 54647787110323 140737488355328 1441283564837599 153263124818952192000

noncomputable def hp756454 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756455 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756456 := @hp756454 (@Neg.neg Real Real.instNeg hp756455) Bool.true 4473631 4194304 137 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756457 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756458 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp756459 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp756460 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 234668771) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp756461 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1))) Bool.false 33026693519749479610725

noncomputable def hp756462 := nat_lit 998484790455452528987809219

noncomputable def hp756463 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp756464 := @Enclosure.Real.IsNear.subLit_ff_p hp756253 (Enclosure.sfrac Bool.false 11 1) 775546199 67108864 37 67108864 11 1 0

noncomputable def hp756465 := @hp756463 500000000000000 37348695 67108864 37 67108864 33026693519749479610725 9444732965739290427392 hp756462 hp738031 hd4948 (@hp756464 1 37348695 37348695 67108864 37 67108864 (hp756443 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756466 := @hp756460 234668771 67108864 117 33554432 Bool.true 62918684 67108864 1 10890000 (@hp756461 9444732965739290427392 hp756462 hp738031 234668771 67108864 117 33554432 (hp756465 rfl) rfl) (Enclosure.sfrac_false_div 234668771 67108864)

noncomputable def hp756467 := nat_lit 3435714279104244793475072

noncomputable def hp756468 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 234668771) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp756467) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp756469 := BSN.sin_reduce_arg_pos_rat_q2 234668771 67108864 226375608064910080 72057594037927936 0 hp756467 hp617687 rfl rfl rfl rfl

noncomputable def hp756470 := nat_lit 5682624471808749993974278563419591175236161

noncomputable def hp756471 := BSN.cos_dyadic_bound_f 48824436463 137438953472 2 1 67108864 21801270 hp756470 hp755189 hp756470 hp756470 hp755190

noncomputable def hp756472 := @BSN.binarySplit_of_base (BSN.cosEvenP 48824436463) (BSN.cosEvenQ 137438953472) 0 1 hp756470 hp755189 hp756470 rfl rfl rfl

noncomputable def hp756473 := hp756471 hp756470 62918684 rfl rfl rfl rfl rfl rfl rfl rfl (hp756472 rfl)

noncomputable def hp756474 := @BSN.binarySplit_of_base (BSN.cosOddP 48824436463) (BSN.cosOddQ 137438953472) 0 1 hp756470 hp755190 hp756470 rfl rfl rfl

noncomputable def hp756475 := @BSN.cos_arg_round Bool.false 62918684 67108864 hp756467 hp617687 48824436463 137438953472 21801270 21780000 (hp756473 (hp756474 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756476 := hp756468 62918684 67108864 0 1000000000000000 21780000 10890000 hp756469 BSN.pi_near_15 hp756475 rfl rfl

noncomputable def hp756477 := @hp756458 15729671 16777216 81730277 22837985280000 (@hp756459 62918684 67108864 1307684432 365407764480000 15729671 16777216 81730277 22837985280000 (hp756466 (hp756476 rfl rfl) rfl rfl) rfl)

noncomputable def hp756478 := @hp756457 15729671 16777216 81730277 22837985280000 35788911 35789185 33554432 hp756477 rfl rfl rfl

noncomputable def hp756479 := @Enclosure.Real.IsNear.recentre' hp756455 Bool.false 71578096 67108864 274 67108864 4473631 4194304 137 33554432 (hp756478 rfl rfl rfl)

noncomputable def hp756480 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756448 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp756481 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756448 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 130420055)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp756482 := nat_lit 1231782593971180426405100594605

noncomputable def hp756483 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756448 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp756482

noncomputable def hp756484 := nat_lit 141591424720870819629789941109161401

noncomputable def hp756485 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756448 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp756486 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp756487 := @hp756486 (Enclosure.sfrac Bool.false 1 16) 1111503475129455 4503599627370496 5246832767 4503599627370496 1 16 0

noncomputable def hp756488 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)) 1394925018203025

noncomputable def hp756489 := @hp756488 4503599627370496 2763804799 4503599627370496 37348695 67108864 37 67108864 74591735547989977989120 1111503475129455 4503599627370496 5246832767

noncomputable def hp756490 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)) 37348695 67108864 37

noncomputable def hp756491 := @hp756490 67108864 37348695 67108864 37 67108864 1394925018203025 4503599627370496 2763804799 4503599627370496 (@hp756464 1 37348695 37348695 67108864 37 67108864 (hp756443 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756492 := hp756491 (@hp756464 1 37348695 37348695 67108864 37 67108864 (hp756443 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756493 := @hp756489 4503599627370496 (hp756492 rfl) (@hp756464 1 37348695 37348695 67108864 37 67108864 (hp756443 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756494 := @hp756485 500000000000000 1392978451840111 4503599627370496 5246832767 4503599627370496 hp756482 hp627574 hp756484 hp738055 hd4948 (@hp756487 1 22287655229441776 1392978451840111 4503599627370496 5246832767 4503599627370496 (hp756493 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp756495 := @hp756481 130420055 67108864 123 16777216 Bool.true 12215533 33554432 1 10890000 (@hp756483 hp627574 hp756484 hp738055 130420055 67108864 123 16777216 (hp756494 rfl) rfl) (Enclosure.sfrac_true_div 130420055 67108864)

noncomputable def hp756496 := nat_lit 2395624071318543947819499590913502361882784853992067239352724919097946145566700183027753765146154390625

noncomputable def hp756497 := nat_lit 24217680662682363898827531657435028610616490410283468646416773354381025429886886799869316650390625

noncomputable def hp756498 := nat_lit 14451756346250573948957769728829955128406001502190369430791161960802750180696031139628635457005507990625

noncomputable def hp756499 := BSN.cos_dyadic_bound_t 130420055 67108864 4 3 33554432 10890000 hp756496 hp745658 hp756497 hp756498 hp745661

noncomputable def hp756500 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 130420055) (BSN.cosEvenQ 67108864) 0 3 hp756496 hp745658 hp756497 rfl rfl rfl

noncomputable def hp756501 := hp756499 hp756497 12215533 rfl rfl rfl rfl rfl rfl rfl rfl (hp756500 rfl)

noncomputable def hp756502 := @BSN.binarySplit_of_base3 (BSN.cosOddP 130420055) (BSN.cosOddQ 67108864) 0 3 hp756498 hp745661 hp756497 rfl rfl rfl

noncomputable def hp756503 := hp756495 (BSN.cos_neg_of_bound 130420055 67108864 Bool.true 12215533 33554432 1 10890000 (hp756501 (hp756502 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp756504 := hp756453 (hp756456 (@Enclosure.Real.IsNear.neg hp756455 Bool.false 4473631 4194304 137 33554432 (hp756479 rfl))) (@hp756480 12215533 33554432 1356247216 182703882240000 12215533 33554432 84765451 11418992640000 (hp756503 rfl) rfl)

noncomputable def hp756505 := @hp756428 67108864 54647787110323 140737488355328 1441283564837599 153263124818952192000 1078794150711329566811 9444732965739290427392 4751947605225996111157 hp756249 (hp756446 rfl) (@hp756449 Bool.false 54647787110323 140737488355328 1441283564837599 153263124818952192000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756253 (Enclosure.sfrac Bool.false 11 1)) (hp756450 rfl (hp756256 rfl rfl))) (hp756504 rfl))

noncomputable def hp756506 := @hp756250 hp756247 hp756249 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 839142 1000))) (@hp756255 hp756247 hp756249 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 839142 1000) 11 (hp756256 rfl rfl)) (@hp756259 hp756247 hp756249 hp756427 (hp756505 rfl) rfl rfl))

theorem hd5035 : hp756248 hp756249 := hp756506

noncomputable def hp756507 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 840426 1000)) Bool.true 6150540751447159970509 2361183241434822606848 198057872631613276426921

noncomputable def hp756508 := nat_lit 259730156557830486753280000

noncomputable def hp756509 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 840426 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 840426 1000)) Bool.true 6150540751447159970509 2361183241434822606848

noncomputable def hp756510 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 840426 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756511 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp756510 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756512 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 840426 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756513 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp756511 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp756514 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 840426 1000)) hp756513 Bool.true 6150540751447159970509 2361183241434822606848

noncomputable def hp756515 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 840426 1000) 840426 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl

noncomputable def hp756516 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp756511 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp756517 := nat_lit 825511605630650523294264983552

noncomputable def hp756518 := @hp756516 365017539 134217728 25491 33554432 270915704115713041715 2361183241434822606848 743210270001643786921 hp756508 hp756517 6150540751447159970509 2361183241434822606848

noncomputable def hp756519 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) 11)

noncomputable def hp756520 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) 11) hp756519

noncomputable def hp756521 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) 11)

noncomputable def hp756522 := @hp756521 730035078 536870912 203928 536870912 730035078 536870912 203928 536870912 783869196235702272 365017539 134217728

noncomputable def hp756523 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp756524 := hp756523 BSN.quadSignPos 9 10 11 840426 1000 189 240 536870912 268435456 9007199254740992

noncomputable def hp756525 := hp756524 Bool.false 878734500169 3829 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp756526 := hp756525 Bool.true 573436107 175066 Bool.true 806012333 Bool.true 800934516 28296951008113761 1 Bool.false 535575518

noncomputable def hp756527 := hp756526 Bool.true Bool.false 42336339 Bool.false Bool.true 730035078 203928 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535575518 536870912) BSN.abs_quadSignPos

noncomputable def hp756528 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp756529 := hp756528 BSN.quadSignNeg 7 8 9 840426 1000 70 133 536870912 268435456 9007199254740992

noncomputable def hp756530 := hp756529 Bool.false 878734500169 3829 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp756531 := hp756530 Bool.true 311850270 142975 Bool.true 478050567 Bool.true 492940886 28296951008113761 1 Bool.false 337730010

noncomputable def hp756532 := hp756531 Bool.true Bool.false 426540737 Bool.true Bool.true 573436107 175066 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 337730010 536870912) BSN.abs_quadSignNeg

noncomputable def hp756533 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp756534 := hp756533 BSN.quadSignPos 5 6 7 840426 1000 83 0 536870912 268435456 9007199254740992

noncomputable def hp756535 := hp756534 Bool.false 878734500169 3829 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp756536 := hp756535 Bool.true 466073557 106246 Bool.false 297011411 Bool.false 739322446 28296951008113761 1 Bool.false 282091027

noncomputable def hp756537 := hp756536 Bool.false Bool.false 103343329 Bool.false Bool.true 311850270 142975 BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 282091027 536870912) BSN.abs_quadSignPos

noncomputable def hp756538 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp756539 := hp756538 BSN.quadSignPos 3 4 5 840426 1000 300 180 536870912 268435456 9007199254740992

noncomputable def hp756540 := hp756539 Bool.false 878734500169 3829 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp756541 := hp756540 Bool.true 744879661 62796 Bool.false 243660618 Bool.false 759013709 28296951008113761 1 Bool.false 482520453

noncomputable def hp756542 := hp756541 Bool.false Bool.false 83955149 Bool.false Bool.true 466073557 106246 BSN.abs_quadSignPos (BSN.cos_quad_nat0 300 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 482520453 536870912) BSN.abs_quadSignPos

noncomputable def hp756543 := hp756533 BSN.quadSignNeg 1 2 3 840426 1000 671 454 536870912 268435456 9007199254740992

noncomputable def hp756544 := hp756543 Bool.false 878734500169 3829 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp756545 := hp756544 Bool.true 536870744 3882 Bool.false 122046863 Bool.false 175395135 28296951008113761 1 Bool.false 120998367

noncomputable def hp756546 := hp756545 Bool.false Bool.false 508474137 Bool.true Bool.true 744879661 62796 BSN.abs_quadSignPos (BSN.cos_quad_nat3 671 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 120998367 536870912) BSN.abs_quadSignNeg

noncomputable def hp756547 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) 1) Bool.true

noncomputable def hp756548 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)))

noncomputable def hp756549 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000))) Bool.true 67108843 67108864

noncomputable def hp756550 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 109841812521) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 109841812521 67108864

noncomputable def hp756551 := nat_lit 16233977282375260121399465856303705815425443051879961459

noncomputable def hp756552 := nat_lit 9918297491785654255407116310658562767736092072345600

noncomputable def hp756553 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) Bool.false hp756551 hp756552 63615363411595847699

noncomputable def hp756554 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 840426 4000) (Real.log (Enclosure.sfrac Bool.false 2825264445904 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1680852))))))

noncomputable def hp756555 := nat_lit 201251453044085235374847088020480000

noncomputable def hp756556 := nat_lit 1014821889681012274862314902701735546880

noncomputable def hp756557 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp756554 (Enclosure.sfrac Bool.false 840426 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 840426 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp756555 hp756556)) Bool.false

noncomputable def hp756558 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 840426 1000) 840426 1000 2825264445904 16000000 1680852

noncomputable def hp756559 := hp756558 4000 2000 hp756555 hp756556 (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl rfl rfl rfl

noncomputable def hp756560 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp756554 (Enclosure.sfrac Bool.false 840426 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 840426 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp756555 hp756556) 2948544060446257108951 1801439850948198400

noncomputable def hp756561 := nat_lit 2992246692687407945576349546633899055899217663322514496122880

noncomputable def hp756562 := @hp756560 63615363411595847699 hp739631 hp756555 hp756556 0 1 hp756561 hp756551 hp756552 63615363411595847699 hp739631

noncomputable def hp756563 := @Enclosure.Real.IsNear.subLit_ff_p (hp756554 (Enclosure.sfrac Bool.false 840426 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 840426 2000) (Real.log Real.pi)) 19075456765415677114163 9007199254740992000 5302670279675519 2178000000000000000000

noncomputable def hp756564 := nat_lit 494683605876239119084064604160000

noncomputable def hp756565 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 840426 4000) (Real.log (Enclosure.sfrac Bool.false 2825264445904 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1680852))))))

noncomputable def hp756566 := @hp756565 (Enclosure.sfrac Bool.false 840426 2000) 22860398985848153585459 9007199254740992000 5302670279675519 2178000000000000000000 840426 2000 0

noncomputable def hp756567 := nat_lit 38150913530831354228326000

noncomputable def hp756568 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 840426 4000) (Real.log (Enclosure.sfrac Bool.false 2825264445904 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1680852))))) 22863934765097024637459

noncomputable def hp756569 := nat_lit 51477042177103304574386331267295608832

noncomputable def hp756570 := @hp756568 9007199254740992000 1750890093134423 726000000000000000000 883944812217763 2251799813685248 200000001089 8712000000000000000 hp756569 22860398985848153585459 9007199254740992000 5302670279675519

noncomputable def hp756571 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 840426 4000) (Real.log (Enclosure.sfrac Bool.false 2825264445904 16000000)) 840426 4000 0 1 54410346098519143 4503599627370496

noncomputable def hp756572 := nat_lit 116845328528590456607473664

noncomputable def hp756573 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2825264445904) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp756572 hp617687

noncomputable def hp756574 := BSN.log_rat_reduce_isNear 2825264445904 16000000 17 5650528891808 4194304000000 79999600 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp756575 := nat_lit 325730655357588001099702939621825871558885364635281697319053963773990633661379492385388979960239641067520

noncomputable def hp756576 := nat_lit 2407305691096073945198068325479520409489874014107665164388298762689362725674116052945089982824116649984

noncomputable def hp756577 := nat_lit 8294246467372795160800269222111622568293457923539255034234250639408260679049411286617040386785280

noncomputable def hp756578 := BSN.log_dyadic_bound 728112445904 4922416445904 5 4 hp756575 268435456 87120000 hp756576 hp756577 79999600 5650528891808

noncomputable def hp756579 := hp756578 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp756580 := @BSN.binarySplit_of_base4 (BSN.artanhP 728112445904) (BSN.artanhQ 4922416445904) 0 4 hp756576 hp756575 hp756577 rfl rfl rfl

noncomputable def hp756581 := hp756574 rfl rfl rfl rfl (hp756579 (hp756580 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp756582 := @hp756571 12500018513 1089000000000000000 22863934765097024637459 9007199254740992000 1750890093134423 726000000000000000000 (Enclosure.Real.IsNear.const Bool.false 840426 4000) (BSN.isNear_log_sfrac 2825264445904 16000000 54410346098519143 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp756573 1000001481040000 87120000000000000000000 54410346098519143 4503599627370496 12500018513 1089000000000000000 (hp756581 rfl rfl rfl) rfl)) rfl

noncomputable def hp756583 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1680852)))) 1 4

noncomputable def hp756584 := @hp756583 0 1 883944812217763 562949953421312 200000001089 2178000000000000000 883944812217763 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp756585 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1680852))) 884279719003555 562949953421312 1

noncomputable def hp756586 := @hp756585 2000000000000000 19962 33554432 1 10890000 29660266093313697775616 883944812217763 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp756587 := BSN.arctan_dyadic_bound_f 1000 1680852 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp756588 := hp756587 1 19962 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1680852) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1680852) 0 0 rfl)

noncomputable def hp756589 := hp756584 (hp756586 (hp756588 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp756590 := @hp756563 16140701112093 33554432000 1260639 268435456000 hp756564 2948544060446257108951 1801439850948198400 63615363411595847699 hp739631 (@hp756566 1 hp756567 19075456765415677114163 9007199254740992000 5302670279675519 2178000000000000000000 (@hp756570 2178000000000000000000 hp756582 hp756589 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 840426 2000) rfl rfl)

noncomputable def hp756591 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 840426 2000) (Real.log Real.pi) 840426 2000 0 1 38410761 33554432

noncomputable def hp756592 := hp756590 (@hp756591 3 268435456 16140701112093 33554432000 1260639 268435456000 (Enclosure.Real.IsNear.const Bool.false 840426 2000) hd4909 rfl) rfl

noncomputable def hp756593 := @hp756553 hp739631 109841812521 67108864 479 67108864 (@hp756557 hp756551 hp756552 63615363411595847699 hp739631 (hp756559 rfl rfl rfl rfl rfl) (hp756562 (hp756592 rfl) (Enclosure.Real.IsNear.const Bool.true hp756555 hp756556) rfl rfl)) rfl

noncomputable def hp756594 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 109841812521) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 7559940556831191990272) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp756595 := BSN.sin_reduce_arg_pos_rat_q2 109841812521 67108864 226375608064910080 72057594037927936 260 7559940556831191990272 hp617687 rfl rfl rfl rfl

noncomputable def hp756596 := BSN.cos_dyadic_bound_f 107433216 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp756597 := hp756596 1 67108843 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 107433216) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp756598 := hp756597 (@BSN.binarySplit_of_le (BSN.cosOddP 107433216) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp756599 := @BSN.cos_arg_round Bool.false 67108843 67108864 7559940556831191990272 hp617687 107433216 137438953472 21801270 21780000 hp756598 rfl

noncomputable def hp756600 := hp756594 67108843 67108864 260 1000000000000000 21780000 10890000 hp756595 BSN.pi_near_15 hp756599 rfl rfl

noncomputable def hp756601 := @hp756550 479 67108864 Bool.true 67108843 67108864 1 10890000 hp756593 (Enclosure.sfrac_false_div 109841812521 67108864) (hp756600 rfl rfl) rfl

noncomputable def hp756602 := @hp756547 67108843 67108864 330213679 45675970560000 536870744 536870912 3882 536870912 (@hp756548 Bool.true 67108843 67108864 330213679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000)) (@hp756549 5283418864 730815528960000 67108843 67108864 330213679 45675970560000 (hp756601 rfl) rfl))

noncomputable def hp756603 := @hp756553 hp739631 878734500169 536870912 3829 536870912 (@hp756557 hp756551 hp756552 63615363411595847699 hp739631 (hp756559 rfl rfl rfl rfl rfl) (hp756562 (hp756592 rfl) (Enclosure.Real.IsNear.const Bool.true hp756555 hp756556) rfl rfl)) rfl

noncomputable def hp756604 := hp756546 (BSN.cos_quad_nat2 454 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 508474137 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl rfl (hp756602 rfl) hp756603

noncomputable def hp756605 := nat_lit 221874036513679917300808999911361

noncomputable def hp756606 := BSN.sin_dyadic_bound_f 122046863 536870912 2 1 536870912 268435456 hp756605 hp708890 hp756605 hp756605 hp708891

noncomputable def hp756607 := @BSN.binarySplit_of_base (BSN.sinEvenP 122046863) (BSN.sinEvenQ 536870912) 0 1 hp756605 hp708890 hp756605 rfl rfl rfl

noncomputable def hp756608 := hp756606 hp756605 120998367 rfl rfl rfl rfl rfl rfl rfl rfl (hp756607 rfl)

noncomputable def hp756609 := @BSN.binarySplit_of_base (BSN.sinOddP 122046863) (BSN.sinOddQ 536870912) 0 1 hp756605 hp708891 hp756605 rfl rfl rfl

noncomputable def hp756610 := nat_lit 132087553289573396218223044134551576195375570053838392358283633257690625

noncomputable def hp756611 := nat_lit 895654153173709918328678980301739872334304677414602447590812890625

noncomputable def hp756612 := nat_lit 396260868560413841234832475045694125106382041552160347869955718147290625

noncomputable def hp756613 := BSN.cos_dyadic_bound_f 175395135 536870912 3 2 536870912 268435456 hp756610 hp708868 hp756611 hp756612 hp708870

noncomputable def hp756614 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 175395135) (BSN.cosEvenQ 536870912) 0 2 hp756610 hp708868 hp756611 rfl rfl rfl

noncomputable def hp756615 := hp756613 hp756611 508474137 rfl rfl rfl rfl rfl rfl rfl rfl (hp756614 rfl)

noncomputable def hp756616 := @BSN.binarySplit_of_base2 (BSN.cosOddP 175395135) (BSN.cosOddQ 536870912) 0 2 hp756612 hp708870 hp756611 rfl rfl rfl

noncomputable def hp756617 := hp756604 hd4911 hd4913 hd4915 hd4917 hd4918 (hp756608 (hp756609 rfl) rfl rfl rfl rfl) (hp756615 (hp756616 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756618 := hp756542 (BSN.cos_quad_nat0 180 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 83955149 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl rfl (hp756617 rfl rfl rfl rfl rfl) hp756603

noncomputable def hp756619 := nat_lit 491972822713682913842052945237288651255140576470431276297758404801126656

noncomputable def hp756620 := nat_lit 12424609017216794959708453624159212456049341237219689333363622994176

noncomputable def hp756621 := nat_lit 1475893618923014307936239418804617635340509630728819389514608487157391616

noncomputable def hp756622 := BSN.cos_dyadic_bound_f 243660618 536870912 3 2 536870912 268435456 hp756619 hp708868 hp756620 hp756621 hp708870

noncomputable def hp756623 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 243660618) (BSN.cosEvenQ 536870912) 0 2 hp756619 hp708868 hp756620 rfl rfl rfl

noncomputable def hp756624 := hp756622 hp756620 482520453 rfl rfl rfl rfl rfl rfl rfl rfl (hp756623 rfl)

noncomputable def hp756625 := @BSN.binarySplit_of_base2 (BSN.cosOddP 243660618) (BSN.cosOddQ 536870912) 0 2 hp756621 hp708870 hp756620 rfl rfl rfl

noncomputable def hp756626 := nat_lit 45826328518397538859818181597419953166563920228526550721824279134518636053730188843517276019101723130159767235761

noncomputable def hp756627 := nat_lit 36559095315118709853720492262815079374443128159165916962014121592563531805217275199374469006846227004796081

noncomputable def hp756628 := nat_lit 277573179197518642478743236807289397588199945445781050349337764515933453026050591896182947711561357585350544862385

noncomputable def hp756629 := BSN.cos_dyadic_bound_f 759013709 536870912 4 3 536870912 268435456 hp756626 hp716712 hp756627 hp756628 hp716714

noncomputable def hp756630 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 759013709) (BSN.cosEvenQ 536870912) 0 3 hp756626 hp716712 hp756627 rfl rfl rfl

noncomputable def hp756631 := hp756629 hp756627 83955149 rfl rfl rfl rfl rfl rfl rfl rfl (hp756630 rfl)

noncomputable def hp756632 := @BSN.binarySplit_of_base3 (BSN.cosOddP 759013709) (BSN.cosOddQ 536870912) 0 3 hp756628 hp716714 hp756627 rfl rfl rfl

noncomputable def hp756633 := hp756618 hd4920 hd4922 hd4924 hd4926 hd4918 (hp756624 (hp756625 rfl) rfl rfl rfl rfl) (hp756631 (hp756632 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756634 := hp756537 (BSN.cos_quad_nat0 0 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 103343329 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl rfl (hp756633 rfl rfl rfl rfl rfl) hp756603

noncomputable def hp756635 := nat_lit 1955092350133558467540241721436271189011728408221501627212029918520278305

noncomputable def hp756636 := nat_lit 60559890295565185936212628547140170746878703443038113651472096034081

noncomputable def hp756637 := nat_lit 5120381915289317452304355402363062506182841360774548866704642641302388001

noncomputable def hp756638 := BSN.sin_dyadic_bound_f 297011411 536870912 3 2 536870912 268435456 hp756635 hp708845 hp756636 hp756637 hp708848

noncomputable def hp756639 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 297011411) (BSN.sinEvenQ 536870912) 0 2 hp756635 hp708845 hp756636 rfl rfl rfl

noncomputable def hp756640 := hp756638 hp756636 282091027 rfl rfl rfl rfl rfl rfl rfl rfl (hp756639 rfl)

noncomputable def hp756641 := @BSN.binarySplit_of_base2 (BSN.sinOddP 297011411) (BSN.sinOddQ 536870912) 0 2 hp756637 hp708848 hp756636 rfl rfl rfl

noncomputable def hp756642 := nat_lit 41242904752499904029593175641009104288833187449743310482832189044433628497897222829437143353169248053340448362496

noncomputable def hp756643 := nat_lit 26668998081802563673887546573672053857493515456610285425063924923987325843347896275698966018582885863919616

noncomputable def hp756644 := nat_lit 249850512070496892380358927648372962811066781549671405457493922647179547938328767062756493505053564730007433646080

noncomputable def hp756645 := BSN.cos_dyadic_bound_f 739322446 536870912 4 3 536870912 268435456 hp756642 hp716712 hp756643 hp756644 hp716714

noncomputable def hp756646 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 739322446) (BSN.cosEvenQ 536870912) 0 3 hp756642 hp716712 hp756643 rfl rfl rfl

noncomputable def hp756647 := hp756645 hp756643 103343329 rfl rfl rfl rfl rfl rfl rfl rfl (hp756646 rfl)

noncomputable def hp756648 := @BSN.binarySplit_of_base3 (BSN.cosOddP 739322446) (BSN.cosOddQ 536870912) 0 3 hp756644 hp716714 hp756643 rfl rfl rfl

noncomputable def hp756649 := hp756634 hd4928 hd4930 hd4932 hd4934 hd4918 (hp756640 (hp756641 rfl) rfl rfl rfl rfl) (hp756647 (hp756648 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756650 := hp756532 (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 426540737 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl rfl (hp756649 rfl rfl rfl rfl rfl) hp756603

noncomputable def hp756651 := nat_lit 7291999209718369678267085903916872567465083492530095981884075197413846721

noncomputable def hp756652 := nat_lit 2727662927150453333999295064549615029106572279964739788792173163048641

noncomputable def hp756653 := nat_lit 21870542303300808128133259121621518472337037333030358466074641245915442881

noncomputable def hp756654 := BSN.cos_dyadic_bound_f 478050567 536870912 3 2 536870912 268435456 hp756651 hp708868 hp756652 hp756653 hp708870

noncomputable def hp756655 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 478050567) (BSN.cosEvenQ 536870912) 0 2 hp756651 hp708868 hp756652 rfl rfl rfl

noncomputable def hp756656 := hp756654 hp756652 337730010 rfl rfl rfl rfl rfl rfl rfl rfl (hp756655 rfl)

noncomputable def hp756657 := @BSN.binarySplit_of_base2 (BSN.cosOddP 478050567) (BSN.cosOddQ 536870912) 0 2 hp756653 hp708870 hp756652 rfl rfl rfl

noncomputable def hp756658 := nat_lit 14836884238759589431171933551822088829122716917936584585183939718028878080

noncomputable def hp756659 := nat_lit 3486251633107161360629092246780606275043989163450074503703382440960256

noncomputable def hp756660 := nat_lit 38852861932202465487056902676848778332780854040712135697713846166123602176

noncomputable def hp756661 := BSN.sin_dyadic_bound_f 492940886 536870912 3 2 536870912 268435456 hp756658 hp708845 hp756659 hp756660 hp708848

noncomputable def hp756662 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 492940886) (BSN.sinEvenQ 536870912) 0 2 hp756658 hp708845 hp756659 rfl rfl rfl

noncomputable def hp756663 := hp756661 hp756659 426540737 rfl rfl rfl rfl rfl rfl rfl rfl (hp756662 rfl)

noncomputable def hp756664 := @BSN.binarySplit_of_base2 (BSN.sinOddP 492940886) (BSN.sinOddQ 536870912) 0 2 hp756660 hp708848 hp756659 rfl rfl rfl

noncomputable def hp756665 := hp756650 hd4936 hd4938 hd4940 hd4942 hd4918 (hp756656 (hp756657 rfl) rfl rfl rfl rfl) (hp756663 (hp756664 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756666 := hp756527 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 42336339 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl rfl (hp756665 rfl rfl rfl rfl rfl) hp756603

noncomputable def hp756667 := nat_lit 151409813527844540204934180994218018409043866938437448467807864808345811621556668009586414326946074604014908371761

noncomputable def hp756668 := nat_lit 75179640610477674375200812136047353154434402644571220363114248753674838781054552343501285700876918463034161

noncomputable def hp756669 := nat_lit 756263862980401307605022789877301545967958349278600641691211860925541422779259707452720992240669487747859314275121

noncomputable def hp756670 := BSN.sin_dyadic_bound_f 806012333 536870912 4 3 536870912 268435456 hp756667 hp642702 hp756668 hp756669 hp642705

noncomputable def hp756671 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 806012333) (BSN.sinEvenQ 536870912) 0 3 hp756667 hp642702 hp756668 rfl rfl rfl

noncomputable def hp756672 := hp756670 hp756668 535575518 rfl rfl rfl rfl rfl rfl rfl rfl (hp756671 rfl)

noncomputable def hp756673 := @BSN.binarySplit_of_base3 (BSN.sinOddP 806012333) (BSN.sinOddQ 536870912) 0 3 hp756669 hp642705 hp756668 rfl rfl rfl

noncomputable def hp756674 := nat_lit 56852807494184496466410409396547912843256789617835634641127189163379894160921275534334230256267749390147529998336

noncomputable def hp756675 := nat_lit 69688981610410480427990629601207851930991238680856969531028665495709645119044944615819239664248589601734656

noncomputable def hp756676 := nat_lit 344230703641880717213402808625869194203842428488141673712253446694079008779963219007154112015626366031107362652160

noncomputable def hp756677 := BSN.cos_dyadic_bound_f 800934516 536870912 4 3 536870912 268435456 hp756674 hp716712 hp756675 hp756676 hp716714

noncomputable def hp756678 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 800934516) (BSN.cosEvenQ 536870912) 0 3 hp756674 hp716712 hp756675 rfl rfl rfl

noncomputable def hp756679 := hp756677 hp756675 42336339 rfl rfl rfl rfl rfl rfl rfl rfl (hp756678 rfl)

noncomputable def hp756680 := @BSN.binarySplit_of_base3 (BSN.cosOddP 800934516) (BSN.cosOddQ 536870912) 0 3 hp756676 hp716714 hp756675 rfl rfl rfl

noncomputable def hp756681 := hp756666 hd4944 hd4946 hd4961 hd4963 hd4918 (hp756672 (hp756673 rfl) rfl rfl rfl rfl) (hp756679 (hp756680 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756682 := @hp756522 25491 33554432 (hp756681 rfl rfl rfl rfl rfl) (hp756681 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp756683 := @hp756520 Bool.true 365017539 134217728 25491 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 840426 1000)) (Enclosure.sfrac Bool.false 840426 1000) 11) hp756682

noncomputable def hp756684 := @Enclosure.Real.IsNear.mulLit_tf hp756511 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1))) 308333 1048576 1

noncomputable def hp756685 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp756510 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756686 := @hp756685 1 1 0 1 308333 1048576 1 33554432 308333 1048576 1

noncomputable def hp756687 := @Enclosure.Real.IsNear.of_eq (hp756510 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756688 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 840426 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756689 := @hp756687 (@Inv.inv Real Real.instInv (Real.sqrt hp756512)) Bool.false 308333 1048576 1 33554432 (hp756688 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 840426 1000) 840426 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000))))

noncomputable def hp756690 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp756512)) Bool.false 19733312 67108864 2 67108864 308333 1048576

noncomputable def hp756691 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp756512) Bool.false 228223198 67108864 6 67108864 114111599 33554432 3 33554432

noncomputable def hp756692 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 840426 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756693 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 840426 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756694 := @hp756693 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 840426 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4488171930591

noncomputable def hp756695 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 840426 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 840426 1000 0

noncomputable def hp756696 := @hp756695 1 10680707 67108864 1 67108864 4488171930591 33554432000 420213 33554432000 (Enclosure.Real.IsNear.const Bool.false 840426 1000) hd4949

noncomputable def hp756697 := @hp756694 33554432000 420213 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 840426 1000) 840426 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000))) (hp756696 rfl)

noncomputable def hp756698 := @hp756692 4488171930591 33554432000 420213 33554432000 388069640 388069677 33554432 hp756697 rfl rfl rfl

noncomputable def hp756699 := @Enclosure.Real.IsNear.recentre' hp756512 Bool.false 776139317 67108864 37 67108864 776139317 67108864 37 67108864 (hp756698 rfl rfl rfl)

noncomputable def hp756700 := @Enclosure.Real.IsNear.sqrt_image hp756512 776139317 67108864 37 67108864 114111596 114111602 33554432 (hp756699 rfl) rfl rfl

noncomputable def hp756701 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp756512) 114111599 33554432 3 33554432 9866655 9866657 33554432 (hp756691 (hp756700 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp756702 := @hp756686 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp756689 (@hp756690 1 33554432 (hp756701 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp756703 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756704 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp756705 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1))) (hp756703 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756704 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp756706 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 840426 1000) 840426 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl

noncomputable def hp756707 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756708 := @hp756707 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756704 (Enclosure.sfrac Bool.false 1 16)))) 73198135

noncomputable def hp756709 := @hp756708 67108864 287 67108864 12003673 33554432 21361519 2854748160000 878646476749855 2251799813685248 150038644849581 15481123719086080000

noncomputable def hp756710 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756711 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756712 := @hp756710 (@Neg.neg Real Real.instNeg hp756711) Bool.true 73198135 67108864 287 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756713 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756714 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp756715 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp756716 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 238395441) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp756717 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1))) Bool.false 33551175738125430145215

noncomputable def hp756718 := nat_lit 39939391618421894952525883

noncomputable def hp756719 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp756720 := @Enclosure.Real.IsNear.subLit_ff_p hp756512 (Enclosure.sfrac Bool.false 11 1) 776139317 67108864 37 67108864 11 1 0

noncomputable def hp756721 := @hp756719 500000000000000 37941813 67108864 37 67108864 33551175738125430145215 9444732965739290427392 hp756718 hp754162 hd4948 (@hp756720 1 37941813 37941813 67108864 37 67108864 (hp756699 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756722 := @hp756716 238395441 67108864 117 33554432 Bool.true 61526153 67108864 1 10890000 (@hp756717 9444732965739290427392 hp756718 hp754162 238395441 67108864 117 33554432 (hp756721 rfl) rfl) (Enclosure.sfrac_false_div 238395441 67108864)

noncomputable def hp756723 := nat_lit 3972784027050894595981312

noncomputable def hp756724 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 238395441) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp756723) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp756725 := BSN.sin_reduce_arg_pos_rat_q2 238395441 67108864 226375608064910080 72057594037927936 0 hp756723 hp617687 rfl rfl rfl rfl

noncomputable def hp756726 := nat_lit 6089990601983307755209965268807282506948095542383723953348942955377860421448677115650860161

noncomputable def hp756727 := nat_lit 103209873172451878793554484798322221082015825867393417078459981963149868525102098506881

noncomputable def hp756728 := nat_lit 18269765386203578361872308697452250876402122595499437073212671946169654964608981142755566721

noncomputable def hp756729 := BSN.cos_dyadic_bound_f 56456656623 137438953472 3 2 67108864 21801270 hp756726 hp746621 hp756727 hp756728 hp746624

noncomputable def hp756730 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 56456656623) (BSN.cosEvenQ 137438953472) 0 2 hp756726 hp746621 hp756727 rfl rfl rfl

noncomputable def hp756731 := hp756729 hp756727 61526153 rfl rfl rfl rfl rfl rfl rfl rfl (hp756730 rfl)

noncomputable def hp756732 := @BSN.binarySplit_of_base2 (BSN.cosOddP 56456656623) (BSN.cosOddQ 137438953472) 0 2 hp756728 hp746624 hp756727 rfl rfl rfl

noncomputable def hp756733 := @BSN.cos_arg_round Bool.false 61526153 67108864 hp756723 hp617687 56456656623 137438953472 21801270 21780000 (hp756731 (hp756732 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756734 := hp756724 61526153 67108864 0 1000000000000000 21780000 10890000 hp756725 BSN.pi_near_15 hp756733 rfl rfl

noncomputable def hp756735 := @hp756714 61526153 67108864 81730277 22837985280000 (@hp756715 61526153 67108864 1307684432 365407764480000 61526153 67108864 81730277 22837985280000 (hp756722 (hp756734 rfl rfl) rfl rfl) rfl)

noncomputable def hp756736 := @hp756713 61526153 67108864 81730277 22837985280000 36598924 36599211 33554432 hp756735 rfl rfl rfl

noncomputable def hp756737 := @Enclosure.Real.IsNear.recentre' hp756711 Bool.false 73198135 67108864 287 67108864 73198135 67108864 287 67108864 (hp756736 rfl rfl rfl)

noncomputable def hp756738 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756704 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp756739 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756704 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 64982857)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp756740 := nat_lit 1227491467176098140970293693045

noncomputable def hp756741 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756704 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp756740

noncomputable def hp756742 := nat_lit 142775863324339277998462423736959981

noncomputable def hp756743 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756704 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp756744 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp756745 := @hp756744 (Enclosure.sfrac Bool.false 1 16) 1106650794803463 4503599627370496 5290723499 4503599627370496 1 16 0

noncomputable def hp756746 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)) 1439581173726969

noncomputable def hp756747 := @hp756746 4503599627370496 2807695531 4503599627370496 37941813 67108864 37 67108864 74266077683957505196032 1106650794803463 4503599627370496 5290723499

noncomputable def hp756748 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)) 37941813 67108864 37

noncomputable def hp756749 := @hp756748 67108864 37941813 67108864 37 67108864 1439581173726969 4503599627370496 2807695531 4503599627370496 (@hp756720 1 37941813 37941813 67108864 37 67108864 (hp756699 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756750 := hp756749 (@hp756720 1 37941813 37941813 67108864 37 67108864 (hp756699 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756751 := @hp756747 4503599627370496 (hp756750 rfl) (@hp756720 1 37941813 37941813 67108864 37 67108864 (hp756699 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756752 := @hp756743 500000000000000 1388125771514119 4503599627370496 5290723499 4503599627370496 hp756740 hp627574 hp756742 hp738055 hd4948 (@hp756745 1 22210012344225904 1388125771514119 4503599627370496 5290723499 4503599627370496 (hp756751 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp756753 := @hp756739 64982857 33554432 31 4194304 Bool.true 12003673 33554432 1 10890000 (@hp756741 hp627574 hp756742 hp738055 64982857 33554432 31 4194304 (hp756752 rfl) rfl) (Enclosure.sfrac_true_div 64982857 33554432)

noncomputable def hp756754 := nat_lit 576694199167692661140954489418765186072433616384885631342693011188395881067041151810613145036634081

noncomputable def hp756755 := nat_lit 5670033391711004761529230569518864317772867678339333813475195780528175590447393985218767992801

noncomputable def hp756756 := nat_lit 3479215615686789493342841952997521368901683061076072550337905500430800007770090660156380311464687585

noncomputable def hp756757 := BSN.cos_dyadic_bound_t 64982857 33554432 4 3 33554432 10890000 hp756754 hp681868 hp756755 hp756756 hp681871

noncomputable def hp756758 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 64982857) (BSN.cosEvenQ 33554432) 0 3 hp756754 hp681868 hp756755 rfl rfl rfl

noncomputable def hp756759 := hp756757 hp756755 12003673 rfl rfl rfl rfl rfl rfl rfl rfl (hp756758 rfl)

noncomputable def hp756760 := @BSN.binarySplit_of_base3 (BSN.cosOddP 64982857) (BSN.cosOddQ 33554432) 0 3 hp756756 hp681871 hp756755 rfl rfl rfl

noncomputable def hp756761 := hp756753 (BSN.cos_neg_of_bound 64982857 33554432 Bool.true 12003673 33554432 1 10890000 (hp756759 (hp756760 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp756762 := hp756709 (hp756712 (@Enclosure.Real.IsNear.neg hp756711 Bool.false 73198135 67108864 287 67108864 (hp756737 rfl))) (@hp756738 12003673 33554432 341784304 45675970560000 12003673 33554432 21361519 2854748160000 (hp756761 rfl) rfl)

noncomputable def hp756763 := @hp756684 33554432 878646476749855 2251799813685248 150038644849581 15481123719086080000 270915704115713041715 2361183241434822606848 743210270001643786921 hp756508 (hp756702 rfl) (@hp756705 Bool.false 878646476749855 2251799813685248 150038644849581 15481123719086080000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756512 (Enclosure.sfrac Bool.false 11 1)) (hp756706 rfl (hp756515 rfl rfl))) (hp756762 rfl))

noncomputable def hp756764 := @hp756509 198057872631613276426921 hp756508 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 840426 1000))) (@hp756514 198057872631613276426921 hp756508 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 840426 1000) 11 (hp756515 rfl rfl)) (@hp756518 198057872631613276426921 hp756508 hp756683 (hp756763 rfl) rfl rfl))

theorem hd5036 : hp756507 hp756508 := hp756764

noncomputable def hp756765 := nat_lit 1964019008212631677784141

noncomputable def hp756766 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 841709 1000)) Bool.false 7083401601501882057181 4722366482869645213696 hp756765

noncomputable def hp756767 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 841709 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 841709 1000)) Bool.false 7083401601501882057181 4722366482869645213696

noncomputable def hp756768 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 841709 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756769 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp756768 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756770 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 841709 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756771 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp756769 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp756772 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 841709 1000)) hp756771 Bool.false 7083401601501882057181 4722366482869645213696

noncomputable def hp756773 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 841709 1000) 841709 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl

noncomputable def hp756774 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp756769 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp756775 := nat_lit 118839758683142999679849988096

noncomputable def hp756776 := @hp756774 23230311 16777216 102121 134217728 544650353795586163165 4722366482869645213696 7596062008104577880141 hp754729 hp756775 7083401601501882057181 4722366482869645213696

noncomputable def hp756777 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) 11)

noncomputable def hp756778 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) 11) hp756777

noncomputable def hp756779 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) 11)

noncomputable def hp756780 := @hp756779 371684976 536870912 204242 536870912 371684976 536870912 204242 536870912 399093704083636224 23230311 16777216

noncomputable def hp756781 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp756782 := hp756781 BSN.quadSignPos 9 10 11 841709 1000 189 240 536870912 268435456 9007199254740992

noncomputable def hp756783 := hp756782 Bool.false 880420969225 3835 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp756784 := hp756783 Bool.false 512715168 175336 Bool.true 705576274 Bool.true 766148623 28296951008113761 1 Bool.false 519298642

noncomputable def hp756785 := hp756784 Bool.true Bool.false 76900808 Bool.false Bool.false 371684976 204242 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 519298642 536870912) BSN.abs_quadSignPos

noncomputable def hp756786 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp756787 := hp756786 BSN.quadSignNeg 7 8 9 841709 1000 70 133 536870912 268435456 9007199254740992

noncomputable def hp756788 := hp756787 Bool.false 880420969225 3835 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp756789 := hp756788 Bool.false 786700229 143196 Bool.true 223912032 Bool.true 319931921 28296951008113761 1 Bool.false 490850498

noncomputable def hp756790 := hp756789 Bool.true Bool.false 301329599 Bool.true Bool.false 512715168 175336 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 70 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 490850498 536870912) BSN.abs_quadSignNeg

noncomputable def hp756791 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp756792 := hp756791 BSN.quadSignNeg 5 6 7 841709 1000 83 1 536870912 268435456 9007199254740992

noncomputable def hp756793 := hp756792 Bool.false 880420969225 3835 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp756794 := hp756793 Bool.false 659318330 106411 Bool.false 749306914 Bool.false 242123285 28296951008113761 1 Bool.false 528661363

noncomputable def hp756795 := hp756794 Bool.false Bool.false 233998703 Bool.true Bool.false 786700229 143196 BSN.abs_quadSignPos (BSN.cos_quad_nat3 83 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 528661363 536870912) BSN.abs_quadSignNeg

noncomputable def hp756796 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp756797 := hp756796 BSN.quadSignNeg 3 4 5 841709 1000 301 181 536870912 268435456 9007199254740992

noncomputable def hp756798 := hp756797 Bool.false 880420969225 3835 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp756799 := hp756798 Bool.false 915548195 62894 Bool.false 131927821 Bool.false 493578436 28296951008113761 1 Bool.false 130604068

noncomputable def hp756800 := hp756799 Bool.true Bool.false 426927603 Bool.true Bool.false 659318330 106411 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 301 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 130604068 536870912) BSN.abs_quadSignNeg

noncomputable def hp756801 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp756802 := hp756801 BSN.quadSignPos 1 2 3 841709 1000 672 455 536870912 268435456 9007199254740992

noncomputable def hp756803 := hp756802 Bool.false 880420969225 3835 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp756804 := hp756803 Bool.false 536870848 3890 Bool.false 487757575 Bool.false 261819286 28296951008113761 1 Bool.false 330129498

noncomputable def hp756805 := hp756804 Bool.false Bool.false 251563992 Bool.false Bool.false 915548195 62894 BSN.abs_quadSignPos (BSN.cos_quad_nat0 672 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 330129498 536870912) BSN.abs_quadSignPos

noncomputable def hp756806 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) 1) Bool.false

noncomputable def hp756807 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)))

noncomputable def hp756808 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000))) Bool.false 67108856 67108864

noncomputable def hp756809 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 110052621153) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 110052621153 67108864

noncomputable def hp756810 := nat_lit 3781943663932231196866669322211344485161021610590409327523

noncomputable def hp756811 := nat_lit 2306187170638015097366963792394284863087045764804771840

noncomputable def hp756812 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) Bool.false hp756810 hp756811 127424332810763823707

noncomputable def hp756813 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 841709 4000) (Real.log (Enclosure.sfrac Bool.false 2833897162724 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1683418))))))

noncomputable def hp756814 := nat_lit 202792309005489996187780077223520000

noncomputable def hp756815 := nat_lit 1024152838374987649568732003222086774080

noncomputable def hp756816 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp756813 (Enclosure.sfrac Bool.false 841709 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 841709 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp756814 hp756815)) Bool.false

noncomputable def hp756817 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 841709 1000) 841709 1000 2833897162724 16000000 1683418

noncomputable def hp756818 := hp756817 4000 2000 hp756814 hp756815 (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl rfl rfl rfl

noncomputable def hp756819 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp756813 (Enclosure.sfrac Bool.false 841709 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 841709 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp756814 hp756815) 1181681164410791686867 720575940379279360

noncomputable def hp756820 := nat_lit 1210221972458313982997334183107630235251526915388930984807360

noncomputable def hp756821 := @hp756819 127424332810763823707 hp738659 hp756814 hp756815 0 1 hp756820 hp756810 hp756811 127424332810763823707 hp738659

noncomputable def hp756822 := @Enclosure.Real.IsNear.subLit_ff_p (hp756813 (Enclosure.sfrac Bool.false 841709 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 841709 2000) (Real.log Real.pi)) 38220730806053766117019 18014398509481984000 10621378083103217 4356000000000000000000

noncomputable def hp756823 := nat_lit 1982532013845136486157202227200000

noncomputable def hp756824 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 841709 4000) (Real.log (Enclosure.sfrac Bool.false 2833897162724 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1683418))))))

noncomputable def hp756825 := @hp756824 (Enclosure.sfrac Bool.false 841709 2000) 45802171483562551752347 18014398509481984000 10621378083103217 4356000000000000000000 841709 2000 0

noncomputable def hp756826 := nat_lit 76441461612107532234038000

noncomputable def hp756827 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 841709 4000) (Real.log (Enclosure.sfrac Bool.false 2833897162724 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1683418))))) 45809243046086825696347

noncomputable def hp756828 := nat_lit 103137321213065933014506068374303277056

noncomputable def hp756829 := @hp756827 18014398509481984000 956488916596247 396000000000000000000 883945315534243 2251799813685248 200000001089 8712000000000000000 hp756828 45802171483562551752347 18014398509481984000 10621378083103217

noncomputable def hp756830 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 841709 4000) (Real.log (Enclosure.sfrac Bool.false 2833897162724 16000000)) 841709 4000 0 1 54424086051220583 4503599627370496

noncomputable def hp756831 := nat_lit 116874834852341092433526784

noncomputable def hp756832 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2833897162724) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp756831 hp617687

noncomputable def hp756833 := BSN.log_rat_reduce_isNear 2833897162724 16000000 17 5667794325448 4194304000000 80818565 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp756834 := nat_lit 330328821825718524257164153222911228392205561979965613052204335825570959191634380191810881139381747384320

noncomputable def hp756835 := nat_lit 2491452011841400592275691564253238247061783034817407508317988914616720775266937148711136483245614956544

noncomputable def hp756836 := nat_lit 9114390749858374548004452016064970718472614463669733209283486293832725111386502036492110220820480

noncomputable def hp756837 := BSN.log_dyadic_bound 736745162724 4931049162724 5 4 hp756834 268435456 87120000 hp756835 hp756836 80818565 5667794325448

noncomputable def hp756838 := hp756837 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp756839 := @BSN.binarySplit_of_base4 (BSN.artanhP 736745162724) (BSN.artanhQ 4931049162724) 0 4 hp756835 hp756834 hp756836 rfl rfl rfl

noncomputable def hp756840 := hp756833 rfl rfl rfl rfl (hp756838 (hp756839 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp756841 := @hp756830 12500018513 1089000000000000000 45809243046086825696347 18014398509481984000 956488916596247 396000000000000000000 (Enclosure.Real.IsNear.const Bool.false 841709 4000) (BSN.isNear_log_sfrac 2833897162724 16000000 54424086051220583 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp756832 1000001481040000 87120000000000000000000 54424086051220583 4503599627370496 12500018513 1089000000000000000 (hp756840 rfl rfl rfl) rfl)) rfl

noncomputable def hp756842 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1683418)))) 1 4

noncomputable def hp756843 := @hp756842 0 1 883945315534243 562949953421312 200000001089 2178000000000000000 883945315534243 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp756844 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1683418))) 884279719003555 562949953421312 1

noncomputable def hp756845 := @hp756844 2000000000000000 19932 33554432 1 10890000 29660282981812300414976 883945315534243 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp756846 := BSN.arctan_dyadic_bound_f 1000 1683418 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp756847 := hp756846 1 19932 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1683418) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1683418) 0 0 rfl)

noncomputable def hp756848 := hp756843 (hp756845 (hp756847 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp756849 := @hp756822 32330683230549 67108864000 2525127 536870912000 hp756823 1181681164410791686867 720575940379279360 127424332810763823707 hp738659 (@hp756825 1 hp756826 38220730806053766117019 18014398509481984000 10621378083103217 4356000000000000000000 (@hp756829 4356000000000000000000 hp756841 hp756848 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 841709 2000) rfl rfl)

noncomputable def hp756850 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 841709 2000) (Real.log Real.pi) 841709 2000 0 1 38410761 33554432

noncomputable def hp756851 := hp756849 (@hp756850 3 268435456 32330683230549 67108864000 2525127 536870912000 (Enclosure.Real.IsNear.const Bool.false 841709 2000) hd4909 rfl) rfl

noncomputable def hp756852 := @hp756812 hp738659 110052621153 67108864 15 2097152 (@hp756816 hp756810 hp756811 127424332810763823707 hp738659 (hp756818 rfl rfl rfl rfl rfl) (hp756821 (hp756851 rfl) (Enclosure.Real.IsNear.const Bool.true hp756814 hp756815) rfl rfl)) rfl

noncomputable def hp756853 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 110052621153) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 4665800160012335579136) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp756854 := BSN.sin_reduce_arg_pos_rat_q0 110052621153 67108864 226375608064910080 72057594037927936 261 4665800160012335579136 hp617687 rfl rfl rfl rfl

noncomputable def hp756855 := BSN.cos_dyadic_bound_f 66305008 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp756856 := hp756855 1 67108856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 66305008) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp756857 := hp756856 (@BSN.binarySplit_of_le (BSN.cosOddP 66305008) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp756858 := @BSN.cos_arg_round Bool.false 67108856 67108864 4665800160012335579136 hp617687 66305008 137438953472 21801270 21780000 hp756857 rfl

noncomputable def hp756859 := hp756853 67108856 67108864 261 1000000000000000 21780000 10890000 hp756854 BSN.pi_near_15 hp756858 rfl rfl

noncomputable def hp756860 := @hp756809 15 2097152 Bool.false 67108856 67108864 1 10890000 hp756852 (Enclosure.sfrac_false_div 110052621153 67108864) (hp756859 rfl rfl) rfl

noncomputable def hp756861 := @hp756806 8388607 8388608 10340447 1427374080000 536870848 536870912 3890 536870912 (@hp756807 Bool.false 8388607 8388608 10340447 1427374080000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000)) (@hp756808 165447152 22837985280000 8388607 8388608 10340447 1427374080000 (hp756860 rfl) rfl))

noncomputable def hp756862 := @hp756812 hp738659 880420969225 536870912 3835 536870912 (@hp756816 hp756810 hp756811 127424332810763823707 hp738659 (hp756818 rfl rfl rfl rfl rfl) (hp756821 (hp756851 rfl) (Enclosure.Real.IsNear.const Bool.true hp756814 hp756815) rfl rfl)) rfl

noncomputable def hp756863 := hp756805 (BSN.cos_quad_nat3 455 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 251563992 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl rfl (hp756861 rfl) hp756862

noncomputable def hp756864 := nat_lit 7902799351422232163065481953125711042668707562875201319085956938087890625

noncomputable def hp756865 := nat_lit 3203554985559041835001456486173257961953212417700695388086090087890625

noncomputable def hp756866 := nat_lit 23701990944295578405526442946404786612082216263790202566481698634087890625

noncomputable def hp756867 := BSN.cos_dyadic_bound_f 487757575 536870912 3 2 536870912 268435456 hp756864 hp708868 hp756865 hp756866 hp708870

noncomputable def hp756868 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 487757575) (BSN.cosEvenQ 536870912) 0 2 hp756864 hp708868 hp756865 rfl rfl rfl

noncomputable def hp756869 := hp756867 hp756865 330129498 rfl rfl rfl rfl rfl rfl rfl rfl (hp756868 rfl)

noncomputable def hp756870 := @BSN.binarySplit_of_base2 (BSN.cosOddP 487757575) (BSN.cosOddQ 536870912) 0 2 hp756866 hp708870 hp756865 rfl rfl rfl

noncomputable def hp756871 := nat_lit 1180527052670701520940439437830775715476703956724644120990300839417831680

noncomputable def hp756872 := nat_lit 22080712006891122442090415472739269622172576754014459165776695091456

noncomputable def hp756873 := nat_lit 3091820816794302350169578000312694819811979226297418579183567131445125376

noncomputable def hp756874 := BSN.sin_dyadic_bound_f 261819286 536870912 3 2 536870912 268435456 hp756871 hp708845 hp756872 hp756873 hp708848

noncomputable def hp756875 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 261819286) (BSN.sinEvenQ 536870912) 0 2 hp756871 hp708845 hp756872 rfl rfl rfl

noncomputable def hp756876 := hp756874 hp756872 251563992 rfl rfl rfl rfl rfl rfl rfl rfl (hp756875 rfl)

noncomputable def hp756877 := @BSN.binarySplit_of_base2 (BSN.sinOddP 261819286) (BSN.sinOddQ 536870912) 0 2 hp756873 hp708848 hp756872 rfl rfl rfl

noncomputable def hp756878 := hp756863 hd4911 hd4913 hd4915 hd4917 hd4918 (hp756869 (hp756870 rfl) rfl rfl rfl rfl) (hp756876 (hp756877 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756879 := hp756800 (BSN.cos_quad_nat1 181 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 426927603 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl rfl (hp756878 rfl rfl rfl rfl rfl) hp756862

noncomputable def hp756880 := nat_lit 302932282894562528539597076257681

noncomputable def hp756881 := BSN.sin_dyadic_bound_f 131927821 536870912 2 1 536870912 268435456 hp756880 hp708890 hp756880 hp756880 hp708891

noncomputable def hp756882 := @BSN.binarySplit_of_base (BSN.sinEvenP 131927821) (BSN.sinEvenQ 536870912) 0 1 hp756880 hp708890 hp756880 rfl rfl rfl

noncomputable def hp756883 := hp756881 hp756880 130604068 rfl rfl rfl rfl rfl rfl rfl rfl (hp756882 rfl)

noncomputable def hp756884 := @BSN.binarySplit_of_base (BSN.sinOddP 131927821) (BSN.sinOddQ 536870912) 0 1 hp756880 hp708891 hp756880 rfl rfl rfl

noncomputable def hp756885 := nat_lit 14913809172328292058906997377127144753998628917860028952513593347087073280

noncomputable def hp756886 := nat_lit 3522487170586546240822502579160723992561844105678632961152599059398656

noncomputable def hp756887 := nat_lit 39054273329250291460366518602585785564484642275367072327027068843893784576

noncomputable def hp756888 := BSN.sin_dyadic_bound_f 493578436 536870912 3 2 536870912 268435456 hp756885 hp708845 hp756886 hp756887 hp708848

noncomputable def hp756889 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 493578436) (BSN.sinEvenQ 536870912) 0 2 hp756885 hp708845 hp756886 rfl rfl rfl

noncomputable def hp756890 := hp756888 hp756886 426927603 rfl rfl rfl rfl rfl rfl rfl rfl (hp756889 rfl)

noncomputable def hp756891 := @BSN.binarySplit_of_base2 (BSN.sinOddP 493578436) (BSN.sinOddQ 536870912) 0 2 hp756887 hp708848 hp756886 rfl rfl rfl

noncomputable def hp756892 := hp756879 hd4920 hd4922 hd4924 hd4926 hd4918 (hp756883 (hp756884 rfl) rfl rfl rfl rfl) (hp756890 (hp756891 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756893 := hp756795 (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 233998703 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl rfl (hp756892 rfl rfl rfl rfl rfl) hp756862

noncomputable def hp756894 := nat_lit 113042501543323148756712082036241207816801571761169402442615586845941841225394858166533270780553879380016149303296

noncomputable def hp756895 := nat_lit 31326860938583118708808309689046194961567021946476985209987936024676526703380713969882015777655991428714496

noncomputable def hp756896 := nat_lit 564774496538569094260699207051124715383053787788206790610161811252345580646191797672757636956914126426929604857856

noncomputable def hp756897 := BSN.sin_dyadic_bound_f 749306914 536870912 4 3 536870912 268435456 hp756894 hp642702 hp756895 hp756896 hp642705

noncomputable def hp756898 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 749306914) (BSN.sinEvenQ 536870912) 0 3 hp756894 hp642702 hp756895 rfl rfl rfl

noncomputable def hp756899 := hp756897 hp756895 528661363 rfl rfl rfl rfl rfl rfl rfl rfl (hp756898 rfl)

noncomputable def hp756900 := @BSN.binarySplit_of_base3 (BSN.sinOddP 749306914) (BSN.sinOddQ 536870912) 0 3 hp756896 hp642705 hp756895 rfl rfl rfl

noncomputable def hp756901 := nat_lit 863402804850305269549131208866126568989970380340815821461345329041430625

noncomputable def hp756902 := nat_lit 11811157490675233821844624908401704887037431757778739747896250390625

noncomputable def hp756903 := nat_lit 2261273937495814612726298750970955982689629126003100271582026886893590625

noncomputable def hp756904 := BSN.sin_dyadic_bound_f 242123285 536870912 3 2 536870912 268435456 hp756901 hp708845 hp756902 hp756903 hp708848

noncomputable def hp756905 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 242123285) (BSN.sinEvenQ 536870912) 0 2 hp756901 hp708845 hp756902 rfl rfl rfl

noncomputable def hp756906 := hp756904 hp756902 233998703 rfl rfl rfl rfl rfl rfl rfl rfl (hp756905 rfl)

noncomputable def hp756907 := @BSN.binarySplit_of_base2 (BSN.sinOddP 242123285) (BSN.sinOddQ 536870912) 0 2 hp756903 hp708848 hp756902 rfl rfl rfl

noncomputable def hp756908 := hp756893 hd4928 hd4930 hd4932 hd4934 hd4918 (hp756899 (hp756900 rfl) rfl rfl rfl rfl) (hp756906 (hp756907 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756909 := hp756790 (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 301329599 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl rfl (hp756908 rfl rfl rfl rfl rfl) hp756862

noncomputable def hp756910 := nat_lit 350837756533077755906913623160331066263103911350853727625231494866272256

noncomputable def hp756911 := nat_lit 6318579432799112075919021500419316117959511691667419857028724555776

noncomputable def hp756912 := nat_lit 1052500632440367669496589031437992360157075815029177848035980427149705216

noncomputable def hp756913 := BSN.cos_dyadic_bound_f 223912032 536870912 3 2 536870912 268435456 hp756910 hp708868 hp756911 hp756912 hp708870

noncomputable def hp756914 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 223912032) (BSN.cosEvenQ 536870912) 0 2 hp756910 hp708868 hp756911 rfl rfl rfl

noncomputable def hp756915 := hp756913 hp756911 490850498 rfl rfl rfl rfl rfl rfl rfl rfl (hp756914 rfl)

noncomputable def hp756916 := @BSN.binarySplit_of_base2 (BSN.cosOddP 223912032) (BSN.cosOddQ 536870912) 0 2 hp756912 hp708870 hp756911 rfl rfl rfl

noncomputable def hp756917 := nat_lit 2632144270481577402211410436949036366004756521049937940858668781677628545

noncomputable def hp756918 := nat_lit 109764167930762880101636205157196890619474829267690104591093152402561

noncomputable def hp756919 := nat_lit 6893533471179862437319243733391507401713359357788165965889080277385137281

noncomputable def hp756920 := BSN.sin_dyadic_bound_f 319931921 536870912 3 2 536870912 268435456 hp756917 hp708845 hp756918 hp756919 hp708848

noncomputable def hp756921 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 319931921) (BSN.sinEvenQ 536870912) 0 2 hp756917 hp708845 hp756918 rfl rfl rfl

noncomputable def hp756922 := hp756920 hp756918 301329599 rfl rfl rfl rfl rfl rfl rfl rfl (hp756921 rfl)

noncomputable def hp756923 := @BSN.binarySplit_of_base2 (BSN.sinOddP 319931921) (BSN.sinOddQ 536870912) 0 2 hp756919 hp708848 hp756918 rfl rfl rfl

noncomputable def hp756924 := hp756909 hd4936 hd4938 hd4940 hd4942 hd4918 (hp756915 (hp756916 rfl) rfl rfl rfl rfl) (hp756922 (hp756923 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756925 := hp756785 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 76900808 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl rfl (hp756924 rfl rfl rfl rfl rfl) hp756862

noncomputable def hp756926 := nat_lit 88850985825324928139792048137902795828783582442506317628236606051447172963738747676851809323376819242637055102976

noncomputable def hp756927 := nat_lit 15223959615777347225301345683008439033589445670292282624582168771900169646167063087108017790398646677016576

noncomputable def hp756928 := nat_lit 443984201572394486611323944187219298177983378558620776228531634606436079742682735848119753844830861304362722267136

noncomputable def hp756929 := BSN.sin_dyadic_bound_f 705576274 536870912 4 3 536870912 268435456 hp756926 hp642702 hp756927 hp756928 hp642705

noncomputable def hp756930 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 705576274) (BSN.sinEvenQ 536870912) 0 3 hp756926 hp642702 hp756927 rfl rfl rfl

noncomputable def hp756931 := hp756929 hp756927 519298642 rfl rfl rfl rfl rfl rfl rfl rfl (hp756930 rfl)

noncomputable def hp756932 := @BSN.binarySplit_of_base3 (BSN.sinOddP 705576274) (BSN.sinOddQ 536870912) 0 3 hp756928 hp642705 hp756927 rfl rfl rfl

noncomputable def hp756933 := nat_lit 47578199222022814102234289850883524367724439101135883163615835320072525743168933099842913213624053762504737915201

noncomputable def hp756934 := nat_lit 40903107570823683048748190502009924159947705292171757816214255806228628851630963855919314292750130845286721

noncomputable def hp756935 := nat_lit 288166998256383230419551921862867816680988474831110345346236427178298307428846045252598861148289469425690784006465

noncomputable def hp756936 := BSN.cos_dyadic_bound_f 766148623 536870912 4 3 536870912 268435456 hp756933 hp716712 hp756934 hp756935 hp716714

noncomputable def hp756937 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 766148623) (BSN.cosEvenQ 536870912) 0 3 hp756933 hp716712 hp756934 rfl rfl rfl

noncomputable def hp756938 := hp756936 hp756934 76900808 rfl rfl rfl rfl rfl rfl rfl rfl (hp756937 rfl)

noncomputable def hp756939 := @BSN.binarySplit_of_base3 (BSN.cosOddP 766148623) (BSN.cosOddQ 536870912) 0 3 hp756935 hp716714 hp756934 rfl rfl rfl

noncomputable def hp756940 := hp756925 hd4944 hd4946 hd4961 hd4963 hd4918 (hp756931 (hp756932 rfl) rfl rfl rfl rfl) (hp756938 (hp756939 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756941 := @hp756780 102121 134217728 (hp756940 rfl rfl rfl rfl rfl) (hp756940 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp756942 := @hp756778 Bool.false 23230311 16777216 102121 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 841709 1000)) (Enclosure.sfrac Bool.false 841709 1000) 11) hp756941

noncomputable def hp756943 := @Enclosure.Real.IsNear.mulLit_tf hp756769 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1))) 4931447 16777216 1

noncomputable def hp756944 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp756768 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756945 := @hp756944 1 1 0 1 4931447 16777216 1 33554432 4931447 16777216 1

noncomputable def hp756946 := @Enclosure.Real.IsNear.of_eq (hp756768 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp756947 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 841709 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756948 := @hp756946 (@Inv.inv Real Real.instInv (Real.sqrt hp756770)) Bool.false 4931447 16777216 1 33554432 (hp756947 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 841709 1000) 841709 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000))))

noncomputable def hp756949 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp756770)) Bool.false 19725788 67108864 2 67108864 4931447 16777216

noncomputable def hp756950 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp756770) Bool.false 228310250 67108864 6 67108864 114155125 33554432 3 33554432

noncomputable def hp756951 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 841709 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756952 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 841709 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp756953 := @hp756952 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 841709 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8990047208263

noncomputable def hp756954 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 841709 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 841709 1000 0

noncomputable def hp756955 := @hp756954 1 10680707 67108864 1 67108864 8990047208263 67108864000 841709 67108864000 (Enclosure.Real.IsNear.const Bool.false 841709 1000) hd4949

noncomputable def hp756956 := @hp756953 67108864000 841709 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 841709 1000) 841709 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000))) (hp756955 rfl)

noncomputable def hp756957 := @hp756951 8990047208263 67108864000 841709 67108864000 388365742 388365779 33554432 hp756956 rfl rfl rfl

noncomputable def hp756958 := @Enclosure.Real.IsNear.recentre' hp756770 Bool.false 776731521 67108864 37 67108864 776731521 67108864 37 67108864 (hp756957 rfl rfl rfl)

noncomputable def hp756959 := @Enclosure.Real.IsNear.sqrt_image hp756770 776731521 67108864 37 67108864 114155122 114155128 33554432 (hp756958 rfl) rfl rfl

noncomputable def hp756960 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp756770) 114155125 33554432 3 33554432 9862893 9862895 33554432 (hp756950 (hp756959 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp756961 := @hp756945 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp756948 (@hp756949 1 33554432 (hp756960 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp756962 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756963 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp756964 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1))) (hp756962 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756963 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp756965 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 841709 1000) 841709 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl

noncomputable def hp756966 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756967 := @hp756966 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756963 (Enclosure.sfrac Bool.false 1 16)))) 37563479

noncomputable def hp756968 := @hp756967 33554432 75 16777216 2940205 8388608 86126701 11418992640000 110444328773195 281474976710656 3835584551795429 383157812047380480000

noncomputable def hp756969 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756970 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756971 := @hp756969 (@Neg.neg Real Real.instNeg hp756970) Bool.true 37563479 33554432 75 16777216 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756972 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp756973 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp756974 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp756975 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 242116369) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp756976 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1))) Bool.false 34074849724838211430435

noncomputable def hp756977 := nat_lit 998484790465634367438267843

noncomputable def hp756978 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp756979 := @Enclosure.Real.IsNear.subLit_ff_p hp756770 (Enclosure.sfrac Bool.false 11 1) 776731521 67108864 37 67108864 11 1 0

noncomputable def hp756980 := @hp756978 500000000000000 38534017 67108864 37 67108864 34074849724838211430435 9444732965739290427392 hp756977 hp738031 hd4948 (@hp756979 1 38534017 38534017 67108864 37 67108864 (hp756958 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp756981 := @hp756975 242116369 67108864 233 67108864 Bool.true 59946519 67108864 1 10890000 (@hp756976 9444732965739290427392 hp756977 hp738031 242116369 67108864 233 67108864 (hp756980 rfl) rfl) (Enclosure.sfrac_false_div 242116369 67108864)

noncomputable def hp756982 := nat_lit 4509026265587612834070528

noncomputable def hp756983 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 242116369) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp756982) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp756984 := BSN.sin_reduce_arg_pos_rat_q2 242116369 67108864 226375608064910080 72057594037927936 0 hp756982 hp617687 rfl rfl rfl rfl

noncomputable def hp756985 := nat_lit 10105846837630601272517807781158075683361870492186950481662061218881190404427921652406510721

noncomputable def hp756986 := nat_lit 284199766429943233199599428907780915923245068230519384044092212629880642053355108263041

noncomputable def hp756987 := nat_lit 30316972113358943931087024144616411488253764986424390406218095472218311451999658247003006081

noncomputable def hp756988 := BSN.cos_dyadic_bound_f 64077117167 137438953472 3 2 67108864 21801270 hp756985 hp746621 hp756986 hp756987 hp746624

noncomputable def hp756989 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 64077117167) (BSN.cosEvenQ 137438953472) 0 2 hp756985 hp746621 hp756986 rfl rfl rfl

noncomputable def hp756990 := hp756988 hp756986 59946519 rfl rfl rfl rfl rfl rfl rfl rfl (hp756989 rfl)

noncomputable def hp756991 := @BSN.binarySplit_of_base2 (BSN.cosOddP 64077117167) (BSN.cosOddQ 137438953472) 0 2 hp756987 hp746624 hp756986 rfl rfl rfl

noncomputable def hp756992 := @BSN.cos_arg_round Bool.false 59946519 67108864 hp756982 hp617687 64077117167 137438953472 21801270 21780000 (hp756990 (hp756991 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp756993 := hp756983 59946519 67108864 0 1000000000000000 21780000 10890000 hp756984 BSN.pi_near_15 hp756992 rfl rfl

noncomputable def hp756994 := @hp756973 59946519 67108864 162779929 45675970560000 (@hp756974 59946519 67108864 2604478864 730815528960000 59946519 67108864 162779929 45675970560000 (hp756981 (hp756993 rfl rfl) rfl rfl) rfl)

noncomputable def hp756995 := @hp756972 59946519 67108864 162779929 45675970560000 37563329 37563629 33554432 hp756994 rfl rfl rfl

noncomputable def hp756996 := @Enclosure.Real.IsNear.recentre' hp756970 Bool.false 75126958 67108864 300 67108864 37563479 33554432 75 16777216 (hp756995 rfl rfl rfl)

noncomputable def hp756997 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756963 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp756998 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756963 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8090397)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true

noncomputable def hp756999 := nat_lit 1222586230747475066906201650525

noncomputable def hp757000 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756963 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp756999

noncomputable def hp757001 := nat_lit 5758339067904216190973757363770877

noncomputable def hp757002 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp756963 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp757003 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp757004 := @hp757003 (Enclosure.sfrac Bool.false 1 16) 1101103640070399 4503599627370496 5334546595 4503599627370496 1 16 0

noncomputable def hp757005 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)) 1484870466156289

noncomputable def hp757006 := @hp757005 4503599627370496 2851518627 4503599627370496 38534017 67108864 37 67108864 73893814431389356916736 1101103640070399 4503599627370496 5334546595

noncomputable def hp757007 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)) 38534017 67108864 37

noncomputable def hp757008 := @hp757007 67108864 38534017 67108864 37 67108864 1484870466156289 4503599627370496 2851518627 4503599627370496 (@hp756979 1 38534017 38534017 67108864 37 67108864 (hp756958 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757009 := hp757008 (@hp756979 1 38534017 38534017 67108864 37 67108864 (hp756958 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757010 := @hp757006 4503599627370496 (hp757009 rfl) (@hp756979 1 38534017 38534017 67108864 37 67108864 (hp756958 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757011 := @hp757002 500000000000000 1382578616781055 4503599627370496 5334546595 4503599627370496 hp756999 hp627574 hp757001 hp747268 hd4948 (@hp757004 1 22121257868496880 1382578616781055 4503599627370496 5334546595 4503599627370496 (hp757010 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp757012 := @hp756998 8090397 4194304 125 16777216 Bool.true 11760820 33554432 1 10890000 (@hp757000 hp627574 hp757001 hp747268 8090397 4194304 125 16777216 (hp757011 rfl) rfl) (Enclosure.sfrac_true_div 8090397 4194304)

noncomputable def hp757013 := nat_lit 8257572159341145329384624337754072223285411689744497062475350259473897232425646713790321

noncomputable def hp757014 := nat_lit 78639002911324146286717975050498583811779943792103054073696260740270581742484905841

noncomputable def hp757015 := nat_lit 49822595299538223719276633252023764812010184317158001682881646936726456877102702385225585

noncomputable def hp757016 := BSN.cos_dyadic_bound_t 8090397 4194304 4 3 33554432 10890000 hp757013 hp633286 hp757014 hp757015 hp633289

noncomputable def hp757017 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 8090397) (BSN.cosEvenQ 4194304) 0 3 hp757013 hp633286 hp757014 rfl rfl rfl

noncomputable def hp757018 := hp757016 hp757014 11760820 rfl rfl rfl rfl rfl rfl rfl rfl (hp757017 rfl)

noncomputable def hp757019 := @BSN.binarySplit_of_base3 (BSN.cosOddP 8090397) (BSN.cosOddQ 4194304) 0 3 hp757015 hp633289 hp757014 rfl rfl rfl

noncomputable def hp757020 := hp757012 (BSN.cos_neg_of_bound 8090397 4194304 Bool.true 11760820 33554432 1 10890000 (hp757018 (hp757019 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp757021 := hp756968 (hp756971 (@Enclosure.Real.IsNear.neg hp756970 Bool.false 37563479 33554432 75 16777216 (hp756996 rfl))) (@hp756997 11760820 33554432 1378027216 182703882240000 2940205 8388608 86126701 11418992640000 (hp757020 rfl) rfl)

noncomputable def hp757022 := @hp756943 33554432 110444328773195 281474976710656 3835584551795429 383157812047380480000 544650353795586163165 4722366482869645213696 7596062008104577880141 hp754729 (hp756961 rfl) (@hp756964 Bool.false 110444328773195 281474976710656 3835584551795429 383157812047380480000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp756770 (Enclosure.sfrac Bool.false 11 1)) (hp756965 rfl (hp756773 rfl rfl))) (hp757021 rfl))

noncomputable def hp757023 := @hp756767 hp756765 hp754729 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 841709 1000))) (@hp756772 hp756765 hp754729 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 841709 1000) 11 (hp756773 rfl rfl)) (@hp756776 hp756765 hp754729 hp756942 (hp757022 rfl) rfl rfl))

theorem hd5037 : hp756766 hp754729 := hp757023

noncomputable def hp757024 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 842992 1000)) Bool.true 104930076430729689035411 18889465931478580854784 1707744940344805006009

noncomputable def hp757025 := nat_lit 2232056032918855745536000

noncomputable def hp757026 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 842992 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 842992 1000)) Bool.true 104930076430729689035411 18889465931478580854784

noncomputable def hp757027 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 842992 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757028 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp757027 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757029 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 842992 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757030 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp757028 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp757031 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 842992 1000)) hp757030 Bool.true 104930076430729689035411 18889465931478580854784

noncomputable def hp757032 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 842992 1000) 842992 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl

noncomputable def hp757033 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp757028 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp757034 := nat_lit 28166952914797776488958751932416

noncomputable def hp757035 := @hp757033 1522288173 268435456 204555 268435456 2191430579790828932461 18889465931478580854784 6858520133174926009 hp757025 hp757034 104930076430729689035411 18889465931478580854784

noncomputable def hp757036 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) 11)

noncomputable def hp757037 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) 11) hp757036

noncomputable def hp757038 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) 11)

noncomputable def hp757039 := @hp757038 1522288173 536870912 204555 536870912 1522288173 536870912 204555 536870912 1634544479530647552 1522288173 268435456

noncomputable def hp757040 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp757041 := hp757040 BSN.quadSignPos 9 10 11 842992 1000 189 240 536870912 268435456 9007199254740992

noncomputable def hp757042 := hp757041 Bool.false 882107963824 3841 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp757043 := hp757042 Bool.true 1402686333 175605 Bool.true 604614671 Bool.true 730837186 28296951008113761 1 Bool.false 484674638

noncomputable def hp757044 := hp757043 Bool.true Bool.false 111656648 Bool.false Bool.true 1522288173 204555 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 484674638 536870912) BSN.abs_quadSignPos

noncomputable def hp757045 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp757046 := hp757045 BSN.quadSignNeg 7 8 9 842992 1000 69 133 536870912 268435456 9007199254740992

noncomputable def hp757047 := hp757046 Bool.false 882107963824 3841 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp757048 := hp757047 Bool.true 1164988486 143416 Bool.true 812562809 Bool.true 146397413 28296951008113761 1 Bool.false 535990411

noncomputable def hp757049 := hp757048 Bool.true Bool.false 144589845 Bool.true Bool.true 1402686333 175605 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535990411 536870912) BSN.abs_quadSignNeg

noncomputable def hp757050 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp757051 := hp757050 BSN.quadSignNeg 5 6 7 842992 1000 84 1 536870912 268435456 9007199254740992

noncomputable def hp757052 := hp757051 Bool.false 882107963824 3841 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp757053 := hp757052 Bool.true 1156475727 106575 Bool.false 358813104 Bool.false 588764524 28296951008113761 1 Bool.false 421363403

noncomputable def hp757054 := hp757053 Bool.false Bool.false 477647124 Bool.true Bool.true 1164988486 143416 BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 421363403 536870912) BSN.abs_quadSignNeg

noncomputable def hp757055 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp757056 := hp757055 BSN.quadSignNeg 3 4 5 842992 1000 302 182 536870912 268435456 9007199254740992

noncomputable def hp757057 := hp757056 Bool.false 882107963824 3841 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp757058 := hp757057 Bool.true 669595476 62992 Bool.false 20720567 Bool.false 228668706 28296951008113761 1 Bool.false 536471105

noncomputable def hp757059 := hp757058 Bool.true Bool.false 488904414 Bool.true Bool.true 1156475727 106575 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 302 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536471105 536870912) BSN.abs_quadSignNeg

noncomputable def hp757060 := hp757055 BSN.quadSignPos 1 2 3 842992 1000 674 456 536870912 268435456 9007199254740992

noncomputable def hp757061 := hp757060 Bool.false 882107963824 3841 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp757062 := hp757061 Bool.true 536870544 3898 Bool.false 10678973 Bool.false 348768980 28296951008113761 1 Bool.false 536764707

noncomputable def hp757063 := hp757062 Bool.true Bool.false 427513496 Bool.false Bool.true 669595476 62992 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 674 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536764707 536870912) BSN.abs_quadSignPos

noncomputable def hp757064 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) 1) Bool.true

noncomputable def hp757065 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)))

noncomputable def hp757066 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000))) Bool.true 67108818 67108864

noncomputable def hp757067 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 55131747739) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 55131747739 33554432

noncomputable def hp757068 := nat_lit 1458731599461508034458357925333260630532097334166910973

noncomputable def hp757069 := nat_lit 887817133824032941037895180220781088228375527424000

noncomputable def hp757070 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) Bool.false hp757068 hp757069 2658707058298665667

noncomputable def hp757071 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 842992 4000) (Real.log (Enclosure.sfrac Bool.false 2842543048256 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1685984))))))

noncomputable def hp757072 := nat_lit 204342588441824829831772963471360000

noncomputable def hp757073 := nat_lit 1033555173575916491725825681608148254720

noncomputable def hp757074 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp757071 (Enclosure.sfrac Bool.false 842992 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 842992 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp757072 hp757073)) Bool.false

noncomputable def hp757075 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 842992 1000) 842992 1000 2842543048256 16000000 1685984

noncomputable def hp757076 := hp757075 4000 2000 hp757072 hp757073 (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl rfl rfl rfl

noncomputable def hp757077 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp757071 (Enclosure.sfrac Bool.false 842992 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 842992 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp757072 hp757073) 1849914703150629691373 1125899906842624000

noncomputable def hp757078 := nat_lit 1911988682046187810925258899892811373651030617839253550530560

noncomputable def hp757079 := @hp757077 2658707058298665667 371712000000000000000000 hp757072 hp757073 0 1 hp757078 hp757068 hp757069 2658707058298665667 371712000000000000000000

noncomputable def hp757080 := @Enclosure.Real.IsNear.subLit_ff_p (hp757071 (Enclosure.sfrac Bool.false 842992 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 842992 2000) (Real.log Real.pi)) 478632071445115497673 225179981368524800 886451300571283 363000000000000000000

noncomputable def hp757081 := nat_lit 1551820927816699743408907878400

noncomputable def hp757082 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 842992 4000) (Real.log (Enclosure.sfrac Bool.false 2842543048256 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1685984))))))

noncomputable def hp757083 := @hp757082 (Enclosure.sfrac Bool.false 842992 2000) 2867722664360116133869 1125899906842624000 886451300571283 363000000000000000000 842992 2000 0

noncomputable def hp757084 := nat_lit 4786320714451154976730000

noncomputable def hp757085 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 842992 4000) (Real.log (Enclosure.sfrac Bool.false 2842543048256 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1685984))))) 2868164637277930103369

noncomputable def hp757086 := nat_lit 6457537361307072495211938026998464512

noncomputable def hp757087 := @hp757085 1125899906842624000 658588475394431 272250000000000000000 883945835627939 2251799813685248 200000001089 8712000000000000000 hp757086 2867722664360116133869 1125899906842624000 886451300571283

noncomputable def hp757088 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 842992 4000) (Real.log (Enclosure.sfrac Bool.false 2842543048256 16000000)) 842992 4000 0 1 54437805099510887 4503599627370496

noncomputable def hp757089 := nat_lit 116904296284210642630475776

noncomputable def hp757090 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2842543048256) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp757089 hp617687

noncomputable def hp757091 := BSN.log_rat_reduce_isNear 2842543048256 16000000 17 5685086096512 4194304000000 81636284 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp757092 := nat_lit 334990828857795147334386991638959765659043424567081016166144443159333796725914954867141106479035181957120

noncomputable def hp757093 := nat_lit 2577922417976014205072392240988952618254769962113012076760763628704466084490815176474231213183733858304

noncomputable def hp757094 := nat_lit 10006050295208857479284725015073221322244760741578449769991375912097899326908478141686280282439680

noncomputable def hp757095 := BSN.log_dyadic_bound 745391048256 4939695048256 5 4 hp757092 268435456 87120000 hp757093 hp757094 81636284 5685086096512

noncomputable def hp757096 := hp757095 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp757097 := @BSN.binarySplit_of_base4 (BSN.artanhP 745391048256) (BSN.artanhQ 4939695048256) 0 4 hp757093 hp757092 hp757094 rfl rfl rfl

noncomputable def hp757098 := hp757091 rfl rfl rfl rfl (hp757096 (hp757097 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp757099 := @hp757088 12500018513 1089000000000000000 2868164637277930103369 1125899906842624000 658588475394431 272250000000000000000 (Enclosure.Real.IsNear.const Bool.false 842992 4000) (BSN.isNear_log_sfrac 2842543048256 16000000 54437805099510887 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp757090 1000001481040000 87120000000000000000000 54437805099510887 4503599627370496 12500018513 1089000000000000000 (hp757098 rfl rfl rfl) rfl)) rfl

noncomputable def hp757100 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1685984)))) 1 4

noncomputable def hp757101 := @hp757100 0 1 883945835627939 562949953421312 200000001089 2178000000000000000 883945835627939 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp757102 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1685984))) 884279719003555 562949953421312 1

noncomputable def hp757103 := @hp757102 2000000000000000 19901 33554432 1 10890000 29660300433260856475648 883945835627939 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp757104 := BSN.arctan_dyadic_bound_f 1000 1685984 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp757105 := hp757104 1 19901 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1685984) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1685984) 0 0 rfl)

noncomputable def hp757106 := hp757101 (hp757103 (hp757105 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp757107 := @hp757080 2023747764807 4194304000 158061 33554432000 hp757081 1849914703150629691373 1125899906842624000 2658707058298665667 371712000000000000000000 (@hp757083 1 hp757084 478632071445115497673 225179981368524800 886451300571283 363000000000000000000 (@hp757087 363000000000000000000 hp757099 hp757106 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 842992 2000) rfl rfl)

noncomputable def hp757108 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 842992 2000) (Real.log Real.pi) 842992 2000 0 1 38410761 33554432

noncomputable def hp757109 := hp757107 (@hp757108 3 268435456 2023747764807 4194304000 158061 33554432000 (Enclosure.Real.IsNear.const Bool.false 842992 2000) hd4909 rfl) rfl

noncomputable def hp757110 := @hp757070 371712000000000000000000 55131747739 33554432 481 67108864 (@hp757074 hp757068 hp757069 2658707058298665667 371712000000000000000000 (hp757076 rfl rfl rfl rfl rfl) (hp757079 (hp757109 rfl) (Enclosure.Real.IsNear.const Bool.true hp757072 hp757073) rfl rfl)) rfl

noncomputable def hp757111 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 55131747739) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 5619509406730339483648) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp757112 := BSN.sin_reduce_arg_pos_rat_q2 55131747739 33554432 226375608064910080 72057594037927936 261 5619509406730339483648 hp619237 rfl rfl rfl rfl

noncomputable def hp757113 := BSN.cos_dyadic_bound_f 159716063 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp757114 := hp757113 1 67108818 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 159716063) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp757115 := hp757114 (@BSN.binarySplit_of_le (BSN.cosOddP 159716063) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp757116 := @BSN.cos_arg_round Bool.false 67108818 67108864 5619509406730339483648 hp619237 159716063 137438953472 21801270 21780000 hp757115 rfl

noncomputable def hp757117 := hp757111 67108818 67108864 261 1000000000000000 21780000 10890000 hp757112 BSN.pi_near_15 hp757116 rfl rfl

noncomputable def hp757118 := @hp757067 481 67108864 Bool.true 67108818 67108864 1 10890000 hp757110 (Enclosure.sfrac_false_div 55131747739 33554432) (hp757117 rfl rfl) rfl

noncomputable def hp757119 := @hp757064 33554409 33554432 331574929 45675970560000 536870544 536870912 3898 536870912 (@hp757065 Bool.true 33554409 33554432 331574929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000)) (@hp757066 5305198864 730815528960000 33554409 33554432 331574929 45675970560000 (hp757118 rfl) rfl))

noncomputable def hp757120 := @hp757070 371712000000000000000000 882107963824 536870912 3841 536870912 (@hp757074 hp757068 hp757069 2658707058298665667 371712000000000000000000 (hp757076 rfl rfl rfl rfl rfl) (hp757079 (hp757109 rfl) (Enclosure.Real.IsNear.const Bool.true hp757072 hp757073) rfl rfl)) rfl

noncomputable def hp757121 := hp757063 (BSN.cos_quad_nat0 456 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 427513496 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl rfl (hp757119 rfl) hp757120

noncomputable def hp757122 := nat_lit 13005227505680597060555503441

noncomputable def hp757123 := BSN.cos_dyadic_bound_f 10678973 536870912 2 1 536870912 268435456 hp757122 hp708767 hp757122 hp757122 hp708768

noncomputable def hp757124 := @BSN.binarySplit_of_base (BSN.cosEvenP 10678973) (BSN.cosEvenQ 536870912) 0 1 hp757122 hp708767 hp757122 rfl rfl rfl

noncomputable def hp757125 := hp757123 hp757122 536764707 rfl rfl rfl rfl rfl rfl rfl rfl (hp757124 rfl)

noncomputable def hp757126 := @BSN.binarySplit_of_base (BSN.cosOddP 10678973) (BSN.cosOddQ 536870912) 0 1 hp757122 hp708768 hp757122 rfl rfl rfl

noncomputable def hp757127 := nat_lit 2065314634635603583049957775360368875844145161129478775062814994636800000

noncomputable def hp757128 := nat_lit 218928756226755076989112182470069606440325345544591622717465600000000

noncomputable def hp757129 := nat_lit 6195506046394357238995895101716166488319554832697347141943010052710400000

noncomputable def hp757130 := BSN.cos_dyadic_bound_f 348768980 536870912 3 2 536870912 268435456 hp757127 hp708868 hp757128 hp757129 hp708870

noncomputable def hp757131 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 348768980) (BSN.cosEvenQ 536870912) 0 2 hp757127 hp708868 hp757128 rfl rfl rfl

noncomputable def hp757132 := hp757130 hp757128 427513496 rfl rfl rfl rfl rfl rfl rfl rfl (hp757131 rfl)

noncomputable def hp757133 := @BSN.binarySplit_of_base2 (BSN.cosOddP 348768980) (BSN.cosOddQ 536870912) 0 2 hp757129 hp708870 hp757128 rfl rfl rfl

noncomputable def hp757134 := hp757121 hd4911 hd4913 hd4915 hd4917 hd4918 (hp757125 (hp757126 rfl) rfl rfl rfl rfl) (hp757132 (hp757133 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757135 := hp757059 (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 488904414 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl rfl (hp757134 rfl rfl rfl rfl rfl) hp757120

noncomputable def hp757136 := nat_lit 184334464349100430408672617121

noncomputable def hp757137 := BSN.cos_dyadic_bound_f 20720567 536870912 2 1 536870912 268435456 hp757136 hp708767 hp757136 hp757136 hp708768

noncomputable def hp757138 := @BSN.binarySplit_of_base (BSN.cosEvenP 20720567) (BSN.cosEvenQ 536870912) 0 1 hp757136 hp708767 hp757136 rfl rfl rfl

noncomputable def hp757139 := hp757137 hp757136 536471105 rfl rfl rfl rfl rfl rfl rfl rfl (hp757138 rfl)

noncomputable def hp757140 := @BSN.binarySplit_of_base (BSN.cosOddP 20720567) (BSN.cosOddQ 536870912) 0 1 hp757136 hp708768 hp757136 rfl rfl rfl

noncomputable def hp757141 := nat_lit 381613933448104174509546627475765848581005788465228731825397692101591296

noncomputable def hp757142 := nat_lit 7475734573792810658935154171028544566975769982093540508321885225216

noncomputable def hp757143 := nat_lit 1144826848875164937907322012118955488653883413855722008395176432534323456

noncomputable def hp757144 := BSN.cos_dyadic_bound_f 228668706 536870912 3 2 536870912 268435456 hp757141 hp708868 hp757142 hp757143 hp708870

noncomputable def hp757145 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 228668706) (BSN.cosEvenQ 536870912) 0 2 hp757141 hp708868 hp757142 rfl rfl rfl

noncomputable def hp757146 := hp757144 hp757142 488904414 rfl rfl rfl rfl rfl rfl rfl rfl (hp757145 rfl)

noncomputable def hp757147 := @BSN.binarySplit_of_base2 (BSN.cosOddP 228668706) (BSN.cosOddQ 536870912) 0 2 hp757143 hp708870 hp757142 rfl rfl rfl

noncomputable def hp757148 := hp757135 hd4920 hd4922 hd4924 hd4926 hd4918 (hp757139 (hp757140 rfl) rfl rfl rfl rfl) (hp757146 (hp757147 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757149 := hp757054 (BSN.cos_quad_nat1 1 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 477647124 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl rfl (hp757148 rfl rfl rfl rfl rfl) hp757120

noncomputable def hp757150 := nat_lit 2313734568712389454478882449912933340072893002564182530913946579675119616

noncomputable def hp757151 := nat_lit 274755479360477062007494779441729916832505663955206449715035542388736

noncomputable def hp757152 := nat_lit 6940654195178447409312632360179916560385013996364637179842409667940581376

noncomputable def hp757153 := BSN.cos_dyadic_bound_f 358813104 536870912 3 2 536870912 268435456 hp757150 hp708868 hp757151 hp757152 hp708870

noncomputable def hp757154 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 358813104) (BSN.cosEvenQ 536870912) 0 2 hp757150 hp708868 hp757151 rfl rfl rfl

noncomputable def hp757155 := hp757153 hp757151 421363403 rfl rfl rfl rfl rfl rfl rfl rfl (hp757154 rfl)

noncomputable def hp757156 := @BSN.binarySplit_of_base2 (BSN.cosOddP 358813104) (BSN.cosOddQ 536870912) 0 2 hp757152 hp708870 hp757151 rfl rfl rfl

noncomputable def hp757157 := nat_lit 30201985477688675117674213471481166602824787080718335176426617727671664640

noncomputable def hp757158 := nat_lit 14438865458923464764855569810368124773941199835201589024794359512498176

noncomputable def hp757159 := nat_lit 79077060945108273031908411978948173662526156602148170508410522228500791296

noncomputable def hp757160 := BSN.sin_dyadic_bound_f 588764524 536870912 3 2 536870912 268435456 hp757157 hp708845 hp757158 hp757159 hp708848

noncomputable def hp757161 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 588764524) (BSN.sinEvenQ 536870912) 0 2 hp757157 hp708845 hp757158 rfl rfl rfl

noncomputable def hp757162 := hp757160 hp757158 477647124 rfl rfl rfl rfl rfl rfl rfl rfl (hp757161 rfl)

noncomputable def hp757163 := @BSN.binarySplit_of_base2 (BSN.sinOddP 588764524) (BSN.sinOddQ 536870912) 0 2 hp757159 hp708848 hp757158 rfl rfl rfl

noncomputable def hp757164 := hp757149 hd4928 hd4930 hd4932 hd4934 hd4918 (hp757155 (hp757156 rfl) rfl rfl rfl rfl) (hp757162 (hp757163 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757165 := hp757049 (BSN.cos_quad_nat1 133 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 144589845 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl rfl (hp757164 rfl rfl rfl rfl rfl) hp757120

noncomputable def hp757166 := nat_lit 156400818540922001983648535632050850647075180298722638202281911206855965216562002350401349323398287982045329934881

noncomputable def hp757167 := nat_lit 82848240494541492443981669474846644533704818063581607117293638158696877664778029906660687323088355490318881

noncomputable def hp757168 := nat_lit 781166350548148683585021443080705841603278192168393703278674883759858068819103283291651595293447551893614535428641

noncomputable def hp757169 := BSN.sin_dyadic_bound_f 812562809 536870912 4 3 536870912 268435456 hp757166 hp642702 hp757167 hp757168 hp642705

noncomputable def hp757170 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 812562809) (BSN.sinEvenQ 536870912) 0 3 hp757166 hp642702 hp757167 rfl rfl rfl

noncomputable def hp757171 := hp757169 hp757167 535990411 rfl rfl rfl rfl rfl rfl rfl rfl (hp757170 rfl)

noncomputable def hp757172 := @BSN.binarySplit_of_base3 (BSN.sinOddP 812562809) (BSN.sinOddQ 536870912) 0 3 hp757168 hp642705 hp757167 rfl rfl rfl

noncomputable def hp757173 := nat_lit 459339305419499531201563123019761

noncomputable def hp757174 := BSN.sin_dyadic_bound_f 146397413 536870912 2 1 536870912 268435456 hp757173 hp708890 hp757173 hp757173 hp708891

noncomputable def hp757175 := @BSN.binarySplit_of_base (BSN.sinEvenP 146397413) (BSN.sinEvenQ 536870912) 0 1 hp757173 hp708890 hp757173 rfl rfl rfl

noncomputable def hp757176 := hp757174 hp757173 144589845 rfl rfl rfl rfl rfl rfl rfl rfl (hp757175 rfl)

noncomputable def hp757177 := @BSN.binarySplit_of_base (BSN.sinOddP 146397413) (BSN.sinOddQ 536870912) 0 1 hp757173 hp708891 hp757173 rfl rfl rfl

noncomputable def hp757178 := hp757165 hd4936 hd4938 hd4940 hd4942 hd4918 (hp757171 (hp757172 rfl) rfl rfl rfl rfl) (hp757176 (hp757177 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757179 := hp757044 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 111656648 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl rfl (hp757178 rfl rfl rfl rfl rfl) hp757120

noncomputable def hp757180 := nat_lit 33589764633570810742322285250003565979990961031764081149629891600671644545

noncomputable def hp757181 := nat_lit 17857861448869135397263233841024258307620379533711049255580603806194561

noncomputable def hp757182 := nat_lit 87944280359863478105915178038076252577002083992518013693093061786072849281

noncomputable def hp757183 := BSN.sin_dyadic_bound_f 604614671 536870912 3 2 536870912 268435456 hp757180 hp708845 hp757181 hp757182 hp708848

noncomputable def hp757184 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 604614671) (BSN.sinEvenQ 536870912) 0 2 hp757180 hp708845 hp757181 rfl rfl rfl

noncomputable def hp757185 := hp757183 hp757181 484674638 rfl rfl rfl rfl rfl rfl rfl rfl (hp757184 rfl)

noncomputable def hp757186 := @BSN.binarySplit_of_base2 (BSN.sinOddP 604614671) (BSN.sinOddQ 536870912) 0 2 hp757182 hp708848 hp757181 rfl rfl rfl

noncomputable def hp757187 := nat_lit 39378061930323436475832369937405694595152806888172223371933589687984170761941912638514003860345030170670679986176

noncomputable def hp757188 := nat_lit 23219220772904572245764602712940090725419224630048965254400878876208162774723039782006767914086369237405696

noncomputable def hp757189 := nat_lit 238568580363622233583344266182711185349158842534327728357134761291492430043126696847120617559101500748251221463040

noncomputable def hp757190 := BSN.cos_dyadic_bound_f 730837186 536870912 4 3 536870912 268435456 hp757187 hp716712 hp757188 hp757189 hp716714

noncomputable def hp757191 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 730837186) (BSN.cosEvenQ 536870912) 0 3 hp757187 hp716712 hp757188 rfl rfl rfl

noncomputable def hp757192 := hp757190 hp757188 111656648 rfl rfl rfl rfl rfl rfl rfl rfl (hp757191 rfl)

noncomputable def hp757193 := @BSN.binarySplit_of_base3 (BSN.cosOddP 730837186) (BSN.cosOddQ 536870912) 0 3 hp757189 hp716714 hp757188 rfl rfl rfl

noncomputable def hp757194 := hp757179 hd4944 hd4946 hd4961 hd4963 hd4918 (hp757185 (hp757186 rfl) rfl rfl rfl rfl) (hp757192 (hp757193 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757195 := @hp757039 204555 268435456 (hp757194 rfl rfl rfl rfl rfl) (hp757194 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp757196 := @hp757037 Bool.true 1522288173 268435456 204555 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 842992 1000)) (Enclosure.sfrac Bool.false 842992 1000) 11) hp757195

noncomputable def hp757197 := @Enclosure.Real.IsNear.mulLit_tf hp757028 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1))) 9859139 33554432 1

noncomputable def hp757198 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp757027 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757199 := @hp757198 1 1 0 1 9859139 33554432 1 33554432 9859139 33554432 1

noncomputable def hp757200 := @Enclosure.Real.IsNear.of_eq (hp757027 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757201 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 842992 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757202 := @hp757200 (@Inv.inv Real Real.instInv (Real.sqrt hp757029)) Bool.false 9859139 33554432 1 33554432 (hp757201 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 842992 1000) 842992 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000))))

noncomputable def hp757203 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp757029)) Bool.false 19718278 67108864 2 67108864 9859139 33554432

noncomputable def hp757204 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp757029) Bool.false 228397202 67108864 6 67108864 114198601 33554432 3 33554432

noncomputable def hp757205 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 842992 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757206 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 842992 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757207 := @hp757206 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 842992 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 562734409709

noncomputable def hp757208 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 842992 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 842992 1000 0

noncomputable def hp757209 := @hp757208 1 10680707 67108864 1 67108864 562734409709 4194304000 52687 4194304000 (Enclosure.Real.IsNear.const Bool.false 842992 1000) hd4949

noncomputable def hp757210 := @hp757207 4194304000 52687 4194304000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 842992 1000) 842992 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000))) (hp757209 rfl)

noncomputable def hp757211 := @hp757205 562734409709 4194304000 52687 4194304000 388661618 388661655 33554432 hp757210 rfl rfl rfl

noncomputable def hp757212 := @Enclosure.Real.IsNear.recentre' hp757029 Bool.false 777323273 67108864 37 67108864 777323273 67108864 37 67108864 (hp757211 rfl rfl rfl)

noncomputable def hp757213 := @Enclosure.Real.IsNear.sqrt_image hp757029 777323273 67108864 37 67108864 114198598 114198604 33554432 (hp757212 rfl) rfl rfl

noncomputable def hp757214 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp757029) 114198601 33554432 3 33554432 9859138 9859140 33554432 (hp757204 (hp757213 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp757215 := @hp757199 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp757202 (@hp757203 1 33554432 (hp757214 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp757216 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757217 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp757218 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1))) (hp757216 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757217 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp757219 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 842992 1000) 842992 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl

noncomputable def hp757220 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757221 := @hp757220 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757217 (Enclosure.sfrac Bool.false 1 16)))) 38701321

noncomputable def hp757222 := @hp757221 33554432 5 1048576 5743319 16777216 347909929 45675970560000 222274032224399 562949953421312 15966419263304849 1532631248189521920000

noncomputable def hp757223 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757224 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757225 := @hp757223 (@Neg.neg Real Real.instNeg hp757224) Bool.true 38701321 33554432 5 1048576 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757226 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757227 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp757228 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp757229 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 30729307) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false

noncomputable def hp757230 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1))) Bool.false 34598124017118003108795

noncomputable def hp757231 := nat_lit 998484790470717478412953027

noncomputable def hp757232 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp757233 := @Enclosure.Real.IsNear.subLit_ff_p hp757029 (Enclosure.sfrac Bool.false 11 1) 777323273 67108864 37 67108864 11 1 0

noncomputable def hp757234 := @hp757232 500000000000000 39125769 67108864 37 67108864 34598124017118003108795 9444732965739290427392 hp757231 hp738031 hd4948 (@hp757233 1 39125769 39125769 67108864 37 67108864 (hp757212 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757235 := @hp757229 30729307 8388608 117 33554432 Bool.true 58184056 67108864 1 10890000 (@hp757230 9444732965739290427392 hp757231 hp738031 30729307 8388608 117 33554432 (hp757234 rfl) rfl) (Enclosure.sfrac_false_div 30729307 8388608)

noncomputable def hp757236 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 30729307) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 630607384109375945703424) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp757237 := BSN.sin_reduce_arg_pos_rat_q2 30729307 8388608 226375608064910080 72057594037927936 0 630607384109375945703424 hp630689 rfl rfl rfl rfl

noncomputable def hp757238 := nat_lit 15835972224679037414123620253295740311156750452826492097864446811483370072307626917784036481

noncomputable def hp757239 := nat_lit 697836861340312809488766650688615235243640309004585607197518741879776514718986084918401

noncomputable def hp757240 := nat_lit 47506521000314431616751883226585843702999764077861467122378945396966350663893442781182272641

noncomputable def hp757241 := BSN.cos_dyadic_bound_f 71691759343 137438953472 3 2 67108864 21801270 hp757238 hp746621 hp757239 hp757240 hp746624

noncomputable def hp757242 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 71691759343) (BSN.cosEvenQ 137438953472) 0 2 hp757238 hp746621 hp757239 rfl rfl rfl

noncomputable def hp757243 := hp757241 hp757239 58184056 rfl rfl rfl rfl rfl rfl rfl rfl (hp757242 rfl)

noncomputable def hp757244 := @BSN.binarySplit_of_base2 (BSN.cosOddP 71691759343) (BSN.cosOddQ 137438953472) 0 2 hp757240 hp746624 hp757239 rfl rfl rfl

noncomputable def hp757245 := @BSN.cos_arg_round Bool.false 58184056 67108864 630607384109375945703424 hp630689 71691759343 137438953472 21801270 21780000 (hp757243 (hp757244 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757246 := hp757236 58184056 67108864 0 1000000000000000 21780000 10890000 hp757237 BSN.pi_near_15 hp757245 rfl rfl

noncomputable def hp757247 := @hp757227 7273007 8388608 81730277 22837985280000 (@hp757228 58184056 67108864 1307684432 365407764480000 7273007 8388608 81730277 22837985280000 (hp757235 (hp757246 rfl rfl) rfl rfl) rfl)

noncomputable def hp757248 := @hp757226 7273007 8388608 81730277 22837985280000 38701161 38701481 33554432 hp757247 rfl rfl rfl

noncomputable def hp757249 := @Enclosure.Real.IsNear.recentre' hp757224 Bool.false 77402642 67108864 320 67108864 38701321 33554432 5 1048576 (hp757248 rfl rfl rfl)

noncomputable def hp757250 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757217 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp757251 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757217 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 64430895)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp757252 := nat_lit 1217065204505025782731576202605

noncomputable def hp757253 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757217 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp757252

noncomputable def hp757254 := nat_lit 145140187440615268033910535588785893

noncomputable def hp757255 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757217 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp757256 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp757257 := @hp757256 (Enclosure.sfrac Bool.false 1 16) 1094860110875055 4503599627370496 5378336243 4503599627370496 1 16 0

noncomputable def hp757258 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)) 1530825799841361

noncomputable def hp757259 := @hp757258 4503599627370496 2895308275 4503599627370496 39125769 67108864 37 67108864 73474818279738986987520 1094860110875055 4503599627370496 5378336243

noncomputable def hp757260 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)) 39125769 67108864 37

noncomputable def hp757261 := @hp757260 67108864 39125769 67108864 37 67108864 1530825799841361 4503599627370496 2895308275 4503599627370496 (@hp757233 1 39125769 39125769 67108864 37 67108864 (hp757212 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757262 := hp757261 (@hp757233 1 39125769 39125769 67108864 37 67108864 (hp757212 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757263 := @hp757259 4503599627370496 (hp757262 rfl) (@hp757233 1 39125769 39125769 67108864 37 67108864 (hp757212 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757264 := @hp757255 500000000000000 1376335087585711 4503599627370496 5378336243 4503599627370496 hp757252 hp627574 hp757254 hp738055 hd4948 (@hp757257 1 22021361401371376 1376335087585711 4503599627370496 5378336243 4503599627370496 (hp757263 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp757265 := @hp757251 64430895 33554432 505 67108864 Bool.true 11486638 33554432 1 10890000 (@hp757253 hp627574 hp757254 hp738055 64430895 33554432 505 67108864 (hp757264 rfl) rfl) (Enclosure.sfrac_true_div 64430895 33554432)

noncomputable def hp757266 := nat_lit 557193145436574663195720773893783942380121934078743567032659416009381212475639493984047051131890625

noncomputable def hp757267 := nat_lit 5118349871123736665416081999118130164612450828052123967604465237314530957103854839902587890625

noncomputable def hp757268 := nat_lit 3362189581401016800461303575404358274946962977616983824568804775800133057284516865772848761621490625

noncomputable def hp757269 := BSN.cos_dyadic_bound_t 64430895 33554432 4 3 33554432 10890000 hp757266 hp681868 hp757267 hp757268 hp681871

noncomputable def hp757270 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 64430895) (BSN.cosEvenQ 33554432) 0 3 hp757266 hp681868 hp757267 rfl rfl rfl

noncomputable def hp757271 := hp757269 hp757267 11486638 rfl rfl rfl rfl rfl rfl rfl rfl (hp757270 rfl)

noncomputable def hp757272 := @BSN.binarySplit_of_base3 (BSN.cosOddP 64430895) (BSN.cosOddQ 33554432) 0 3 hp757268 hp681871 hp757267 rfl rfl rfl

noncomputable def hp757273 := hp757265 (BSN.cos_neg_of_bound 64430895 33554432 Bool.true 11486638 33554432 1 10890000 (hp757271 (hp757272 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp757274 := hp757222 (hp757225 (@Enclosure.Real.IsNear.neg hp757224 Bool.false 38701321 33554432 5 1048576 (hp757249 rfl))) (@hp757250 11486638 33554432 5566558864 730815528960000 5743319 16777216 347909929 45675970560000 (hp757273 rfl) rfl)

noncomputable def hp757275 := @hp757197 33554432 222274032224399 562949953421312 15966419263304849 1532631248189521920000 2191430579790828932461 18889465931478580854784 6858520133174926009 hp757025 (hp757215 rfl) (@hp757218 Bool.false 222274032224399 562949953421312 15966419263304849 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757029 (Enclosure.sfrac Bool.false 11 1)) (hp757219 rfl (hp757032 rfl rfl))) (hp757274 rfl))

noncomputable def hp757276 := @hp757026 1707744940344805006009 hp757025 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 842992 1000))) (@hp757031 1707744940344805006009 hp757025 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 842992 1000) 11 (hp757032 rfl rfl)) (@hp757035 1707744940344805006009 hp757025 hp757196 (hp757275 rfl) rfl rfl))

theorem hd5038 : hp757024 hp757025 := hp757276

noncomputable def hp757277 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 844274 1000)) Bool.false 52372009867399691650209 151115727451828646838272 477732781872026344984691

noncomputable def hp757278 := nat_lit 623352375738793168207872000

noncomputable def hp757279 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 844274 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 844274 1000)) Bool.false 52372009867399691650209 151115727451828646838272

noncomputable def hp757280 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 844274 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757281 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp757280 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757282 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 844274 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757283 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp757281 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp757284 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 844274 1000)) hp757283 Bool.false 52372009867399691650209 151115727451828646838272

noncomputable def hp757285 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 844274 1000) 844274 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl

noncomputable def hp757286 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp757281 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp757287 := nat_lit 14058504350391935762383245410304

noncomputable def hp757288 := @hp757286 61684917 268435456 204869 268435456 17646488715452194899105 151115727451828646838272 1992431591209426456691 hp757278 hp757287 52372009867399691650209 151115727451828646838272

noncomputable def hp757289 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) 11)

noncomputable def hp757290 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) 11) hp757289

noncomputable def hp757291 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) 11)

noncomputable def hp757292 := @hp757291 61684917 536870912 204869 536870912 61684917 536870912 204869 536870912 66233675292868608 61684917 268435456

noncomputable def hp757293 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp757294 := hp757293 BSN.quadSignPos 9 10 11 844274 1000 189 240 536870912 268435456 9007199254740992

noncomputable def hp757295 := hp757294 Bool.false 883794166460 3847 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp757296 := hp757295 Bool.false 154372815 175875 Bool.true 503208841 Bool.true 695030352 28296951008113761 1 Bool.false 432697789

noncomputable def hp757297 := hp757296 Bool.true Bool.false 146406314 Bool.false Bool.false 61684917 204869 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 189 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 432697789 536870912) BSN.abs_quadSignPos

noncomputable def hp757298 := hp757293 BSN.quadSignPos 7 8 9 844274 1000 69 132 536870912 268435456 9007199254740992

noncomputable def hp757299 := hp757298 Bool.false 883794166460 3847 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp757300 := hp757299 Bool.false 308758810 143637 Bool.true 557574302 Bool.true 815790099 28296951008113761 1 Bool.false 462608744

noncomputable def hp757301 := hp757300 Bool.true Bool.false 27512700 Bool.false Bool.false 154372815 175875 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 462608744 536870912) BSN.abs_quadSignPos

noncomputable def hp757302 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp757303 := hp757302 BSN.quadSignNeg 5 6 7 844274 1000 84 2 536870912 268435456 9007199254740992

noncomputable def hp757304 := hp757303 Bool.false 883794166460 3847 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp757305 := hp757304 Bool.false 495825839 106740 Bool.false 811804131 Bool.false 92343646 28296951008113761 1 Bool.false 31492636

noncomputable def hp757306 := hp757305 Bool.false Bool.false 528948759 Bool.true Bool.false 308758810 143637 BSN.abs_quadSignPos (BSN.cos_quad_nat0 84 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 31492636 536870912) BSN.abs_quadSignNeg

noncomputable def hp757307 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp757308 := hp757307 BSN.quadSignNeg 3 4 5 844274 1000 302 182 536870912 268435456 9007199254740992

noncomputable def hp757309 := hp757308 Bool.false 883794166460 3847 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp757310 := hp757309 Bool.false 557041794 63090 Bool.false 752780468 Bool.false 807145929 28296951008113761 1 Bool.false 90105906

noncomputable def hp757311 := hp757310 Bool.true Bool.false 36141573 Bool.true Bool.false 495825839 106740 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 302 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 90105906 536870912) BSN.abs_quadSignNeg

noncomputable def hp757312 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp757313 := hp757312 BSN.quadSignNeg 1 2 3 844274 1000 675 457 536870912 268435456 9007199254740992

noncomputable def hp757314 := hp757313 Bool.false 883794166460 3847 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp757315 := hp757314 Bool.false 536870872 3906 Bool.false 376495395 Bool.false 435516525 28296951008113761 1 Bool.false 346385950

noncomputable def hp757316 := hp757315 Bool.false Bool.false 389297352 Bool.true Bool.false 557041794 63090 BSN.abs_quadSignPos (BSN.cos_quad_nat3 675 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 346385950 536870912) BSN.abs_quadSignNeg

noncomputable def hp757317 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) 1) Bool.false

noncomputable def hp757318 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)))

noncomputable def hp757319 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000))) Bool.false 67108859 67108864

noncomputable def hp757320 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 110474270807) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 110474270807 67108864

noncomputable def hp757321 := nat_lit 755152230453620699586269661202808379691652371229432718139

noncomputable def hp757322 := nat_lit 458725891217391651135585433901439558594247526449152000

noncomputable def hp757323 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) Bool.false hp757321 hp757322 63905696942452258351

noncomputable def hp757324 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 844274 4000) (Real.log (Enclosure.sfrac Bool.false 2851195348304 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1688548))))))

noncomputable def hp757325 := nat_lit 205901115110882349804245649259520000

noncomputable def hp757326 := nat_lit 1043021919070705851335300016902327930880

noncomputable def hp757327 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp757324 (Enclosure.sfrac Bool.false 844274 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 844274 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp757325 hp757326)) Bool.false

noncomputable def hp757328 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 844274 1000) 844274 1000 2851195348304 16000000 1688548

noncomputable def hp757329 := hp757328 4000 2000 hp757325 hp757326 (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl rfl rfl rfl

noncomputable def hp757330 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp757324 (Enclosure.sfrac Bool.false 844274 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 844274 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp757325 hp757326) 14827607408348360797519 9007199254740992000

noncomputable def hp757331 := nat_lit 15465517679690151927526802661433515616085040562778782067486720

noncomputable def hp757332 := @hp757330 63905696942452258351 hp739631 hp757325 hp757326 0 1 hp757331 hp757321 hp757322 63905696942452258351 hp739631

noncomputable def hp757333 := @Enclosure.Real.IsNear.subLit_ff_p (hp757324 (Enclosure.sfrac Bool.false 844274 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 844274 2000) (Real.log Real.pi)) 19180181870250466405711 9007199254740992000 5326720315294531 2178000000000000000000

noncomputable def hp757334 := nat_lit 497531944506121304691817054208000

noncomputable def hp757335 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 844274 4000) (Real.log (Enclosure.sfrac Bool.false 2851195348304 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1688548))))))

noncomputable def hp757336 := @hp757335 (Enclosure.sfrac Bool.false 844274 2000) 4596490788409812909123 1801439850948198400 5326720315294531 2178000000000000000000 844274 2000 0

noncomputable def hp757337 := nat_lit 7672072748100186562284400

noncomputable def hp757338 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 844274 4000) (Real.log (Enclosure.sfrac Bool.false 2851195348304 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1688548))))) 4597197945480968444323

noncomputable def hp757339 := nat_lit 10350377100947175395904404870349717504

noncomputable def hp757340 := @hp757338 1801439850948198400 5276720315022281 2178000000000000000000 883946338944419 2251799813685248 200000001089 8712000000000000000 hp757339 4596490788409812909123 1801439850948198400 5326720315294531

noncomputable def hp757341 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 844274 4000) (Real.log (Enclosure.sfrac Bool.false 2851195348304 16000000)) 844274 4000 0 1 54451492589857895 4503599627370496

noncomputable def hp757342 := nat_lit 116933689945913000156200960

noncomputable def hp757343 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2851195348304) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp757342 hp617687

noncomputable def hp757344 := BSN.log_rat_reduce_isNear 2851195348304 16000000 17 5702390696608 4194304000000 82452122 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp757345 := nat_lit 339713829060289865667901207390406519152953749058619774642841096311417343365480862032425400596933661163520

noncomputable def hp757346 := nat_lit 2666698806602529644866062557145654389121912303857198521056902304814835519866680430709609189207319773184

noncomputable def hp757347 := nat_lit 10973869843225555515693098522764802187632962946158822465046670883162467340246160954013309500129280

noncomputable def hp757348 := BSN.log_dyadic_bound 754043348304 4948347348304 5 4 hp757345 268435456 87120000 hp757346 hp757347 82452122 5702390696608

noncomputable def hp757349 := hp757348 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp757350 := @BSN.binarySplit_of_base4 (BSN.artanhP 754043348304) (BSN.artanhQ 4948347348304) 0 4 hp757346 hp757345 hp757347 rfl rfl rfl

noncomputable def hp757351 := hp757344 rfl rfl rfl rfl (hp757349 (hp757350 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp757352 := @hp757341 12500018513 1089000000000000000 4597197945480968444323 1801439850948198400 5276720315022281 2178000000000000000000 (Enclosure.Real.IsNear.const Bool.false 844274 4000) (BSN.isNear_log_sfrac 2851195348304 16000000 54451492589857895 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp757343 1000001481040000 87120000000000000000000 54451492589857895 4503599627370496 12500018513 1089000000000000000 (hp757351 rfl rfl rfl) rfl)) rfl

noncomputable def hp757353 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1688548)))) 1 4

noncomputable def hp757354 := @hp757353 0 1 883946338944419 562949953421312 200000001089 2178000000000000000 883946338944419 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp757355 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1688548))) 884279719003555 562949953421312 1

noncomputable def hp757356 := @hp757355 2000000000000000 19871 33554432 1 10890000 29660317321759459115008 883946338944419 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp757357 := BSN.arctan_dyadic_bound_f 1000 1688548 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp757358 := hp757357 1 19871 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1688548) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1688548) 0 0 rfl)

noncomputable def hp757359 := hp757354 (hp757356 (hp757358 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp757360 := @hp757333 16214603416257 33554432000 1266411 268435456000 hp757334 14827607408348360797519 9007199254740992000 63905696942452258351 hp739631 (@hp757336 1 hp757337 19180181870250466405711 9007199254740992000 5326720315294531 2178000000000000000000 (@hp757340 2178000000000000000000 hp757352 hp757359 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 844274 2000) rfl rfl)

noncomputable def hp757361 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 844274 2000) (Real.log Real.pi) 844274 2000 0 1 38410761 33554432

noncomputable def hp757362 := hp757360 (@hp757361 3 268435456 16214603416257 33554432000 1266411 268435456000 (Enclosure.Real.IsNear.const Bool.false 844274 2000) hd4909 rfl) rfl

noncomputable def hp757363 := @hp757323 hp739631 110474270807 67108864 241 33554432 (@hp757327 hp757321 hp757322 63905696942452258351 hp739631 (hp757329 rfl rfl rfl rfl rfl) (hp757332 (hp757362 rfl) (Enclosure.Real.IsNear.const Bool.true hp757325 hp757326) rfl rfl)) rfl

noncomputable def hp757364 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 110474270807) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3545410308151594450944) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp757365 := BSN.sin_reduce_arg_pos_rat_q0 110474270807 67108864 226375608064910080 72057594037927936 262 3545410308151594450944 hp617687 rfl rfl rfl rfl

noncomputable def hp757366 := BSN.cos_dyadic_bound_f 50383310 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp757367 := hp757366 1 67108859 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 50383310) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp757368 := hp757367 (@BSN.binarySplit_of_le (BSN.cosOddP 50383310) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp757369 := @BSN.cos_arg_round Bool.false 67108859 67108864 3545410308151594450944 hp617687 50383310 137438953472 21801270 21780000 hp757368 rfl

noncomputable def hp757370 := hp757364 67108859 67108864 262 1000000000000000 21780000 10890000 hp757365 BSN.pi_near_15 hp757369 rfl rfl

noncomputable def hp757371 := @hp757320 241 33554432 Bool.false 67108859 67108864 1 10890000 hp757363 (Enclosure.sfrac_false_div 110474270807 67108864) (hp757370 rfl rfl) rfl

noncomputable def hp757372 := @hp757317 67108859 67108864 166127777 22837985280000 536870872 536870912 3906 536870912 (@hp757318 Bool.false 67108859 67108864 166127777 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000)) (@hp757319 2658044432 365407764480000 67108859 67108864 166127777 22837985280000 (hp757371 rfl) rfl))

noncomputable def hp757373 := @hp757323 hp739631 883794166460 536870912 3847 536870912 (@hp757327 hp757321 hp757322 63905696942452258351 hp739631 (hp757329 rfl rfl rfl rfl rfl) (hp757332 (hp757362 rfl) (Enclosure.Real.IsNear.const Bool.true hp757325 hp757326) rfl rfl)) rfl

noncomputable def hp757374 := hp757316 (BSN.cos_quad_nat1 457 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 389297352 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl rfl (hp757372 rfl) hp757373

noncomputable def hp757375 := nat_lit 5048178367776181399715567999667614682535570530797893765722920085581630625

noncomputable def hp757376 := nat_lit 403717289615550330954937149913005495093174146943781670660247875390625

noncomputable def hp757377 := nat_lit 13220765897135383251100179624696274540601105298708955644664674108534590625

noncomputable def hp757378 := BSN.sin_dyadic_bound_f 376495395 536870912 3 2 536870912 268435456 hp757375 hp708845 hp757376 hp757377 hp708848

noncomputable def hp757379 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 376495395) (BSN.sinEvenQ 536870912) 0 2 hp757375 hp708845 hp757376 rfl rfl rfl

noncomputable def hp757380 := hp757378 hp757376 346385950 rfl rfl rfl rfl rfl rfl rfl rfl (hp757379 rfl)

noncomputable def hp757381 := @BSN.binarySplit_of_base2 (BSN.sinOddP 376495395) (BSN.sinOddQ 536870912) 0 2 hp757377 hp708848 hp757376 rfl rfl rfl

noncomputable def hp757382 := nat_lit 9039450388645614208651829478918578025790319410013135422185354508925390625

noncomputable def hp757383 := nat_lit 1294306422808283984953934969462893769532545859997817892163238525390625

noncomputable def hp757384 := nat_lit 23672655474149204753350580359598097763347783856737262971993378470525390625

noncomputable def hp757385 := BSN.sin_dyadic_bound_f 435516525 536870912 3 2 536870912 268435456 hp757382 hp708845 hp757383 hp757384 hp708848

noncomputable def hp757386 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 435516525) (BSN.sinEvenQ 536870912) 0 2 hp757382 hp708845 hp757383 rfl rfl rfl

noncomputable def hp757387 := hp757385 hp757383 389297352 rfl rfl rfl rfl rfl rfl rfl rfl (hp757386 rfl)

noncomputable def hp757388 := @BSN.binarySplit_of_base2 (BSN.sinOddP 435516525) (BSN.sinOddQ 536870912) 0 2 hp757384 hp708848 hp757383 rfl rfl rfl

noncomputable def hp757389 := hp757374 hd4911 hd4913 hd4915 hd4917 hd4918 (hp757380 (hp757381 rfl) rfl rfl rfl rfl) (hp757387 (hp757388 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757390 := hp757311 (BSN.cos_quad_nat2 182 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36141573 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl rfl (hp757389 rfl rfl rfl rfl rfl) hp757373

noncomputable def hp757391 := nat_lit 44335999091226280353479952969614474716340897184251619808799219981978718356079941440267615895192966181337018925056

noncomputable def hp757392 := nat_lit 33114645169588084785732874268262166966554483485497164433190976153163590159641619303326292817212541266558976

noncomputable def hp757393 := nat_lit 268559935223688269252162045229279608786119019716310431281079873111846951090480150463429783433543875011014138265600

noncomputable def hp757394 := BSN.cos_dyadic_bound_f 752780468 536870912 4 3 536870912 268435456 hp757391 hp716712 hp757392 hp757393 hp716714

noncomputable def hp757395 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 752780468) (BSN.cosEvenQ 536870912) 0 3 hp757391 hp716712 hp757392 rfl rfl rfl

noncomputable def hp757396 := hp757394 hp757392 90105906 rfl rfl rfl rfl rfl rfl rfl rfl (hp757395 rfl)

noncomputable def hp757397 := @BSN.binarySplit_of_base3 (BSN.cosOddP 752780468) (BSN.cosOddQ 536870912) 0 3 hp757393 hp716714 hp757392 rfl rfl rfl

noncomputable def hp757398 := nat_lit 58642465359597303622524844668466695113265079693230100634401017821043896250967024480213066810228602118086487025121

noncomputable def hp757399 := nat_lit 76458315906908903234860816137682557242397907445995752907077196785827708096237223390689014845852112148342241

noncomputable def hp757400 := nat_lit 355044832249123710274733596336761369698576795203285266001039957416525698014498148298414552209829518688051984180705

noncomputable def hp757401 := BSN.cos_dyadic_bound_f 807145929 536870912 4 3 536870912 268435456 hp757398 hp716712 hp757399 hp757400 hp716714

noncomputable def hp757402 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 807145929) (BSN.cosEvenQ 536870912) 0 3 hp757398 hp716712 hp757399 rfl rfl rfl

noncomputable def hp757403 := hp757401 hp757399 36141573 rfl rfl rfl rfl rfl rfl rfl rfl (hp757402 rfl)

noncomputable def hp757404 := @BSN.binarySplit_of_base3 (BSN.cosOddP 807145929) (BSN.cosOddQ 536870912) 0 3 hp757400 hp716714 hp757399 rfl rfl rfl

noncomputable def hp757405 := hp757390 hd4920 hd4922 hd4924 hd4926 hd4918 (hp757396 (hp757397 rfl) rfl rfl rfl rfl) (hp757403 (hp757404 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757406 := hp757306 (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 528948759 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl rfl (hp757405 rfl rfl rfl rfl rfl) hp757373

noncomputable def hp757407 := nat_lit 60012219705412639156133777179068341858594298876487052567130767792544786549249351092462596619955697206608646800241

noncomputable def hp757408 := nat_lit 81924742232844404619174574373167832864624437022863846590627024348783841504482750859625378262681589733294961

noncomputable def hp757409 := nat_lit 363320769996013476177233503650564491789640315408894087786785436102895260441922797002215674237057206577782711026545

noncomputable def hp757410 := BSN.cos_dyadic_bound_f 811804131 536870912 4 3 536870912 268435456 hp757407 hp716712 hp757408 hp757409 hp716714

noncomputable def hp757411 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 811804131) (BSN.cosEvenQ 536870912) 0 3 hp757407 hp716712 hp757408 rfl rfl rfl

noncomputable def hp757412 := hp757410 hp757408 31492636 rfl rfl rfl rfl rfl rfl rfl rfl (hp757411 rfl)

noncomputable def hp757413 := @BSN.binarySplit_of_base3 (BSN.cosOddP 811804131) (BSN.cosOddQ 536870912) 0 3 hp757409 hp716714 hp757408 rfl rfl rfl

noncomputable def hp757414 := nat_lit 72715680227172021124444883235856

noncomputable def hp757415 := BSN.cos_dyadic_bound_f 92343646 536870912 2 1 536870912 268435456 hp757414 hp708767 hp757414 hp757414 hp708768

noncomputable def hp757416 := @BSN.binarySplit_of_base (BSN.cosEvenP 92343646) (BSN.cosEvenQ 536870912) 0 1 hp757414 hp708767 hp757414 rfl rfl rfl

noncomputable def hp757417 := hp757415 hp757414 528948759 rfl rfl rfl rfl rfl rfl rfl rfl (hp757416 rfl)

noncomputable def hp757418 := @BSN.binarySplit_of_base (BSN.cosOddP 92343646) (BSN.cosOddQ 536870912) 0 1 hp757414 hp708768 hp757414 rfl rfl rfl

noncomputable def hp757419 := hp757406 hd4928 hd4930 hd4932 hd4934 hd4918 (hp757412 (hp757413 rfl) rfl rfl rfl rfl) (hp757417 (hp757418 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757420 := hp757301 (BSN.cos_quad_nat0 132 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 27512700 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl rfl (hp757419 rfl rfl rfl rfl rfl) hp757373

noncomputable def hp757421 := nat_lit 24290660994712492117207973629902493169129298026772345116331651478121447680

noncomputable def hp757422 := nat_lit 9341615656678213743836320455312228939385140087730432100899113018163456

noncomputable def hp757423 := nat_lit 63603273322707619389483243559483643262770109367118864128895726735907717376

noncomputable def hp757424 := BSN.sin_dyadic_bound_f 557574302 536870912 3 2 536870912 268435456 hp757421 hp708845 hp757422 hp757423 hp708848

noncomputable def hp757425 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 557574302) (BSN.sinEvenQ 536870912) 0 2 hp757421 hp708845 hp757422 rfl rfl rfl

noncomputable def hp757426 := hp757424 hp757422 462608744 rfl rfl rfl rfl rfl rfl rfl rfl (hp757425 rfl)

noncomputable def hp757427 := @BSN.binarySplit_of_base2 (BSN.sinOddP 557574302) (BSN.sinOddQ 536870912) 0 2 hp757423 hp708848 hp757422 rfl rfl rfl

noncomputable def hp757428 := nat_lit 61203331338129408152594301368639941933091096202528882520856446358385653258733056188895473301749280109916564408881

noncomputable def hp757429 := nat_lit 86884270959978731243186051119892194695875362128203457334489723692605726004529361640673838578045664519178801

noncomputable def hp757430 := nat_lit 370516732960283494498423499300436117622964765174712436347643411135327310216694513438413769052405765746183554648625

noncomputable def hp757431 := BSN.cos_dyadic_bound_f 815790099 536870912 4 3 536870912 268435456 hp757428 hp716712 hp757429 hp757430 hp716714

noncomputable def hp757432 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 815790099) (BSN.cosEvenQ 536870912) 0 3 hp757428 hp716712 hp757429 rfl rfl rfl

noncomputable def hp757433 := hp757431 hp757429 27512700 rfl rfl rfl rfl rfl rfl rfl rfl (hp757432 rfl)

noncomputable def hp757434 := @BSN.binarySplit_of_base3 (BSN.cosOddP 815790099) (BSN.cosOddQ 536870912) 0 3 hp757430 hp716714 hp757429 rfl rfl rfl

noncomputable def hp757435 := hp757420 hd4936 hd4938 hd4940 hd4942 hd4918 (hp757426 (hp757427 rfl) rfl rfl rfl rfl) (hp757433 (hp757434 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757436 := hp757297 (BSN.cos_quad_nat0 240 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 146406314 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl rfl (hp757435 rfl rfl rfl rfl rfl) hp757373

noncomputable def hp757437 := nat_lit 16112582929354004840853859556048228014912874483120747092110100937456341825

noncomputable def hp757438 := nat_lit 4111365638334872245985059748854899374864321228179465245618393197171521

noncomputable def hp757439 := nat_lit 42192965461084137170980894454818641630545843316661094678462120294828331841

noncomputable def hp757440 := BSN.sin_dyadic_bound_f 503208841 536870912 3 2 536870912 268435456 hp757437 hp708845 hp757438 hp757439 hp708848

noncomputable def hp757441 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 503208841) (BSN.sinEvenQ 536870912) 0 2 hp757437 hp708845 hp757438 rfl rfl rfl

noncomputable def hp757442 := hp757440 hp757438 432697789 rfl rfl rfl rfl rfl rfl rfl rfl (hp757441 rfl)

noncomputable def hp757443 := @BSN.binarySplit_of_base2 (BSN.sinOddP 503208841) (BSN.sinOddQ 536870912) 0 2 hp757439 hp708848 hp757438 rfl rfl rfl

noncomputable def hp757444 := nat_lit 32197747318774024599592329910267798903769681822288259596784946484668352847543727570089208556870815644172393906176

noncomputable def hp757445 := nat_lit 12707064896312300294594964991493956441525208482473379743852929472466585351838163741086466700214987648925696

noncomputable def hp757446 := nat_lit 195115573339590158657556594818144688655327545309148919005025880045296893490057180254062497522967485052653446103040

noncomputable def hp757447 := BSN.cos_dyadic_bound_f 695030352 536870912 4 3 536870912 268435456 hp757444 hp716712 hp757445 hp757446 hp716714

noncomputable def hp757448 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 695030352) (BSN.cosEvenQ 536870912) 0 3 hp757444 hp716712 hp757445 rfl rfl rfl

noncomputable def hp757449 := hp757447 hp757445 146406314 rfl rfl rfl rfl rfl rfl rfl rfl (hp757448 rfl)

noncomputable def hp757450 := @BSN.binarySplit_of_base3 (BSN.cosOddP 695030352) (BSN.cosOddQ 536870912) 0 3 hp757446 hp716714 hp757445 rfl rfl rfl

noncomputable def hp757451 := hp757436 hd4944 hd4946 hd4961 hd4963 hd4918 (hp757442 (hp757443 rfl) rfl rfl rfl rfl) (hp757449 (hp757450 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757452 := @hp757292 204869 268435456 (hp757451 rfl rfl rfl rfl rfl) (hp757451 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp757453 := @hp757290 Bool.false 61684917 268435456 204869 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 844274 1000)) (Enclosure.sfrac Bool.false 844274 1000) 11) hp757452

noncomputable def hp757454 := @Enclosure.Real.IsNear.mulLit_tf hp757281 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1))) 19710789 67108864 1

noncomputable def hp757455 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp757280 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757456 := @hp757455 1 1 0 1 19710789 67108864 1 67108864 19710789 67108864 1

noncomputable def hp757457 := @Enclosure.Real.IsNear.of_eq (hp757280 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp757458 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 844274 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757459 := @hp757457 (@Inv.inv Real Real.instInv (Real.sqrt hp757282)) Bool.false 19710789 67108864 1 67108864 (hp757458 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 844274 1000) 844274 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000))))

noncomputable def hp757460 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp757282)) Bool.false 19710789 67108864 1 67108864 19710789 67108864

noncomputable def hp757461 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp757282) Bool.false 228483988 67108864 6 67108864 57120997 16777216 3 33554432

noncomputable def hp757462 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 844274 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757463 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 844274 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp757464 := @hp757463 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 844274 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 4508721610859

noncomputable def hp757465 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 844274 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 844274 1000 0

noncomputable def hp757466 := @hp757465 1 10680707 67108864 1 67108864 4508721610859 33554432000 422137 33554432000 (Enclosure.Real.IsNear.const Bool.false 844274 1000) hd4949

noncomputable def hp757467 := @hp757464 33554432000 422137 33554432000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 844274 1000) 844274 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000))) (hp757466 rfl)

noncomputable def hp757468 := @hp757462 4508721610859 33554432000 422137 33554432000 388957039 388957076 33554432 hp757467 rfl rfl rfl

noncomputable def hp757469 := @Enclosure.Real.IsNear.recentre' hp757282 Bool.false 777914115 67108864 37 67108864 777914115 67108864 37 67108864 (hp757468 rfl rfl rfl)

noncomputable def hp757470 := @Enclosure.Real.IsNear.sqrt_image hp757282 777914115 67108864 37 67108864 114241991 114241997 33554432 (hp757469 rfl) rfl rfl

noncomputable def hp757471 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp757282) 57120997 16777216 3 33554432 9855394 9855395 33554432 (hp757461 (hp757470 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp757472 := @hp757456 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp757459 (@hp757460 1 67108864 (hp757471 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp757473 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757474 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp757475 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1))) (hp757473 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757474 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp757476 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 844274 1000) 844274 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl

noncomputable def hp757477 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757478 := @hp757477 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757474 (Enclosure.sfrac Bool.false 1 16)))) 80069465

noncomputable def hp757479 := @hp757478 67108864 343 67108864 11181173 33554432 350632429 45675970560000 895270540182445 2251799813685248 5549276462927897 510877082729840640000

noncomputable def hp757480 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757481 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757482 := @hp757480 (@Neg.neg Real Real.instNeg hp757481) Bool.true 80069465 67108864 343 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757483 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp757484 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp757485 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp757486 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 124773413) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp757487 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1))) Bool.false 35120593614853501552105

noncomputable def hp757488 := nat_lit 998484790475792772547159491

noncomputable def hp757489 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp757490 := @Enclosure.Real.IsNear.subLit_ff_p hp757282 (Enclosure.sfrac Bool.false 11 1) 777914115 67108864 37 67108864 11 1 0

noncomputable def hp757491 := @hp757489 500000000000000 39716611 67108864 37 67108864 35120593614853501552105 9444732965739290427392 hp757488 hp738031 hd4948 (@hp757490 1 39716611 39716611 67108864 37 67108864 (hp757469 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757492 := @hp757486 124773413 33554432 117 33554432 Bool.true 56246156 67108864 1 10890000 (@hp757487 9444732965739290427392 hp757488 hp738031 124773413 33554432 117 33554432 (hp757491 rfl) rfl) (Enclosure.sfrac_false_div 124773413 33554432)

noncomputable def hp757493 := nat_lit 2789933986816086314582016

noncomputable def hp757494 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 124773413) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp757493) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp757495 := BSN.sin_reduce_arg_pos_rat_q2 124773413 33554432 226375608064910080 72057594037927936 0 hp757493 hp619237 rfl rfl rfl rfl

noncomputable def hp757496 := nat_lit 23700296103731004832117639891367605896576214096519917357187561774259813797044684071971136641

noncomputable def hp757497 := nat_lit 1562978416114712377041244837299953500354794416716801112162342305295140197270229973804161

noncomputable def hp757498 := nat_lit 71097762354360785071598837184428217782727932700726318469338360638168851110739511755965801601

noncomputable def hp757499 := BSN.cos_dyadic_bound_f 79294693103 137438953472 3 2 67108864 21801270 hp757496 hp746621 hp757497 hp757498 hp746624

noncomputable def hp757500 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 79294693103) (BSN.cosEvenQ 137438953472) 0 2 hp757496 hp746621 hp757497 rfl rfl rfl

noncomputable def hp757501 := hp757499 hp757497 56246156 rfl rfl rfl rfl rfl rfl rfl rfl (hp757500 rfl)

noncomputable def hp757502 := @BSN.binarySplit_of_base2 (BSN.cosOddP 79294693103) (BSN.cosOddQ 137438953472) 0 2 hp757498 hp746624 hp757497 rfl rfl rfl

noncomputable def hp757503 := @BSN.cos_arg_round Bool.false 56246156 67108864 hp757493 hp619237 79294693103 137438953472 21801270 21780000 (hp757501 (hp757502 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp757504 := hp757494 56246156 67108864 0 1000000000000000 21780000 10890000 hp757495 BSN.pi_near_15 hp757503 rfl rfl

noncomputable def hp757505 := @hp757484 14061539 16777216 81730277 22837985280000 (@hp757485 56246156 67108864 1307684432 365407764480000 14061539 16777216 81730277 22837985280000 (hp757492 (hp757504 rfl rfl) rfl rfl) rfl)

noncomputable def hp757506 := @hp757483 14061539 16777216 81730277 22837985280000 40034561 40034904 33554432 hp757505 rfl rfl rfl

noncomputable def hp757507 := @Enclosure.Real.IsNear.recentre' hp757481 Bool.false 80069465 67108864 343 67108864 80069465 67108864 343 67108864 (hp757506 rfl rfl rfl)

noncomputable def hp757508 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757474 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp757509 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757474 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 32053177)) (@Nat.cast Real Real.instNatCast 16777216)) Bool.true

noncomputable def hp757510 := nat_lit 1210934799120482747979023224645

noncomputable def hp757511 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757474 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp757510

noncomputable def hp757512 := nat_lit 29264016188260233345987803132670861

noncomputable def hp757513 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp757474 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp757514 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp757515 := @hp757514 (Enclosure.sfrac Bool.false 1 16) 1087927456814583 4503599627370496 5422058551 4503599627370496 1 16 0

noncomputable def hp757516 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)) 1577409189325321

noncomputable def hp757517 := @hp757516 4503599627370496 2939030583 4503599627370496 39716611 67108864 37 67108864 73009575741235723763712 1087927456814583 4503599627370496 5422058551

noncomputable def hp757518 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)) 39716611 67108864 37

noncomputable def hp757519 := @hp757518 67108864 39716611 67108864 37 67108864 1577409189325321 4503599627370496 2939030583 4503599627370496 (@hp757490 1 39716611 39716611 67108864 37 67108864 (hp757469 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757520 := hp757519 (@hp757490 1 39716611 39716611 67108864 37 67108864 (hp757469 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757521 := @hp757517 4503599627370496 (hp757520 rfl) (@hp757490 1 39716611 39716611 67108864 37 67108864 (hp757469 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp757522 := @hp757513 500000000000000 1369402433525239 4503599627370496 5422058551 4503599627370496 hp757510 hp627574 hp757512 hp742826 hd4948 (@hp757515 1 21910438936403824 1369402433525239 4503599627370496 5422058551 4503599627370496 (hp757521 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp757523 := @hp757509 32053177 16777216 509 67108864 Bool.true 11181173 33554432 1 10890000 (@hp757511 hp627574 hp757512 hp742826 32053177 16777216 509 67108864 (hp757522 rfl) rfl) (Enclosure.sfrac_true_div 32053177 16777216)

noncomputable def hp757524 := nat_lit 133291850068193597571355379954332905362909700718392402431060775716053320445162907306609526132001

noncomputable def hp757525 := nat_lit 1176123644623589542803812769006924856105282306548818172288014687687418162703213335353183521

noncomputable def hp757526 := nat_lit 804389724860753783728116651717616467780762303795795191269669706429595409484912770558382453247265

noncomputable def hp757527 := BSN.cos_dyadic_bound_t 32053177 16777216 4 3 33554432 10890000 hp757524 hp633087 hp757525 hp757526 hp633090

noncomputable def hp757528 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 32053177) (BSN.cosEvenQ 16777216) 0 3 hp757524 hp633087 hp757525 rfl rfl rfl

noncomputable def hp757529 := hp757527 hp757525 11181173 rfl rfl rfl rfl rfl rfl rfl rfl (hp757528 rfl)

noncomputable def hp757530 := @BSN.binarySplit_of_base3 (BSN.cosOddP 32053177) (BSN.cosOddQ 16777216) 0 3 hp757526 hp633090 hp757525 rfl rfl rfl

noncomputable def hp757531 := hp757523 (BSN.cos_neg_of_bound 32053177 16777216 Bool.true 11181173 33554432 1 10890000 (hp757529 (hp757530 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp757532 := hp757479 (hp757482 (@Enclosure.Real.IsNear.neg hp757481 Bool.false 80069465 67108864 343 67108864 (hp757507 rfl))) (@hp757508 11181173 33554432 5610118864 730815528960000 11181173 33554432 350632429 45675970560000 (hp757531 rfl) rfl)

noncomputable def hp757533 := @hp757454 67108864 895270540182445 2251799813685248 5549276462927897 510877082729840640000 17646488715452194899105 151115727451828646838272 1992431591209426456691 hp757278 (hp757472 rfl) (@hp757475 Bool.false 895270540182445 2251799813685248 5549276462927897 510877082729840640000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp757282 (Enclosure.sfrac Bool.false 11 1)) (hp757476 rfl (hp757285 rfl rfl))) (hp757532 rfl))

noncomputable def hp757534 := @hp757279 477732781872026344984691 hp757278 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 844274 1000))) (@hp757284 477732781872026344984691 hp757278 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 844274 1000) 11 (hp757285 rfl rfl)) (@hp757288 477732781872026344984691 hp757278 hp757453 (hp757533 rfl) rfl rfl))

theorem hd5039 : hp757277 hp757278 := hp757534

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

noncomputable def hp790762 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) Bool.false 556919581 10737418240 1213 10737418240

noncomputable def hp792297 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) 830146 1000 831433 1000

noncomputable def hp792298 := hp792297 (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl rfl rfl

noncomputable def hp792299 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298))

noncomputable def hp792300 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 830146 1000) 830146 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl rfl

noncomputable def hp792301 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298))

noncomputable def hp792302 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298)) 72094639779617503274629

noncomputable def hp792303 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 830146 1000))

noncomputable def hp792304 := @hp792302 37778931862957161709568 hp754467 hp743344 (@hp792303 Bool.true 72094639779617503274629 37778931862957161709568 hp754467 hp743344 (hd4340 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298) hd5028)

noncomputable def hp792305 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298)) 15784989092937944361795

noncomputable def hp792306 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 831433 1000))

noncomputable def hp792307 := @hp792305 18889465931478580854784 hp754727 hp754729 (@hp792306 Bool.false 15784989092937944361795 18889465931478580854784 hp754727 hp754729 (hd4359 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298) hd5029)

noncomputable def hp792308 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298) hp792300 (hp792301 (hp792304 rfl rfl rfl) (hp792307 rfl rfl rfl))

noncomputable def hp792309 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792310 := hp792309 (Enclosure.sfrac Bool.false 830146 1000) 749551 1000 830146 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792311 := hp792310 (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl rfl rfl rfl

noncomputable def hp792312 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792313 := @hp792312 Bool.true Bool.false 72094639779617503274629 37778931862957161709568 hp754467 hp743344 556919581 10737418240 1213 10737418240 (@hp792303 Bool.true 72094639779617503274629 37778931862957161709568 hp754467 hp743344 (hd4340 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298) hd5028)

noncomputable def hp792314 := hp792313 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792315 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792316 := hp792315 (Enclosure.sfrac Bool.false 831433 1000) 749551 1000 831433 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792317 := hp792316 (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl rfl rfl rfl

noncomputable def hp792318 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792319 := @hp792318 Bool.false Bool.false 15784989092937944361795 18889465931478580854784 hp754727 hp754729 556919581 10737418240 1213 10737418240 (@hp792306 Bool.false 15784989092937944361795 18889465931478580854784 hp754727 hp754729 (hd4359 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298) hd5029)

noncomputable def hp792320 := hp792319 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792322 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) 831433 1000 832719 1000

noncomputable def hp792323 := hp792322 (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl rfl rfl

noncomputable def hp792324 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323))

noncomputable def hp792325 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 831433 1000) 831433 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl rfl

noncomputable def hp792326 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323))

noncomputable def hp792327 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323)) 15784989092937944361795

noncomputable def hp792328 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 831433 1000))

noncomputable def hp792329 := @hp792327 18889465931478580854784 hp754727 hp754729 (@hp792328 Bool.false 15784989092937944361795 18889465931478580854784 hp754727 hp754729 (hd4340 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323) hd5029)

noncomputable def hp792330 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323)) 25666612124073623993571

noncomputable def hp792331 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 832719 1000))

noncomputable def hp792332 := @hp792330 18889465931478580854784 hp754974 hp754729 (@hp792331 Bool.true 25666612124073623993571 18889465931478580854784 hp754974 hp754729 (hd4359 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323) hd5030)

noncomputable def hp792333 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323) hp792325 (hp792326 (hp792329 rfl rfl rfl) (hp792332 rfl rfl rfl))

noncomputable def hp792334 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792335 := hp792334 (Enclosure.sfrac Bool.false 831433 1000) 749551 1000 831433 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792336 := hp792335 (@Eq.refl Real (Enclosure.sfrac Bool.false 831433 1000)) rfl rfl rfl rfl

noncomputable def hp792337 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792338 := @hp792337 Bool.false Bool.false 15784989092937944361795 18889465931478580854784 hp754727 hp754729 556919581 10737418240 1213 10737418240 (@hp792328 Bool.false 15784989092937944361795 18889465931478580854784 hp754727 hp754729 (hd4340 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323) hd5029)

noncomputable def hp792339 := hp792338 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792340 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792341 := hp792340 (Enclosure.sfrac Bool.false 832719 1000) 749551 1000 832719 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792342 := hp792341 (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl rfl rfl rfl

noncomputable def hp792343 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792344 := @hp792343 Bool.true Bool.false 25666612124073623993571 18889465931478580854784 hp754974 hp754729 556919581 10737418240 1213 10737418240 (@hp792331 Bool.true 25666612124073623993571 18889465931478580854784 hp754974 hp754729 (hd4359 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323) hd5030)

noncomputable def hp792345 := hp792344 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792347 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) 832719 1000 834004 1000

noncomputable def hp792348 := hp792347 (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl rfl rfl

noncomputable def hp792349 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348))

noncomputable def hp792350 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 832719 1000) 832719 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl rfl

noncomputable def hp792351 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348))

noncomputable def hp792352 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348)) 25666612124073623993571

noncomputable def hp792353 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 832719 1000))

noncomputable def hp792354 := @hp792352 18889465931478580854784 hp754974 hp754729 (@hp792353 Bool.true 25666612124073623993571 18889465931478580854784 hp754974 hp754729 (hd4340 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348) hd5030)

noncomputable def hp792355 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348)) 664356483192670713703121

noncomputable def hp792356 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 834004 1000))

noncomputable def hp792357 := @hp792355 151115727451828646838272 hp755227 hp755229 (@hp792356 Bool.false 664356483192670713703121 151115727451828646838272 hp755227 hp755229 (hd4359 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348) hd5031)

noncomputable def hp792358 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348) hp792350 (hp792351 (hp792354 rfl rfl rfl) (hp792357 rfl rfl rfl))

noncomputable def hp792359 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792360 := hp792359 (Enclosure.sfrac Bool.false 832719 1000) 749551 1000 832719 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792361 := hp792360 (@Eq.refl Real (Enclosure.sfrac Bool.false 832719 1000)) rfl rfl rfl rfl

noncomputable def hp792362 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792363 := @hp792362 Bool.true Bool.false 25666612124073623993571 18889465931478580854784 hp754974 hp754729 556919581 10737418240 1213 10737418240 (@hp792353 Bool.true 25666612124073623993571 18889465931478580854784 hp754974 hp754729 (hd4340 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348) hd5030)

noncomputable def hp792364 := hp792363 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792365 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792366 := hp792365 (Enclosure.sfrac Bool.false 834004 1000) 749551 1000 834004 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792367 := hp792366 (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl rfl rfl rfl

noncomputable def hp792368 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792369 := @hp792368 Bool.false Bool.false 664356483192670713703121 151115727451828646838272 hp755227 hp755229 556919581 10737418240 1213 10737418240 (@hp792356 Bool.false 664356483192670713703121 151115727451828646838272 hp755227 hp755229 (hd4359 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348) hd5031)

noncomputable def hp792370 := hp792369 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792372 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) 834004 1000 835932 1000

noncomputable def hp792373 := hp792372 (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl rfl rfl

noncomputable def hp792374 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373))

noncomputable def hp792375 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 834004 1000) 834004 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl rfl

noncomputable def hp792376 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373))

noncomputable def hp792377 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373)) 664356483192670713703121

noncomputable def hp792378 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 834004 1000))

noncomputable def hp792379 := @hp792377 151115727451828646838272 hp755227 hp755229 (@hp792378 Bool.false 664356483192670713703121 151115727451828646838272 hp755227 hp755229 (hd4340 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373) hd5031)

noncomputable def hp792380 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373)) 299924172146550985982823

noncomputable def hp792381 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 835932 1000))

noncomputable def hp792382 := @hp792380 75557863725914323419136 hp755486 hp755488 (@hp792381 Bool.true 299924172146550985982823 75557863725914323419136 hp755486 hp755488 (hd4359 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373) hd5032)

noncomputable def hp792383 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373) hp792375 (hp792376 (hp792379 rfl rfl rfl) (hp792382 rfl rfl rfl))

noncomputable def hp792384 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792385 := hp792384 (Enclosure.sfrac Bool.false 834004 1000) 749551 1000 834004 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792386 := hp792385 (@Eq.refl Real (Enclosure.sfrac Bool.false 834004 1000)) rfl rfl rfl rfl

noncomputable def hp792387 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792388 := @hp792387 Bool.false Bool.false 664356483192670713703121 151115727451828646838272 hp755227 hp755229 556919581 10737418240 1213 10737418240 (@hp792378 Bool.false 664356483192670713703121 151115727451828646838272 hp755227 hp755229 (hd4340 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373) hd5031)

noncomputable def hp792389 := hp792388 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792390 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792391 := hp792390 (Enclosure.sfrac Bool.false 835932 1000) 749551 1000 835932 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792392 := hp792391 (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl rfl rfl rfl

noncomputable def hp792393 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792394 := @hp792393 Bool.true Bool.false 299924172146550985982823 75557863725914323419136 hp755486 hp755488 556919581 10737418240 1213 10737418240 (@hp792381 Bool.true 299924172146550985982823 75557863725914323419136 hp755486 hp755488 (hd4359 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373) hd5032)

noncomputable def hp792395 := hp792394 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792397 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) 835932 1000 836975 1000

noncomputable def hp792398 := hp792397 (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl rfl rfl

noncomputable def hp792399 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398))

noncomputable def hp792400 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 835932 1000) 835932 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl rfl

noncomputable def hp792401 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398))

noncomputable def hp792402 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398)) 299924172146550985982823

noncomputable def hp792403 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 835932 1000))

noncomputable def hp792404 := @hp792402 75557863725914323419136 hp755486 hp755488 (@hp792403 Bool.true 299924172146550985982823 75557863725914323419136 hp755486 hp755488 (hd4340 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398) hd5032)

noncomputable def hp792405 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398)) 1809654454223218690565

noncomputable def hp792406 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 836975 1000))

noncomputable def hp792407 := @hp792405 4722366482869645213696 35497466644823495963647 hp755739 (@hp792406 Bool.false 1809654454223218690565 4722366482869645213696 35497466644823495963647 hp755739 (hd4359 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398) hd5033)

noncomputable def hp792408 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398) hp792400 (hp792401 (hp792404 rfl rfl rfl) (hp792407 rfl rfl rfl))

noncomputable def hp792409 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792410 := hp792409 (Enclosure.sfrac Bool.false 835932 1000) 749551 1000 835932 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792411 := hp792410 (@Eq.refl Real (Enclosure.sfrac Bool.false 835932 1000)) rfl rfl rfl rfl

noncomputable def hp792412 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792413 := @hp792412 Bool.true Bool.false 299924172146550985982823 75557863725914323419136 hp755486 hp755488 556919581 10737418240 1213 10737418240 (@hp792403 Bool.true 299924172146550985982823 75557863725914323419136 hp755486 hp755488 (hd4340 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398) hd5032)

noncomputable def hp792414 := hp792413 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792415 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792416 := hp792415 (Enclosure.sfrac Bool.false 836975 1000) 749551 1000 836975 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792417 := hp792416 (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl rfl rfl rfl

noncomputable def hp792418 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792419 := @hp792418 Bool.false Bool.false 1809654454223218690565 4722366482869645213696 35497466644823495963647 hp755739 556919581 10737418240 1213 10737418240 (@hp792406 Bool.false 1809654454223218690565 4722366482869645213696 35497466644823495963647 hp755739 (hd4359 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398) hd5033)

noncomputable def hp792420 := hp792419 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792422 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) 836975 1000 837617 1000

noncomputable def hp792423 := hp792422 (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl rfl rfl

noncomputable def hp792424 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423))

noncomputable def hp792425 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 836975 1000) 836975 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl rfl

noncomputable def hp792426 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423))

noncomputable def hp792427 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423)) 1809654454223218690565

noncomputable def hp792428 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 836975 1000))

noncomputable def hp792429 := @hp792427 4722366482869645213696 35497466644823495963647 hp755739 (@hp792428 Bool.false 1809654454223218690565 4722366482869645213696 35497466644823495963647 hp755739 (hd4340 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423) hd5033)

noncomputable def hp792430 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423)) 15461606859136740593409

noncomputable def hp792431 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 837617 1000))

noncomputable def hp792432 := @hp792430 37778931862957161709568 hp755994 hp740088 (@hp792431 Bool.true 15461606859136740593409 37778931862957161709568 hp755994 hp740088 (hd4359 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423) hd5034)

noncomputable def hp792433 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423) hp792425 (hp792426 (hp792429 rfl rfl rfl) (hp792432 rfl rfl rfl))

noncomputable def hp792434 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792435 := hp792434 (Enclosure.sfrac Bool.false 836975 1000) 749551 1000 836975 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792436 := hp792435 (@Eq.refl Real (Enclosure.sfrac Bool.false 836975 1000)) rfl rfl rfl rfl

noncomputable def hp792437 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792438 := @hp792437 Bool.false Bool.false 1809654454223218690565 4722366482869645213696 35497466644823495963647 hp755739 556919581 10737418240 1213 10737418240 (@hp792428 Bool.false 1809654454223218690565 4722366482869645213696 35497466644823495963647 hp755739 (hd4340 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423) hd5033)

noncomputable def hp792439 := hp792438 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792440 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792441 := hp792440 (Enclosure.sfrac Bool.false 837617 1000) 749551 1000 837617 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792442 := hp792441 (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl rfl rfl rfl

noncomputable def hp792443 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792444 := @hp792443 Bool.true Bool.false 15461606859136740593409 37778931862957161709568 hp755994 hp740088 556919581 10737418240 1213 10737418240 (@hp792431 Bool.true 15461606859136740593409 37778931862957161709568 hp755994 hp740088 (hd4359 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423) hd5034)

noncomputable def hp792445 := hp792444 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792447 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) 837617 1000 839142 1000

noncomputable def hp792448 := hp792447 (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl rfl rfl

noncomputable def hp792449 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448))

noncomputable def hp792450 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 837617 1000) 837617 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl rfl

noncomputable def hp792451 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448))

noncomputable def hp792452 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448)) 15461606859136740593409

noncomputable def hp792453 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 837617 1000))

noncomputable def hp792454 := @hp792452 37778931862957161709568 hp755994 hp740088 (@hp792453 Bool.true 15461606859136740593409 37778931862957161709568 hp755994 hp740088 (hd4340 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448) hd5034)

noncomputable def hp792455 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448)) 9880340082090028839003

noncomputable def hp792456 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 839142 1000))

noncomputable def hp792457 := @hp792455 9444732965739290427392 hp756247 hp756249 (@hp792456 Bool.false 9880340082090028839003 9444732965739290427392 hp756247 hp756249 (hd4359 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448) hd5035)

noncomputable def hp792458 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448) hp792450 (hp792451 (hp792454 rfl rfl rfl) (hp792457 rfl rfl rfl))

noncomputable def hp792459 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792460 := hp792459 (Enclosure.sfrac Bool.false 837617 1000) 749551 1000 837617 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792461 := hp792460 (@Eq.refl Real (Enclosure.sfrac Bool.false 837617 1000)) rfl rfl rfl rfl

noncomputable def hp792462 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792463 := @hp792462 Bool.true Bool.false 15461606859136740593409 37778931862957161709568 hp755994 hp740088 556919581 10737418240 1213 10737418240 (@hp792453 Bool.true 15461606859136740593409 37778931862957161709568 hp755994 hp740088 (hd4340 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448) hd5034)

noncomputable def hp792464 := hp792463 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792465 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792466 := hp792465 (Enclosure.sfrac Bool.false 839142 1000) 749551 1000 839142 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792467 := hp792466 (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl rfl rfl rfl

noncomputable def hp792468 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792469 := @hp792468 Bool.false Bool.false 9880340082090028839003 9444732965739290427392 hp756247 hp756249 556919581 10737418240 1213 10737418240 (@hp792456 Bool.false 9880340082090028839003 9444732965739290427392 hp756247 hp756249 (hd4359 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448) hd5035)

noncomputable def hp792470 := hp792469 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792472 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) 839142 1000 840426 1000

noncomputable def hp792473 := hp792472 (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl rfl rfl

noncomputable def hp792474 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473))

noncomputable def hp792475 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 839142 1000) 839142 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl rfl

noncomputable def hp792476 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473))

noncomputable def hp792477 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473)) 9880340082090028839003

noncomputable def hp792478 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 839142 1000))

noncomputable def hp792479 := @hp792477 9444732965739290427392 hp756247 hp756249 (@hp792478 Bool.false 9880340082090028839003 9444732965739290427392 hp756247 hp756249 (hd4340 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473) hd5035)

noncomputable def hp792480 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473)) 6150540751447159970509

noncomputable def hp792481 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 840426 1000))

noncomputable def hp792482 := @hp792480 2361183241434822606848 198057872631613276426921 hp756508 (@hp792481 Bool.true 6150540751447159970509 2361183241434822606848 198057872631613276426921 hp756508 (hd4359 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473) hd5036)

noncomputable def hp792483 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473) hp792475 (hp792476 (hp792479 rfl rfl rfl) (hp792482 rfl rfl rfl))

noncomputable def hp792484 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792485 := hp792484 (Enclosure.sfrac Bool.false 839142 1000) 749551 1000 839142 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792486 := hp792485 (@Eq.refl Real (Enclosure.sfrac Bool.false 839142 1000)) rfl rfl rfl rfl

noncomputable def hp792487 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792488 := @hp792487 Bool.false Bool.false 9880340082090028839003 9444732965739290427392 hp756247 hp756249 556919581 10737418240 1213 10737418240 (@hp792478 Bool.false 9880340082090028839003 9444732965739290427392 hp756247 hp756249 (hd4340 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473) hd5035)

noncomputable def hp792489 := hp792488 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792490 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792491 := hp792490 (Enclosure.sfrac Bool.false 840426 1000) 749551 1000 840426 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792492 := hp792491 (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl rfl rfl rfl

noncomputable def hp792493 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792494 := @hp792493 Bool.true Bool.false 6150540751447159970509 2361183241434822606848 198057872631613276426921 hp756508 556919581 10737418240 1213 10737418240 (@hp792481 Bool.true 6150540751447159970509 2361183241434822606848 198057872631613276426921 hp756508 (hd4359 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473) hd5036)

noncomputable def hp792495 := hp792494 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792497 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) 840426 1000 841709 1000

noncomputable def hp792498 := hp792497 (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl rfl rfl

noncomputable def hp792499 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498))

noncomputable def hp792500 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 840426 1000) 840426 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl rfl

noncomputable def hp792501 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498))

noncomputable def hp792502 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498)) 6150540751447159970509

noncomputable def hp792503 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 840426 1000))

noncomputable def hp792504 := @hp792502 2361183241434822606848 198057872631613276426921 hp756508 (@hp792503 Bool.true 6150540751447159970509 2361183241434822606848 198057872631613276426921 hp756508 (hd4340 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498) hd5036)

noncomputable def hp792505 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498)) 7083401601501882057181

noncomputable def hp792506 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 841709 1000))

noncomputable def hp792507 := @hp792505 4722366482869645213696 hp756765 hp754729 (@hp792506 Bool.false 7083401601501882057181 4722366482869645213696 hp756765 hp754729 (hd4359 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498) hd5037)

noncomputable def hp792508 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498) hp792500 (hp792501 (hp792504 rfl rfl rfl) (hp792507 rfl rfl rfl))

noncomputable def hp792509 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792510 := hp792509 (Enclosure.sfrac Bool.false 840426 1000) 749551 1000 840426 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792511 := hp792510 (@Eq.refl Real (Enclosure.sfrac Bool.false 840426 1000)) rfl rfl rfl rfl

noncomputable def hp792512 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792513 := @hp792512 Bool.true Bool.false 6150540751447159970509 2361183241434822606848 198057872631613276426921 hp756508 556919581 10737418240 1213 10737418240 (@hp792503 Bool.true 6150540751447159970509 2361183241434822606848 198057872631613276426921 hp756508 (hd4340 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498) hd5036)

noncomputable def hp792514 := hp792513 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792515 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792516 := hp792515 (Enclosure.sfrac Bool.false 841709 1000) 749551 1000 841709 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792517 := hp792516 (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl rfl rfl rfl

noncomputable def hp792518 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792519 := @hp792518 Bool.false Bool.false 7083401601501882057181 4722366482869645213696 hp756765 hp754729 556919581 10737418240 1213 10737418240 (@hp792506 Bool.false 7083401601501882057181 4722366482869645213696 hp756765 hp754729 (hd4359 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498) hd5037)

noncomputable def hp792520 := hp792519 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792522 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) 841709 1000 842992 1000

noncomputable def hp792523 := hp792522 (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl rfl rfl

noncomputable def hp792524 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523))

noncomputable def hp792525 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 841709 1000) 841709 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl rfl

noncomputable def hp792526 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523))

noncomputable def hp792527 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523)) 7083401601501882057181

noncomputable def hp792528 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 841709 1000))

noncomputable def hp792529 := @hp792527 4722366482869645213696 hp756765 hp754729 (@hp792528 Bool.false 7083401601501882057181 4722366482869645213696 hp756765 hp754729 (hd4340 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523) hd5037)

noncomputable def hp792530 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523)) 104930076430729689035411

noncomputable def hp792531 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 842992 1000))

noncomputable def hp792532 := @hp792530 18889465931478580854784 1707744940344805006009 hp757025 (@hp792531 Bool.true 104930076430729689035411 18889465931478580854784 1707744940344805006009 hp757025 (hd4359 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523) hd5038)

noncomputable def hp792533 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523) hp792525 (hp792526 (hp792529 rfl rfl rfl) (hp792532 rfl rfl rfl))

noncomputable def hp792534 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792535 := hp792534 (Enclosure.sfrac Bool.false 841709 1000) 749551 1000 841709 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792536 := hp792535 (@Eq.refl Real (Enclosure.sfrac Bool.false 841709 1000)) rfl rfl rfl rfl

noncomputable def hp792537 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792538 := @hp792537 Bool.false Bool.false 7083401601501882057181 4722366482869645213696 hp756765 hp754729 556919581 10737418240 1213 10737418240 (@hp792528 Bool.false 7083401601501882057181 4722366482869645213696 hp756765 hp754729 (hd4340 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523) hd5037)

noncomputable def hp792539 := hp792538 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792540 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792541 := hp792540 (Enclosure.sfrac Bool.false 842992 1000) 749551 1000 842992 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792542 := hp792541 (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl rfl rfl rfl

noncomputable def hp792543 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792544 := @hp792543 Bool.true Bool.false 104930076430729689035411 18889465931478580854784 1707744940344805006009 hp757025 556919581 10737418240 1213 10737418240 (@hp792531 Bool.true 104930076430729689035411 18889465931478580854784 1707744940344805006009 hp757025 (hd4359 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523) hd5038)

noncomputable def hp792545 := hp792544 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792547 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) 842992 1000 844274 1000

noncomputable def hp792548 := hp792547 (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl rfl rfl

noncomputable def hp792549 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548))

noncomputable def hp792550 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 842992 1000) 842992 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl rfl

noncomputable def hp792551 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548))

noncomputable def hp792552 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548)) 104930076430729689035411

noncomputable def hp792553 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 842992 1000))

noncomputable def hp792554 := @hp792552 18889465931478580854784 1707744940344805006009 hp757025 (@hp792553 Bool.true 104930076430729689035411 18889465931478580854784 1707744940344805006009 hp757025 (hd4340 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548) hd5038)

noncomputable def hp792555 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548)) 52372009867399691650209

noncomputable def hp792556 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 844274 1000))

noncomputable def hp792557 := @hp792555 151115727451828646838272 477732781872026344984691 hp757278 (@hp792556 Bool.false 52372009867399691650209 151115727451828646838272 477732781872026344984691 hp757278 (hd4359 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548) hd5039)

noncomputable def hp792558 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548) hp792550 (hp792551 (hp792554 rfl rfl rfl) (hp792557 rfl rfl rfl))

noncomputable def hp792559 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792560 := hp792559 (Enclosure.sfrac Bool.false 842992 1000) 749551 1000 842992 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792561 := hp792560 (@Eq.refl Real (Enclosure.sfrac Bool.false 842992 1000)) rfl rfl rfl rfl

noncomputable def hp792562 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792563 := @hp792562 Bool.true Bool.false 104930076430729689035411 18889465931478580854784 1707744940344805006009 hp757025 556919581 10737418240 1213 10737418240 (@hp792553 Bool.true 104930076430729689035411 18889465931478580854784 1707744940344805006009 hp757025 (hd4340 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548) hd5038)

noncomputable def hp792564 := hp792563 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792565 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792566 := hp792565 (Enclosure.sfrac Bool.false 844274 1000) 749551 1000 844274 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792567 := hp792566 (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl rfl rfl rfl

noncomputable def hp792568 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792569 := @hp792568 Bool.false Bool.false 52372009867399691650209 151115727451828646838272 477732781872026344984691 hp757278 556919581 10737418240 1213 10737418240 (@hp792556 Bool.false 52372009867399691650209 151115727451828646838272 477732781872026344984691 hp757278 (hd4359 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548) hd5039)

noncomputable def hp792570 := hp792569 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792572 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) 844274 1000 845556 1000

noncomputable def hp792573 := hp792572 (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl rfl rfl

noncomputable def hp792574 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573))

noncomputable def hp792575 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 844274 1000) 844274 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl rfl

noncomputable def hp792576 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573))

noncomputable def hp792577 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573)) 52372009867399691650209

noncomputable def hp792578 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 844274 1000))

noncomputable def hp792579 := @hp792577 151115727451828646838272 477732781872026344984691 hp757278 (@hp792578 Bool.false 52372009867399691650209 151115727451828646838272 477732781872026344984691 hp757278 (hd4340 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573) hd5039)

noncomputable def hp792580 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573)) 76793180622600504301829

noncomputable def hp792581 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 845556 1000))

noncomputable def hp792582 := @hp792580 37778931862957161709568 hp757535 hp741590 (@hp792581 Bool.true 76793180622600504301829 37778931862957161709568 hp757535 hp741590 (hd4359 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573) hd5040)

noncomputable def hp792583 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573) hp792575 (hp792576 (hp792579 rfl rfl rfl) (hp792582 rfl rfl rfl))

noncomputable def hp792584 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792585 := hp792584 (Enclosure.sfrac Bool.false 844274 1000) 749551 1000 844274 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792586 := hp792585 (@Eq.refl Real (Enclosure.sfrac Bool.false 844274 1000)) rfl rfl rfl rfl

noncomputable def hp792587 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792588 := @hp792587 Bool.false Bool.false 52372009867399691650209 151115727451828646838272 477732781872026344984691 hp757278 556919581 10737418240 1213 10737418240 (@hp792578 Bool.false 52372009867399691650209 151115727451828646838272 477732781872026344984691 hp757278 (hd4340 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573) hd5039)

noncomputable def hp792589 := hp792588 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792590 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792591 := hp792590 (Enclosure.sfrac Bool.false 845556 1000) 749551 1000 845556 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792592 := hp792591 (@Eq.refl Real (Enclosure.sfrac Bool.false 845556 1000)) rfl rfl rfl rfl

noncomputable def hp792593 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792594 := @hp792593 Bool.true Bool.false 76793180622600504301829 37778931862957161709568 hp757535 hp741590 556919581 10737418240 1213 10737418240 (@hp792581 Bool.true 76793180622600504301829 37778931862957161709568 hp757535 hp741590 (hd4359 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573) hd5040)

noncomputable def hp792595 := hp792594 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl
open Zeta.Certificates
noncomputable def certificatePairs : List (Σ' I : ZIntervalRS, I.Certified) := [(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 830146 1000) (Enclosure.sfrac Bool.false 831433 1000) hp792298) (hp792299 (hp792308 (hp792311 (hp792314 rfl rfl)) (hp792317 (hp792320 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 831433 1000) (Enclosure.sfrac Bool.false 832719 1000) hp792323) (hp792324 (hp792333 (hp792336 (hp792339 rfl rfl)) (hp792342 (hp792345 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 832719 1000) (Enclosure.sfrac Bool.false 834004 1000) hp792348) (hp792349 (hp792358 (hp792361 (hp792364 rfl rfl)) (hp792367 (hp792370 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 834004 1000) (Enclosure.sfrac Bool.false 835932 1000) hp792373) (hp792374 (hp792383 (hp792386 (hp792389 rfl rfl)) (hp792392 (hp792395 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 835932 1000) (Enclosure.sfrac Bool.false 836975 1000) hp792398) (hp792399 (hp792408 (hp792411 (hp792414 rfl rfl)) (hp792417 (hp792420 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 836975 1000) (Enclosure.sfrac Bool.false 837617 1000) hp792423) (hp792424 (hp792433 (hp792436 (hp792439 rfl rfl)) (hp792442 (hp792445 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 837617 1000) (Enclosure.sfrac Bool.false 839142 1000) hp792448) (hp792449 (hp792458 (hp792461 (hp792464 rfl rfl)) (hp792467 (hp792470 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 839142 1000) (Enclosure.sfrac Bool.false 840426 1000) hp792473) (hp792474 (hp792483 (hp792486 (hp792489 rfl rfl)) (hp792492 (hp792495 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 840426 1000) (Enclosure.sfrac Bool.false 841709 1000) hp792498) (hp792499 (hp792508 (hp792511 (hp792514 rfl rfl)) (hp792517 (hp792520 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 841709 1000) (Enclosure.sfrac Bool.false 842992 1000) hp792523) (hp792524 (hp792533 (hp792536 (hp792539 rfl rfl)) (hp792542 (hp792545 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 842992 1000) (Enclosure.sfrac Bool.false 844274 1000) hp792548) (hp792549 (hp792558 (hp792561 (hp792564 rfl rfl)) (hp792567 (hp792570 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 844274 1000) (Enclosure.sfrac Bool.false 845556 1000) hp792573) (hp792574 (hp792583 (hp792586 (hp792589 rfl rfl)) (hp792592 (hp792595 rfl rfl)))))]

theorem solution : Zeta.Certificates.BatchSpec 12 830146 1000 845556 1000 :=
  ⟨CertifiedZeroIntervals.ofCertifiedRS certificatePairs (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.singleton _)))))))))))), rfl, rfl, rfl⟩
#print axioms solution
