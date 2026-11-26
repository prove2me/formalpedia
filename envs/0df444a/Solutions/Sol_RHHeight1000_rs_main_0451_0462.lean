-- Prove2me | solution 1 for RHHeight1000.rs_main_0451_0462
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:34:58.744698+00:00
-- url     : https://prove2.me/submissions/2a1a47dd-247e-4d8a-a454-ee9e4df0980f

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

noncomputable def hp631148 := nat_lit 1208925819614629174706176000000000000000

noncomputable def hp632690 := nat_lit 60446290980731458735308800000000000000

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

noncomputable def hp738860 := nat_lit 51426570998450436377149440000

noncomputable def hp739140 := nat_lit 4460544000000000000000000

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

noncomputable def hp742094 := nat_lit 12856642749612609094287360000

noncomputable def hp742826 := nat_lit 3868562622766813359059763200000000000000

noncomputable def hp743344 := nat_lit 5142657099845043637714944000

noncomputable def hp743892 := nat_lit 1622016000000000000000000

noncomputable def hp744350 := nat_lit 4285547583204203031429120000

noncomputable def hp745658 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600

noncomputable def hp745661 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600

noncomputable def hp746621 := nat_lit 5133330660362904937396483134791632965849700352038159351603073932373040875403608499582161387520

noncomputable def hp746624 := nat_lit 230999879716330722182841741065623483463236515841717170822138326956786839393162382481197262438400

noncomputable def hp749778 := nat_lit 42817430781178796431748579083484854091482398720

noncomputable def hp749779 := nat_lit 299722015468251575022240053584393978640376791040

noncomputable def hp750331 := nat_lit 1071386895801050757857280000

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

noncomputable def hp751615 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 815969 1000)) Bool.false 90151228217801955985693 18889465931478580854784 1190095007903759139496411

noncomputable def hp751616 := nat_lit 1607080343701576136785920000

noncomputable def hp751617 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 815969 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 815969 1000)) Bool.false 90151228217801955985693 18889465931478580854784

noncomputable def hp751618 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 815969 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751619 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp751618 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751620 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 815969 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751621 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp751619 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp751622 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 815969 1000)) hp751621 Bool.false 90151228217801955985693 18889465931478580854784

noncomputable def hp751623 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 815969 1000) 815969 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl

noncomputable def hp751624 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp751619 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp751625 := nat_lit 24199786055605735372711429931008

noncomputable def hp751626 := @hp751624 1249167547 268435456 24751 33554432 2248876667918884915485 18889465931478580854784 4652632155669856936411 hp751616 hp751625 90151228217801955985693 18889465931478580854784

noncomputable def hp751627 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) 11)

noncomputable def hp751628 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) 11) hp751627

noncomputable def hp751629 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) 11)

noncomputable def hp751630 := @hp751629 1249167547 536870912 198008 536870912 1249167547 536870912 198008 536870912 1341283440397385728 1249167547 268435456

noncomputable def hp751631 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp751632 := hp751631 BSN.quadSignNeg 9 10 11 815969 1000 192 241 536870912 268435456 9007199254740992

noncomputable def hp751633 := hp751632 Bool.false 846687900172 3718 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp751634 := hp751633 Bool.false 1214996990 169985 Bool.true 89145550 Bool.true 519250756 28296951008113761 1 Bool.false 529486746

noncomputable def hp751635 := hp751634 Bool.false Bool.false 441999505 Bool.true Bool.false 1249167547 198008 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 529486746 536870912) BSN.abs_quadSignNeg

noncomputable def hp751636 := hp751631 BSN.quadSignNeg 7 8 9 815969 1000 76 137 536870912 268435456 9007199254740992

noncomputable def hp751637 := hp751636 Bool.false 846687900172 3718 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp751638 := hp751637 Bool.false 1133076347 138827 Bool.true 161170205 Bool.true 316169646 28296951008113761 1 Bool.false 512860170

noncomputable def hp751639 := hp751638 Bool.false Bool.false 298208444 Bool.true Bool.false 1214996990 169985 BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 512860170 536870912) BSN.abs_quadSignNeg

noncomputable def hp751640 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp751641 := hp751640 BSN.quadSignNeg 5 6 7 815969 1000 73 6 536870912 268435456 9007199254740992

noncomputable def hp751642 := hp751641 Bool.false 846687900172 3718 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp751643 := hp751642 Bool.false 1271152318 103166 Bool.false 209812966 Bool.true 697098366 28296951008113761 1 Bool.false 204512806

noncomputable def hp751644 := hp751643 Bool.true Bool.false 144415600 Bool.true Bool.false 1133076347 138827 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 204512806 536870912) BSN.abs_quadSignNeg

noncomputable def hp751645 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp751646 := hp751645 BSN.quadSignPos 3 4 5 815969 1000 283 167 536870912 268435456 9007199254740992

noncomputable def hp751647 := hp751646 Bool.false 846687900172 3718 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp751648 := hp751647 Bool.false 768509225 60979 Bool.false 735807003 Bool.false 807831658 28296951008113761 1 Bool.false 526142664

noncomputable def hp751649 := hp751648 Bool.false Bool.false 535698750 Bool.false Bool.false 1271152318 103166 BSN.abs_quadSignPos (BSN.cos_quad_nat3 283 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 526142664 536870912) BSN.abs_quadSignPos

noncomputable def hp751650 := hp751645 BSN.quadSignNeg 1 2 3 815969 1000 643 433 536870912 268435456 9007199254740992

noncomputable def hp751651 := hp751650 Bool.false 846687900172 3718 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp751652 := hp751651 Bool.false 536870864 3778 Bool.false 789459564 Bool.false 263463079 28296951008113761 1 Bool.false 534171975

noncomputable def hp751653 := hp751652 Bool.false Bool.false 253014977 Bool.true Bool.false 768509225 60979 BSN.abs_quadSignPos (BSN.cos_quad_nat3 643 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 534171975 536870912) BSN.abs_quadSignNeg

noncomputable def hp751654 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) 1) Bool.false

noncomputable def hp751655 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)))

noncomputable def hp751656 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000))) Bool.false 67108858 67108864

noncomputable def hp751657 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 105835987521) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 105835987521 67108864

noncomputable def hp751658 := nat_lit 75467193693125060625731193233689439640552170597172679438223

noncomputable def hp751659 := nat_lit 47852509875080674580119826770955023161873159407271936000

noncomputable def hp751660 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) Bool.false hp751658 hp751659 123540140979036167687

noncomputable def hp751661 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 815969 4000) (Real.log (Enclosure.sfrac Bool.false 2663222635844 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1631938))))))

noncomputable def hp751662 := nat_lit 173624076209289253365604520407520000

noncomputable def hp751663 := nat_lit 850031331990675812806298714913478121280

noncomputable def hp751664 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp751661 (Enclosure.sfrac Bool.false 815969 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 815969 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp751662 hp751663)) Bool.false

noncomputable def hp751665 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 815969 1000) 815969 1000 2663222635844 16000000 1631938

noncomputable def hp751666 := hp751665 4000 2000 hp751662 hp751663 (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl rfl rfl rfl

noncomputable def hp751667 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp751661 (Enclosure.sfrac Bool.false 815969 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 815969 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp751662 hp751663) 28410135251106509206087 18014398509481984000

noncomputable def hp751668 := nat_lit 24149501981800019400233981834780620684976694591095257420231360

noncomputable def hp751669 := @hp751667 123540140979036167687 hp738659 hp751662 hp751663 0 1 hp751668 hp751658 hp751659 123540140979036167687 hp738659

noncomputable def hp751670 := @Enclosure.Real.IsNear.subLit_ff_p (hp751661 (Enclosure.sfrac Bool.false 815969 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 815969 2000) (Real.log Real.pi)) 36823436693775119659591 18014398509481984000 10299627606578597 4356000000000000000000

noncomputable def hp751671 := nat_lit 1906571902788112575826040455168000

noncomputable def hp751672 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 815969 4000) (Real.log (Enclosure.sfrac Bool.false 2663222635844 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1631938))))))

noncomputable def hp751673 := @hp751672 (Enclosure.sfrac Bool.false 815969 2000) 44173032062466872160839 18014398509481984000 10299627606578597 4356000000000000000000 815969 2000 0

noncomputable def hp751674 := nat_lit 73646873387550239319182000

noncomputable def hp751675 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 815969 4000) (Real.log (Enclosure.sfrac Bool.false 2663222635844 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1631938))))) 44180103540568195192839

noncomputable def hp751676 := nat_lit 99468825368175388925213465337577603072

noncomputable def hp751677 := @hp751675 18014398509481984000 927238873275827 396000000000000000000 883934762665379 2251799813685248 200000001089 8712000000000000000 hp751676 44173032062466872160839 18014398509481984000 10299627606578597

noncomputable def hp751678 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 815969 4000) (Real.log (Enclosure.sfrac Bool.false 2663222635844 16000000)) 815969 4000 0 1 54144340704816231 4503599627370496

noncomputable def hp751679 := nat_lit 116274086295333650917490688

noncomputable def hp751680 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2663222635844) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp751679 hp617687

noncomputable def hp751681 := BSN.log_rat_reduce_isNear 2663222635844 16000000 17 5326445271688 4194304000000 64144443 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp751682 := nat_lit 249207362438702621090540950983068926213121914654675683327142007788931488272566578304300694585081498501120

noncomputable def hp751683 := nat_lit 1184690764240144556969368293232245526639655755500771726129107990428309945095793150302384154602757423104

noncomputable def hp751684 := nat_lit 1107017063865375688531108926342347369258062644663962740197259278542677730152347036559940682055680

noncomputable def hp751685 := BSN.log_dyadic_bound 566070635844 4760374635844 5 4 hp751682 268435456 87120000 hp751683 hp751684 64144443 5326445271688

noncomputable def hp751686 := hp751685 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp751687 := @BSN.binarySplit_of_base4 (BSN.artanhP 566070635844) (BSN.artanhQ 4760374635844) 0 4 hp751683 hp751682 hp751684 rfl rfl rfl

noncomputable def hp751688 := hp751681 rfl rfl rfl rfl (hp751686 (hp751687 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp751689 := @hp751678 12500018513 1089000000000000000 44180103540568195192839 18014398509481984000 927238873275827 396000000000000000000 (Enclosure.Real.IsNear.const Bool.false 815969 4000) (BSN.isNear_log_sfrac 2663222635844 16000000 54144340704816231 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp751680 1000001481040000 87120000000000000000000 54144340704816231 4503599627370496 12500018513 1089000000000000000 (hp751688 rfl rfl rfl) rfl)) rfl

noncomputable def hp751690 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1631938)))) 1 4

noncomputable def hp751691 := @hp751690 0 1 883934762665379 562949953421312 200000001089 2178000000000000000 883934762665379 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp751692 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1631938))) 884279719003555 562949953421312 1

noncomputable def hp751693 := @hp751692 2000000000000000 20561 33554432 1 10890000 29659928886291598409728 883934762665379 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp751694 := BSN.arctan_dyadic_bound_f 1000 1631938 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp751695 := hp751694 1 20561 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1631938) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1631938) 0 0 rfl)

noncomputable def hp751696 := hp751691 (hp751693 (hp751695 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp751697 := @hp751670 31341990242409 67108864000 2447907 536870912000 hp751671 28410135251106509206087 18014398509481984000 123540140979036167687 hp738659 (@hp751673 1 hp751674 36823436693775119659591 18014398509481984000 10299627606578597 4356000000000000000000 (@hp751677 4356000000000000000000 hp751689 hp751696 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 815969 2000) rfl rfl)

noncomputable def hp751698 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 815969 2000) (Real.log Real.pi) 815969 2000 0 1 38410761 33554432

noncomputable def hp751699 := hp751697 (@hp751698 3 268435456 31341990242409 67108864000 2447907 536870912000 (Enclosure.Real.IsNear.const Bool.false 815969 2000) hd4909 rfl) rfl

noncomputable def hp751700 := @hp751660 hp738659 105835987521 67108864 233 33554432 (@hp751664 hp751658 hp751659 123540140979036167687 hp738659 (hp751666 rfl rfl rfl rfl rfl) (hp751669 (hp751699 rfl) (Enclosure.Real.IsNear.const Bool.true hp751662 hp751663) rfl rfl)) rfl

noncomputable def hp751701 := nat_lit 15187922553860278244605952

noncomputable def hp751702 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 105835987521) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp751701) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp751703 := BSN.sin_reduce_arg_pos_rat_q3 105835987521 67108864 226375608064910080 72057594037927936 250 hp751701 hp617687 rfl rfl rfl rfl

noncomputable def hp751704 := nat_lit 14365639407546587698190782217863530722523457480115761676457667098407931470238344129729635304546879297718540336738124631283071720712076403347456

noncomputable def hp751705 := nat_lit 10219340754297552266381941811302302390940085663867350691004148382455083236880373344989872329910648701301812219668766957802255761888710656

noncomputable def hp751706 := nat_lit 71739032818960687794583320990870530893205805545839534772666115867748984100973218297800530437752661029357460463947231132886012349408493482479616

noncomputable def hp751707 := BSN.sin_dyadic_bound_f 215833360838 137438953472 4 3 67108864 21801270 hp751704 hp737934 hp751705 hp751706 hp737937

noncomputable def hp751708 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215833360838) (BSN.sinEvenQ 137438953472) 0 3 hp751704 hp737934 hp751705 rfl rfl rfl

noncomputable def hp751709 := hp751707 hp751705 67108858 rfl rfl rfl rfl rfl rfl rfl rfl (hp751708 rfl)

noncomputable def hp751710 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215833360838) (BSN.sinOddQ 137438953472) 0 3 hp751706 hp737937 hp751705 rfl rfl rfl

noncomputable def hp751711 := @BSN.sin_arg_round Bool.false 67108858 67108864 hp751701 hp617687 215833360838 137438953472 21801270 21780000 (hp751709 (hp751710 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751712 := hp751702 67108858 67108864 250 1000000000000000 21780000 10890000 hp751703 BSN.pi_near_15 hp751711 rfl rfl

noncomputable def hp751713 := @hp751657 233 33554432 Bool.false 67108858 67108864 1 10890000 hp751700 (Enclosure.sfrac_false_div 105835987521 67108864) (hp751712 rfl rfl) rfl

noncomputable def hp751714 := @hp751654 33554429 33554432 160682777 22837985280000 536870864 536870912 3778 536870912 (@hp751655 Bool.false 33554429 33554432 160682777 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000)) (@hp751656 2570924432 365407764480000 33554429 33554432 160682777 22837985280000 (hp751713 rfl) rfl))

noncomputable def hp751715 := @hp751660 hp738659 846687900172 536870912 3718 536870912 (@hp751664 hp751658 hp751659 123540140979036167687 hp738659 (hp751666 rfl rfl rfl rfl rfl) (hp751669 (hp751699 rfl) (Enclosure.Real.IsNear.const Bool.true hp751662 hp751663) rfl rfl)) rfl

noncomputable def hp751716 := hp751653 (BSN.cos_quad_nat1 433 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 253014977 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl rfl (hp751714 rfl) hp751715

noncomputable def hp751717 := nat_lit 139331330677878306183548960512474323226575499058098819156452231627409116879307200991957875961877300886413556842496

noncomputable def hp751718 := nat_lit 58608240706804375483344403203994453256343565662535004769946805284010211257760910831115567526019246583709696

noncomputable def hp751719 := nat_lit 695991571309906041701748034241210770928138299042303760898569333816541319988257806254291465703211641367959548461056

noncomputable def hp751720 := BSN.sin_dyadic_bound_f 789459564 536870912 4 3 536870912 268435456 hp751717 hp642702 hp751718 hp751719 hp642705

noncomputable def hp751721 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 789459564) (BSN.sinEvenQ 536870912) 0 3 hp751717 hp642702 hp751718 rfl rfl rfl

noncomputable def hp751722 := hp751720 hp751718 534171975 rfl rfl rfl rfl rfl rfl rfl rfl (hp751721 rfl)

noncomputable def hp751723 := @BSN.binarySplit_of_base3 (BSN.sinOddP 789459564) (BSN.sinOddQ 536870912) 0 3 hp751719 hp642705 hp751718 rfl rfl rfl

noncomputable def hp751724 := nat_lit 1210455044880423064308417468124184062021527881455159805977892230207748545

noncomputable def hp751725 := nat_lit 23214434228813098960220418684597973144154314661751283778859050842561

noncomputable def hp751726 := nat_lit 3170201817983785185314205392980707003814149153968347132625504354937977281

noncomputable def hp751727 := BSN.sin_dyadic_bound_f 263463079 536870912 3 2 536870912 268435456 hp751724 hp708845 hp751725 hp751726 hp708848

noncomputable def hp751728 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 263463079) (BSN.sinEvenQ 536870912) 0 2 hp751724 hp708845 hp751725 rfl rfl rfl

noncomputable def hp751729 := hp751727 hp751725 253014977 rfl rfl rfl rfl rfl rfl rfl rfl (hp751728 rfl)

noncomputable def hp751730 := @BSN.binarySplit_of_base2 (BSN.sinOddP 263463079) (BSN.sinOddQ 536870912) 0 2 hp751726 hp708848 hp751725 rfl rfl rfl

noncomputable def hp751731 := hp751716 hd4911 hd4913 hd4915 hd4917 hd4918 (hp751722 (hp751723 rfl) rfl rfl rfl rfl) (hp751729 (hp751730 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751732 := hp751649 (BSN.cos_quad_nat3 167 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 535698750 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl rfl (hp751731 rfl rfl rfl rfl rfl) hp751715

noncomputable def hp751733 := nat_lit 105104248910869065338367925840263706364118600074254936075779400673419511923554258282084739114339553662058852818641

noncomputable def hp751734 := nat_lit 25186452558724138024864087742159812570060647000127987401850069688838679974035039462007358742655937298079441

noncomputable def hp751735 := nat_lit 525142531832222866653552096755343363450824930412526037927592912628254438430894033110113628304856654349712674299601

noncomputable def hp751736 := BSN.sin_dyadic_bound_f 735807003 536870912 4 3 536870912 268435456 hp751733 hp642702 hp751734 hp751735 hp642705

noncomputable def hp751737 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 735807003) (BSN.sinEvenQ 536870912) 0 3 hp751733 hp642702 hp751734 rfl rfl rfl

noncomputable def hp751738 := hp751736 hp751734 526142664 rfl rfl rfl rfl rfl rfl rfl rfl (hp751737 rfl)

noncomputable def hp751739 := @BSN.binarySplit_of_base3 (BSN.sinOddP 735807003) (BSN.sinOddQ 536870912) 0 3 hp751735 hp642705 hp751734 rfl rfl rfl

noncomputable def hp751740 := nat_lit 152783816165763211354025481939653965902170928504988322560949968774615037377706638619274881233015118434977910951936

noncomputable def hp751741 := nat_lit 77241451098090627914737559877113154012203322897598922265258635697369305666401118515506093740026888550158336

noncomputable def hp751742 := nat_lit 763119582008889786294359837933661819175794352626980000690757185745661238018052029068663083588305420046005752631296

noncomputable def hp751743 := BSN.sin_dyadic_bound_f 807831658 536870912 4 3 536870912 268435456 hp751740 hp642702 hp751741 hp751742 hp642705

noncomputable def hp751744 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 807831658) (BSN.sinEvenQ 536870912) 0 3 hp751740 hp642702 hp751741 rfl rfl rfl

noncomputable def hp751745 := hp751743 hp751741 535698750 rfl rfl rfl rfl rfl rfl rfl rfl (hp751744 rfl)

noncomputable def hp751746 := @BSN.binarySplit_of_base3 (BSN.sinOddP 807831658) (BSN.sinOddQ 536870912) 0 3 hp751742 hp642705 hp751741 rfl rfl rfl

noncomputable def hp751747 := hp751732 hd4920 hd4922 hd4924 hd4926 hd4918 (hp751738 (hp751739 rfl) rfl rfl rfl rfl) (hp751745 (hp751746 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751748 := hp751644 (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 144415600 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl rfl (hp751747 rfl rfl rfl rfl rfl) hp751715

noncomputable def hp751749 := nat_lit 1937890763171655989428727024728336

noncomputable def hp751750 := BSN.sin_dyadic_bound_f 209812966 536870912 2 1 536870912 268435456 hp751749 hp708890 hp751749 hp751749 hp708891

noncomputable def hp751751 := @BSN.binarySplit_of_base (BSN.sinEvenP 209812966) (BSN.sinEvenQ 536870912) 0 1 hp751749 hp708890 hp751749 rfl rfl rfl

noncomputable def hp751752 := hp751750 hp751749 204512806 rfl rfl rfl rfl rfl rfl rfl rfl (hp751751 rfl)

noncomputable def hp751753 := @BSN.binarySplit_of_base (BSN.sinOddP 209812966) (BSN.sinOddQ 536870912) 0 1 hp751749 hp708891 hp751749 rfl rfl rfl

noncomputable def hp751754 := nat_lit 32583320063698077325233348792593957927595203863638982683139057432013796067732432588706438244339398197586233921536

noncomputable def hp751755 := nat_lit 13168271647822608867008767161296001683176440278224171608542203270317771648085113369075270057025251191033856

noncomputable def hp751756 := nat_lit 197449484139261531918463994036487829098749326118604750263900504828300373922880273480034972244976424364264955842560

noncomputable def hp751757 := BSN.cos_dyadic_bound_f 697098366 536870912 4 3 536870912 268435456 hp751754 hp716712 hp751755 hp751756 hp716714

noncomputable def hp751758 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 697098366) (BSN.cosEvenQ 536870912) 0 3 hp751754 hp716712 hp751755 rfl rfl rfl

noncomputable def hp751759 := hp751757 hp751755 144415600 rfl rfl rfl rfl rfl rfl rfl rfl (hp751758 rfl)

noncomputable def hp751760 := @BSN.binarySplit_of_base3 (BSN.cosOddP 697098366) (BSN.cosOddQ 536870912) 0 3 hp751756 hp716714 hp751755 rfl rfl rfl

noncomputable def hp751761 := hp751748 hd4928 hd4930 hd4932 hd4934 hd4918 (hp751752 (hp751753 rfl) rfl rfl rfl rfl) (hp751759 (hp751760 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751762 := hp751639 (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 298208444 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl rfl (hp751761 rfl rfl rfl rfl rfl) hp751715

noncomputable def hp751763 := nat_lit 94173760236221338818511596996823033666311711183818180167515409016190625

noncomputable def hp751764 := nat_lit 455279469442483523485097307650340365598876631636928380648875390625

noncomputable def hp751765 := nat_lit 282520370149725131488487820795853800318203935798191266645784929297790625

noncomputable def hp751766 := BSN.cos_dyadic_bound_f 161170205 536870912 3 2 536870912 268435456 hp751763 hp708868 hp751764 hp751765 hp708870

noncomputable def hp751767 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 161170205) (BSN.cosEvenQ 536870912) 0 2 hp751763 hp708868 hp751764 rfl rfl rfl

noncomputable def hp751768 := hp751766 hp751764 512860170 rfl rfl rfl rfl rfl rfl rfl rfl (hp751767 rfl)

noncomputable def hp751769 := @BSN.binarySplit_of_base2 (BSN.cosOddP 161170205) (BSN.cosOddQ 536870912) 0 2 hp751765 hp708870 hp751764 rfl rfl rfl

noncomputable def hp751770 := nat_lit 2510494358786448684654370445583160284423844091677892290463075132236120320

noncomputable def hp751771 := nat_lit 99853061242774983749595819161214379878899844692388931070209512980736

noncomputable def hp751772 := nat_lit 6574942606151067776502042297582015921637882973693549273895845007121203456

noncomputable def hp751773 := BSN.sin_dyadic_bound_f 316169646 536870912 3 2 536870912 268435456 hp751770 hp708845 hp751771 hp751772 hp708848

noncomputable def hp751774 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 316169646) (BSN.sinEvenQ 536870912) 0 2 hp751770 hp708845 hp751771 rfl rfl rfl

noncomputable def hp751775 := hp751773 hp751771 298208444 rfl rfl rfl rfl rfl rfl rfl rfl (hp751774 rfl)

noncomputable def hp751776 := @BSN.binarySplit_of_base2 (BSN.sinOddP 316169646) (BSN.sinOddQ 536870912) 0 2 hp751772 hp708848 hp751771 rfl rfl rfl

noncomputable def hp751777 := hp751762 hd4936 hd4938 hd4940 hd4942 hd4918 (hp751768 (hp751769 rfl) rfl rfl rfl rfl) (hp751775 (hp751776 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751778 := hp751635 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 441999505 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl rfl (hp751777 rfl rfl rfl rfl rfl) hp751715

noncomputable def hp751779 := nat_lit 63153681878879900236464006250000

noncomputable def hp751780 := BSN.cos_dyadic_bound_f 89145550 536870912 2 1 536870912 268435456 hp751779 hp708767 hp751779 hp751779 hp708768

noncomputable def hp751781 := @BSN.binarySplit_of_base (BSN.cosEvenP 89145550) (BSN.cosEvenQ 536870912) 0 1 hp751779 hp708767 hp751779 rfl rfl rfl

noncomputable def hp751782 := hp751780 hp751779 529486746 rfl rfl rfl rfl rfl rfl rfl rfl (hp751781 rfl)

noncomputable def hp751783 := @BSN.binarySplit_of_base (BSN.cosOddP 89145550) (BSN.cosOddQ 536870912) 0 1 hp751779 hp708768 hp751779 rfl rfl rfl

noncomputable def hp751784 := nat_lit 18268188563387377708200410864216427285021554296588934971654148204814991360

noncomputable def hp751785 := nat_lit 5284660594525210347306754239681114135746579206347780174939862157295616

noncomputable def hp751786 := nat_lit 47836699644099615085676865137512111561693814410446457091191914092927451136

noncomputable def hp751787 := BSN.sin_dyadic_bound_f 519250756 536870912 3 2 536870912 268435456 hp751784 hp708845 hp751785 hp751786 hp708848

noncomputable def hp751788 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 519250756) (BSN.sinEvenQ 536870912) 0 2 hp751784 hp708845 hp751785 rfl rfl rfl

noncomputable def hp751789 := hp751787 hp751785 441999505 rfl rfl rfl rfl rfl rfl rfl rfl (hp751788 rfl)

noncomputable def hp751790 := @BSN.binarySplit_of_base2 (BSN.sinOddP 519250756) (BSN.sinOddQ 536870912) 0 2 hp751786 hp708848 hp751785 rfl rfl rfl

noncomputable def hp751791 := hp751778 hd4944 hd4946 hd4961 hd4963 hd4918 (hp751782 (hp751783 rfl) rfl rfl rfl rfl) (hp751789 (hp751790 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751792 := @hp751630 24751 33554432 (hp751791 rfl rfl rfl rfl rfl) (hp751791 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp751793 := @hp751628 Bool.false 1249167547 268435456 24751 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 815969 1000)) (Enclosure.sfrac Bool.false 815969 1000) 11) hp751792

noncomputable def hp751794 := @Enclosure.Real.IsNear.mulLit_tf hp751619 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1))) 19879545 67108864 1

noncomputable def hp751795 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp751618 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751796 := @hp751795 1 1 0 1 19879545 67108864 1 67108864 19879545 67108864 1

noncomputable def hp751797 := @Enclosure.Real.IsNear.of_eq (hp751618 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751798 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 815969 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751799 := @hp751797 (@Inv.inv Real Real.instInv (Real.sqrt hp751620)) Bool.false 19879545 67108864 1 67108864 (hp751798 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 815969 1000) 815969 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000))))

noncomputable def hp751800 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp751620)) Bool.false 19879545 67108864 1 67108864 19879545 67108864

noncomputable def hp751801 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp751620) Bool.false 226544400 67108864 6 67108864 14159025 4194304 3 33554432

noncomputable def hp751802 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 815969 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751803 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 815969 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751804 := @hp751803 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 815969 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8715125810083

noncomputable def hp751805 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 815969 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 815969 1000 0

noncomputable def hp751806 := @hp751805 1 10680707 67108864 1 67108864 8715125810083 67108864000 815969 67108864000 (Enclosure.Real.IsNear.const Bool.false 815969 1000) hd4949

noncomputable def hp751807 := @hp751804 67108864000 815969 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 815969 1000) 815969 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000))) (hp751806 rfl)

noncomputable def hp751808 := @hp751802 8715125810083 67108864000 815969 67108864000 382381399 382381436 33554432 hp751807 rfl rfl rfl

noncomputable def hp751809 := @Enclosure.Real.IsNear.recentre' hp751620 Bool.false 764762835 67108864 37 67108864 764762835 67108864 37 67108864 (hp751808 rfl rfl rfl)

noncomputable def hp751810 := @Enclosure.Real.IsNear.sqrt_image hp751620 764762835 67108864 37 67108864 113272197 113272203 33554432 (hp751809 rfl) rfl rfl

noncomputable def hp751811 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp751620) 14159025 4194304 3 33554432 9939772 9939773 33554432 (hp751801 (hp751810 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp751812 := @hp751796 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp751799 (@hp751800 1 67108864 (hp751811 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp751813 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751814 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp751815 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1))) (hp751813 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751814 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp751816 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 815969 1000) 815969 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl

noncomputable def hp751817 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751818 := @hp751817 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751814 (Enclosure.sfrac Bool.false 1 16)))) 21145083

noncomputable def hp751819 := @hp751818 16777216 95 16777216 5349951 16777216 288014929 45675970560000 113125157940933 281474976710656 3736912446062431 383157812047380480000

noncomputable def hp751820 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751821 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751822 := @hp751820 (@Neg.neg Real Real.instNeg hp751821) Bool.true 21145083 16777216 95 16777216 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751823 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp751824 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp751825 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp751826 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 166914897) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp751827 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1))) Bool.false 23491183431916428751705

noncomputable def hp751828 := nat_lit 998484790362824137546081731

noncomputable def hp751829 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp751830 := @Enclosure.Real.IsNear.subLit_ff_p hp751620 (Enclosure.sfrac Bool.false 11 1) 764762835 67108864 37 67108864 11 1 0

noncomputable def hp751831 := @hp751829 500000000000000 26565331 67108864 37 67108864 23491183431916428751705 9444732965739290427392 hp751828 hp738031 hd4948 (@hp751830 1 26565331 26565331 67108864 37 67108864 (hp751809 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751832 := @hp751826 166914897 67108864 233 67108864 Bool.true 53246417 67108864 1 10890000 (@hp751827 9444732965739290427392 hp751828 hp738031 166914897 67108864 233 67108864 (hp751831 rfl) rfl) (Enclosure.sfrac_false_div 166914897 67108864)

noncomputable def hp751833 := nat_lit 8863161879271757330776064

noncomputable def hp751834 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 166914897) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp751833) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp751835 := BSN.sin_reduce_arg_pos_rat_q1 166914897 67108864 226375608064910080 72057594037927936 0 hp751833 hp617687 rfl rfl rfl rfl

noncomputable def hp751836 := nat_lit 271617629342988381773461382861367710799248188974562425306590600852239851923143415236106566465

noncomputable def hp751837 := nat_lit 63338977370596331396644829057862905109894406095874447875701654523693505213162851979410241

noncomputable def hp751838 := nat_lit 711276956601607653441566196818440797865948284942555888601652818600923156028363823858026724161

noncomputable def hp751839 := BSN.sin_dyadic_bound_f 125953105783 137438953472 3 2 67108864 21801270 hp751836 hp738039 hp751837 hp751838 hp738042

noncomputable def hp751840 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 125953105783) (BSN.sinEvenQ 137438953472) 0 2 hp751836 hp738039 hp751837 rfl rfl rfl

noncomputable def hp751841 := hp751839 hp751837 53246417 rfl rfl rfl rfl rfl rfl rfl rfl (hp751840 rfl)

noncomputable def hp751842 := @BSN.binarySplit_of_base2 (BSN.sinOddP 125953105783) (BSN.sinOddQ 137438953472) 0 2 hp751838 hp738042 hp751837 rfl rfl rfl

noncomputable def hp751843 := @BSN.sin_arg_round Bool.false 53246417 67108864 hp751833 hp617687 125953105783 137438953472 21801270 21780000 (hp751841 (hp751842 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751844 := hp751834 53246417 67108864 0 1000000000000000 21780000 10890000 hp751835 BSN.pi_near_15 hp751843 rfl rfl

noncomputable def hp751845 := @hp751824 53246417 67108864 162779929 45675970560000 (@hp751825 53246417 67108864 2604478864 730815528960000 53246417 67108864 162779929 45675970560000 (hp751832 (hp751844 rfl rfl) rfl rfl) rfl)

noncomputable def hp751846 := @hp751823 53246417 67108864 162779929 45675970560000 42289976 42290356 33554432 hp751845 rfl rfl rfl

noncomputable def hp751847 := @Enclosure.Real.IsNear.recentre' hp751821 Bool.false 84580332 67108864 380 67108864 21145083 16777216 95 16777216 (hp751846 rfl rfl rfl)

noncomputable def hp751848 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751814 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp751849 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751814 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 63597255)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp751850 := nat_lit 1201318183993188057864770855845

noncomputable def hp751851 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751814 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp751850

noncomputable def hp751852 := nat_lit 24011474967920849039187243809529069

noncomputable def hp751853 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp751814 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp751854 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp751855 := @hp751854 (Enclosure.sfrac Bool.false 1 16) 1077052374054423 4503599627370496 4448863831 4503599627370496 1 16 0

noncomputable def hp751856 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)) 705716811139561

noncomputable def hp751857 := @hp751856 4503599627370496 1965835863 4503599627370496 26565331 67108864 37 67108864 72279761291295401705472 1077052374054423 4503599627370496 4448863831

noncomputable def hp751858 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)) 26565331 67108864 37

noncomputable def hp751859 := @hp751858 67108864 26565331 67108864 37 67108864 705716811139561 4503599627370496 1965835863 4503599627370496 (@hp751830 1 26565331 26565331 67108864 37 67108864 (hp751809 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751860 := hp751859 (@hp751830 1 26565331 26565331 67108864 37 67108864 (hp751809 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751861 := @hp751857 4503599627370496 (hp751860 rfl) (@hp751830 1 26565331 26565331 67108864 37 67108864 (hp751809 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp751862 := @hp751853 500000000000000 1358527350765079 4503599627370496 4448863831 4503599627370496 hp751850 hp627574 hp751852 hp742826 hd4948 (@hp751855 1 21736437612241264 1358527350765079 4503599627370496 4448863831 4503599627370496 (hp751861 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp751863 := @hp751849 63597255 33554432 417 67108864 Bool.true 10699902 33554432 1 10890000 (@hp751851 hp627574 hp751852 hp742826 63597255 33554432 417 67108864 (hp751862 rfl) rfl) (Enclosure.sfrac_true_div 63597255 33554432)

noncomputable def hp751864 := nat_lit 528695008082966806736085395613069224638505922415139683001020210183341519351512771912887237949390625

noncomputable def hp751865 := nat_lit 4377845706552279579349472755160597050279883401196826295498872064105267503828269494238525390625

noncomputable def hp751866 := nat_lit 3191094417307733419922879812126767404742249965561269039166655748741160269266976803564972054230990625

noncomputable def hp751867 := BSN.cos_dyadic_bound_t 63597255 33554432 4 3 33554432 10890000 hp751864 hp681868 hp751865 hp751866 hp681871

noncomputable def hp751868 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 63597255) (BSN.cosEvenQ 33554432) 0 3 hp751864 hp681868 hp751865 rfl rfl rfl

noncomputable def hp751869 := hp751867 hp751865 10699902 rfl rfl rfl rfl rfl rfl rfl rfl (hp751868 rfl)

noncomputable def hp751870 := @BSN.binarySplit_of_base3 (BSN.cosOddP 63597255) (BSN.cosOddQ 33554432) 0 3 hp751866 hp681871 hp751865 rfl rfl rfl

noncomputable def hp751871 := hp751863 (BSN.cos_neg_of_bound 63597255 33554432 Bool.true 10699902 33554432 1 10890000 (hp751869 (hp751870 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp751872 := hp751819 (hp751822 (@Enclosure.Real.IsNear.neg hp751821 Bool.false 21145083 16777216 95 16777216 (hp751847 rfl))) (@hp751848 10699902 33554432 4608238864 730815528960000 5349951 16777216 288014929 45675970560000 (hp751871 rfl) rfl)

noncomputable def hp751873 := @hp751794 67108864 113125157940933 281474976710656 3736912446062431 383157812047380480000 2248876667918884915485 18889465931478580854784 4652632155669856936411 hp751616 (hp751812 rfl) (@hp751815 Bool.false 113125157940933 281474976710656 3736912446062431 383157812047380480000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751620 (Enclosure.sfrac Bool.false 11 1)) (hp751816 rfl (hp751623 rfl rfl))) (hp751872 rfl))

noncomputable def hp751874 := @hp751617 1190095007903759139496411 hp751616 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 815969 1000))) (@hp751622 1190095007903759139496411 hp751616 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 815969 1000) 11 (hp751623 rfl rfl)) (@hp751626 1190095007903759139496411 hp751616 hp751793 (hp751873 rfl) rfl rfl))

theorem hd5017 : hp751615 hp751616 := hp751874

noncomputable def hp751875 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 817260 1000)) Bool.true 31922198073318024890163 9444732965739290427392 317819373059543018578751

noncomputable def hp751876 := nat_lit 428554758320420303142912000

noncomputable def hp751877 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 817260 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 817260 1000)) Bool.true 31922198073318024890163 9444732965739290427392

noncomputable def hp751878 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 817260 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751879 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp751878 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp751880 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 817260 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp751881 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp751879 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp751882 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 817260 1000)) hp751881 Bool.true 31922198073318024890163 9444732965739290427392

noncomputable def hp751883 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 817260 1000) 817260 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl

noncomputable def hp751884 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp751879 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp751885 := nat_lit 8569049796333445444410254819328

noncomputable def hp751886 := @hp751884 938973639 268435456 12395 16777216 1114999822862589409485 9444732965739290427392 1203301037724281938751 hp751876 hp751885 31922198073318024890163 9444732965739290427392

noncomputable def hp751887 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) 11)

noncomputable def hp751888 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) 11) hp751887

noncomputable def hp751889 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) 11)

noncomputable def hp751890 := @hp751889 938973639 536870912 198320 536870912 938973639 536870912 198320 536870912 1008215267827777536 938973639 268435456

noncomputable def hp751891 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp751892 := hp751891 BSN.quadSignNeg 9 10 11 817260 1000 191 241 536870912 268435456 9007199254740992

noncomputable def hp751893 := hp751892 Bool.false 848374660177 3725 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp751894 := hp751893 Bool.true 979859457 170252 Bool.true 841622925 Bool.true 494472795 28296951008113761 1 Bool.false 536868245

noncomputable def hp751895 := hp751894 Bool.false Bool.false 427469285 Bool.true Bool.true 938973639 198320 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536868245 536870912) BSN.abs_quadSignNeg

noncomputable def hp751896 := hp751891 BSN.quadSignNeg 7 8 9 817260 1000 75 137 536870912 268435456 9007199254740992

noncomputable def hp751897 := hp751896 Bool.false 848374660177 3725 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp751898 := hp751897 Bool.true 1117244619 139044 Bool.true 758986710 Bool.true 152306740 28296951008113761 1 Bool.false 530261662

noncomputable def hp751899 := hp751898 Bool.false Bool.false 150271954 Bool.true Bool.true 979859457 170252 BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 530261662 536870912) BSN.abs_quadSignNeg

noncomputable def hp751900 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp751901 := hp751900 BSN.quadSignNeg 5 6 7 817260 1000 73 6 536870912 268435456 9007199254740992

noncomputable def hp751902 := hp751901 Bool.false 848374660177 3725 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp751903 := hp751902 Bool.true 752250050 103326 Bool.false 654703870 Bool.true 359049341 28296951008113761 1 Bool.false 504079305

noncomputable def hp751904 := hp751903 Bool.true Bool.false 421216970 Bool.true Bool.true 1117244619 139044 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 504079305 536870912) BSN.abs_quadSignNeg

noncomputable def hp751905 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp751906 := hp751905 BSN.quadSignPos 3 4 5 817260 1000 284 168 536870912 268435456 9007199254740992

noncomputable def hp751907 := hp751906 Bool.false 848374660177 3725 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp751908 := hp751907 Bool.true 991578245 61071 Bool.false 618411066 Bool.false 535774851 28296951008113761 1 Bool.false 218383186

noncomputable def hp751909 := hp751908 Bool.false Bool.false 290994290 Bool.false Bool.true 752250050 103326 BSN.abs_quadSignPos (BSN.cos_quad_nat0 284 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 218383186 536870912) BSN.abs_quadSignPos

noncomputable def hp751910 := hp751900 BSN.quadSignNeg 1 2 3 817260 1000 645 434 536870912 268435456 9007199254740992

noncomputable def hp751911 := hp751910 Bool.false 848374660177 3725 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp751912 := hp751911 Bool.true 536870904 3778 Bool.false 309169324 Bool.false 345459676 28296951008113761 1 Bool.false 292362172

noncomputable def hp751913 := hp751912 Bool.true Bool.false 429507140 Bool.true Bool.true 991578245 61071 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 645 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 292362172 536870912) BSN.abs_quadSignNeg

noncomputable def hp751914 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) 1) Bool.true

noncomputable def hp751915 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)))

noncomputable def hp751916 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000))) Bool.true 67108863 67108864

noncomputable def hp751917 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 53023416261) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 53023416261 33554432

noncomputable def hp751918 := nat_lit 828322714298776776622451121266780113226967432209

noncomputable def hp751919 := nat_lit 524181581475604642006069460556019171695001600

noncomputable def hp751920 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) Bool.false hp751918 hp751919 6186747708731840249

noncomputable def hp751921 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 817260 4000) (Real.log (Enclosure.sfrac Bool.false 2671656630400 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1634520))))))

noncomputable def hp751922 := nat_lit 175001941063467706556418048000000000

noncomputable def hp751923 := nat_lit 858132668014230471827363570810880000000

noncomputable def hp751924 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp751921 (Enclosure.sfrac Bool.false 817260 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 817260 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp751922 hp751923)) Bool.false

noncomputable def hp751925 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 817260 1000) 817260 1000 2671656630400 16000000 1634520

noncomputable def hp751926 := hp751925 4000 2000 hp751922 hp751923 (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl rfl rfl rfl

noncomputable def hp751927 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp751921 (Enclosure.sfrac Bool.false 817260 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 817260 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp751922 hp751923) 1423336675960091573833 900719925474099200

noncomputable def hp751928 := nat_lit 1221411541596404283736401525375143283759957096838103040000000

noncomputable def hp751929 := @hp751927 6186747708731840249 892108800000000000000000 hp751922 hp751923 0 1 hp751928 hp751918 hp751919 6186747708731840249 892108800000000000000000

noncomputable def hp751930 := @Enclosure.Real.IsNear.subLit_ff_p (hp751921 (Enclosure.sfrac Bool.false 817260 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 817260 2000) (Real.log Real.pi)) 1844667310888339373641 900719925474099200 64473532065493 27225000000000000000

noncomputable def hp751931 := nat_lit 4775925370660892742795237785600

noncomputable def hp751932 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 817260 4000) (Real.log (Enclosure.sfrac Bool.false 2671656630400 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1634520))))))

noncomputable def hp751933 := @hp751932 (Enclosure.sfrac Bool.false 817260 2000) 2212728494034820529737 900719925474099200 64473532065493 27225000000000000000 817260 2000 0

noncomputable def hp751934 := nat_lit 3689334621776678747282000

noncomputable def hp751935 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 817260 4000) (Real.log (Enclosure.sfrac Bool.false 2671656630400 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1634520))))) 2213082068161345932537

noncomputable def hp751936 := nat_lit 4982621610603648259430710237542219776

noncomputable def hp751937 := @hp751935 900719925474099200 170262752165573 72600000000000000000 883935316313507 2251799813685248 200000001089 8712000000000000000 hp751936 2212728494034820529737 900719925474099200 64473532065493

noncomputable def hp751938 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 817260 4000) (Real.log (Enclosure.sfrac Bool.false 2671656630400 16000000)) 817260 4000 0 1 54158580333341799 4503599627370496

noncomputable def hp751939 := nat_lit 116304665664745902547402752

noncomputable def hp751940 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2671656630400) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp751939 hp617687

noncomputable def hp751941 := BSN.log_rat_reduce_isNear 2671656630400 16000000 17 5343313260800 4194304000000 64993191 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp751942 := nat_lit 252761524932839373549630279613393410243809265235525530290653432517311015598618045526835200000000000000000

noncomputable def hp751943 := nat_lit 1233564205665090927477537632876142432456246938084372839515083663076353807431965175971840000000000000000

noncomputable def hp751944 := nat_lit 1246056015202831827538166668339273233041506676012746765778365426806737425190092800000000000000000

noncomputable def hp751945 := BSN.log_dyadic_bound 574504630400 4768808630400 5 4 hp751942 268435456 87120000 hp751943 hp751944 64993191 5343313260800

noncomputable def hp751946 := hp751945 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp751947 := @BSN.binarySplit_of_base4 (BSN.artanhP 574504630400) (BSN.artanhQ 4768808630400) 0 4 hp751943 hp751942 hp751944 rfl rfl rfl

noncomputable def hp751948 := hp751941 rfl rfl rfl rfl (hp751946 (hp751947 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp751949 := @hp751938 12500018513 1089000000000000000 2213082068161345932537 900719925474099200 170262752165573 72600000000000000000 (Enclosure.Real.IsNear.const Bool.false 817260 4000) (BSN.isNear_log_sfrac 2671656630400 16000000 54158580333341799 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp751940 1000001481040000 87120000000000000000000 54158580333341799 4503599627370496 12500018513 1089000000000000000 (hp751948 rfl rfl rfl) rfl)) rfl

noncomputable def hp751950 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1634520)))) 1 4

noncomputable def hp751951 := @hp751950 0 1 883935316313507 562949953421312 200000001089 2178000000000000000 883935316313507 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp751952 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1634520))) 884279719003555 562949953421312 1

noncomputable def hp751953 := @hp751952 2000000000000000 20528 33554432 1 10890000 29659947463640061313024 883935316313507 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp751954 := BSN.arctan_dyadic_bound_f 1000 1634520 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp751955 := hp751954 1 20528 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1634520) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1634520) 0 0 rfl)

noncomputable def hp751956 := hp751951 (hp751953 (hp751955 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp751957 := @hp751930 1569578926743 3355443200 122589 26843545600 hp751931 1423336675960091573833 900719925474099200 6186747708731840249 892108800000000000000000 (@hp751933 1 hp751934 1844667310888339373641 900719925474099200 64473532065493 27225000000000000000 (@hp751937 27225000000000000000 hp751949 hp751956 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 817260 2000) rfl rfl)

noncomputable def hp751958 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 817260 2000) (Real.log Real.pi) 817260 2000 0 1 38410761 33554432

noncomputable def hp751959 := hp751957 (@hp751958 3 268435456 1569578926743 3355443200 122589 26843545600 (Enclosure.Real.IsNear.const Bool.false 817260 2000) hd4909 rfl) rfl

noncomputable def hp751960 := @hp751920 892108800000000000000000 53023416261 33554432 233 33554432 (@hp751924 hp751918 hp751919 6186747708731840249 892108800000000000000000 (hp751926 rfl rfl rfl rfl rfl) (hp751929 (hp751959 rfl) (Enclosure.Real.IsNear.const Bool.true hp751922 hp751923) rfl rfl)) rfl

noncomputable def hp751961 := nat_lit 7595134869369295095201792

noncomputable def hp751962 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 53023416261) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp751961) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp751963 := BSN.sin_reduce_arg_pos_rat_q1 53023416261 33554432 226375608064910080 72057594037927936 251 hp751961 hp619237 rfl rfl rfl rfl

noncomputable def hp751964 := nat_lit 14374539746043803213793086320195030498415320119723156115689563449079872258764825624190205410140657721539574197791481354738633654384715780590481

noncomputable def hp751965 := nat_lit 10238308784162089865571291237288340032255922842225785905155950911724907170184475542939646775551850715939298829273825721928801058129185681

noncomputable def hp751966 := nat_lit 71783424188953648827794283444113156899244176371101345705681570894960671530414465572267127395548434336001607860446470438255609659354002022730641

noncomputable def hp751967 := BSN.sin_dyadic_bound_f 215866716341 137438953472 4 3 67108864 21801270 hp751964 hp737934 hp751965 hp751966 hp737937

noncomputable def hp751968 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215866716341) (BSN.sinEvenQ 137438953472) 0 3 hp751964 hp737934 hp751965 rfl rfl rfl

noncomputable def hp751969 := hp751967 hp751965 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (hp751968 rfl)

noncomputable def hp751970 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215866716341) (BSN.sinOddQ 137438953472) 0 3 hp751966 hp737937 hp751965 rfl rfl rfl

noncomputable def hp751971 := @BSN.sin_arg_round Bool.false 67108863 67108864 hp751961 hp619237 215866716341 137438953472 21801270 21780000 (hp751969 (hp751970 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751972 := hp751962 67108863 67108864 251 1000000000000000 21780000 10890000 hp751963 BSN.pi_near_15 hp751971 rfl rfl

noncomputable def hp751973 := @hp751917 233 33554432 Bool.true 67108863 67108864 1 10890000 hp751960 (Enclosure.sfrac_false_div 53023416261 33554432) (hp751972 rfl rfl) rfl

noncomputable def hp751974 := @hp751914 67108863 67108864 160682777 22837985280000 536870904 536870912 3778 536870912 (@hp751915 Bool.true 67108863 67108864 160682777 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000)) (@hp751916 2570924432 365407764480000 67108863 67108864 160682777 22837985280000 (hp751973 rfl) rfl))

noncomputable def hp751975 := @hp751920 892108800000000000000000 848374660177 536870912 3725 536870912 (@hp751924 hp751918 hp751919 6186747708731840249 892108800000000000000000 (hp751926 rfl rfl rfl rfl rfl) (hp751929 (hp751959 rfl) (Enclosure.Real.IsNear.const Bool.true hp751922 hp751923) rfl rfl)) rfl

noncomputable def hp751976 := hp751913 (BSN.cos_quad_nat2 434 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 429507140 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl rfl (hp751974 rfl) hp751975

noncomputable def hp751977 := nat_lit 2295422655069916906263441359846427356931779513893043373622559243086397440

noncomputable def hp751978 := nat_lit 83477833830336673818432841946557718742457320376535010010590074699776

noncomputable def hp751979 := nat_lit 6011686084880723733218068955948920079467172843582123017090495157486288896

noncomputable def hp751980 := BSN.sin_dyadic_bound_f 309169324 536870912 3 2 536870912 268435456 hp751977 hp708845 hp751978 hp751979 hp708848

noncomputable def hp751981 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 309169324) (BSN.sinEvenQ 536870912) 0 2 hp751977 hp708845 hp751978 rfl rfl rfl

noncomputable def hp751982 := hp751980 hp751978 292362172 rfl rfl rfl rfl rfl rfl rfl rfl (hp751981 rfl)

noncomputable def hp751983 := @BSN.binarySplit_of_base2 (BSN.sinOddP 309169324) (BSN.sinOddQ 536870912) 0 2 hp751979 hp708848 hp751978 rfl rfl rfl

noncomputable def hp751984 := nat_lit 1988028199651730392928462546611682340261743507560342629231998859969888256

noncomputable def hp751985 := nat_lit 202851811769536505468521870054612457923400268523481671456176985931776

noncomputable def hp751986 := nat_lit 5963678895331652105774450596094937795869383722143980924353084225937801216

noncomputable def hp751987 := BSN.cos_dyadic_bound_f 345459676 536870912 3 2 536870912 268435456 hp751984 hp708868 hp751985 hp751986 hp708870

noncomputable def hp751988 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 345459676) (BSN.cosEvenQ 536870912) 0 2 hp751984 hp708868 hp751985 rfl rfl rfl

noncomputable def hp751989 := hp751987 hp751985 429507140 rfl rfl rfl rfl rfl rfl rfl rfl (hp751988 rfl)

noncomputable def hp751990 := @BSN.binarySplit_of_base2 (BSN.cosOddP 345459676) (BSN.cosOddQ 536870912) 0 2 hp751986 hp708870 hp751985 rfl rfl rfl

noncomputable def hp751991 := hp751976 hd4911 hd4913 hd4915 hd4917 hd4918 (hp751982 (hp751983 rfl) rfl rfl rfl rfl) (hp751989 (hp751990 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp751992 := hp751909 (BSN.cos_quad_nat0 168 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 290994290 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl rfl (hp751991 rfl rfl rfl rfl rfl) hp751975

noncomputable def hp751993 := nat_lit 20167341504841806152966827281888483499362631183638937169848147342894868884825631574689950077760419614191636647936

noncomputable def hp751994 := nat_lit 3128434223656650700517527655688830123882224303374913311296210712419215571424412866090448151412523855712256

noncomputable def hp751995 := nat_lit 122263139332666104443429440399894882027592860359095854265615776814222388172843027524309702158438999130701286543360

noncomputable def hp751996 := BSN.cos_dyadic_bound_f 618411066 536870912 4 3 536870912 268435456 hp751993 hp716712 hp751994 hp751995 hp716714

noncomputable def hp751997 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 618411066) (BSN.cosEvenQ 536870912) 0 3 hp751993 hp716712 hp751994 rfl rfl rfl

noncomputable def hp751998 := hp751996 hp751994 218383186 rfl rfl rfl rfl rfl rfl rfl rfl (hp751997 rfl)

noncomputable def hp751999 := @BSN.binarySplit_of_base3 (BSN.cosOddP 618411066) (BSN.cosOddQ 536870912) 0 3 hp751995 hp716714 hp751994 rfl rfl rfl

noncomputable def hp752000 := nat_lit 11357176180559559492612045308003971964705704733110970711698606371349445277441673912225409374657019534603211511281

noncomputable def hp752001 := nat_lit 559484282217089473244985434692640944627036638401038469606171128474556125161240112746913831704092937033201

noncomputable def hp752002 := nat_lit 68873096574453625875811778058046741371945612185767954961145954681602029563377354048420558803108094282747204605425

noncomputable def hp752003 := BSN.cos_dyadic_bound_f 535774851 536870912 4 3 536870912 268435456 hp752000 hp716712 hp752001 hp752002 hp716714

noncomputable def hp752004 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 535774851) (BSN.cosEvenQ 536870912) 0 3 hp752000 hp716712 hp752001 rfl rfl rfl

noncomputable def hp752005 := hp752003 hp752001 290994290 rfl rfl rfl rfl rfl rfl rfl rfl (hp752004 rfl)

noncomputable def hp752006 := @BSN.binarySplit_of_base3 (BSN.cosOddP 535774851) (BSN.cosOddQ 536870912) 0 3 hp752002 hp716714 hp752001 rfl rfl rfl

noncomputable def hp752007 := hp751992 hd4920 hd4922 hd4924 hd4926 hd4918 (hp751998 (hp751999 rfl) rfl rfl rfl rfl) (hp752005 (hp752006 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752008 := hp751904 (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 421216970 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl rfl (hp752007 rfl rfl rfl rfl rfl) hp751975

noncomputable def hp752009 := nat_lit 65849917881958824602407551230391846673259122820234599337293977266940667584568630583910197096417736060253350400000

noncomputable def hp752010 := nat_lit 6202101893029896429258295622449163137831377713747662457048357832229094789655185043678434504881000000000000

noncomputable def hp752011 := nat_lit 329100819635296476495874184389651298144324230606227658236614890632600452883833335852656939824360370984242752000000

noncomputable def hp752012 := BSN.sin_dyadic_bound_f 654703870 536870912 4 3 536870912 268435456 hp752009 hp642702 hp752010 hp752011 hp642705

noncomputable def hp752013 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 654703870) (BSN.sinEvenQ 536870912) 0 3 hp752009 hp642702 hp752010 rfl rfl rfl

noncomputable def hp752014 := hp752012 hp752010 504079305 rfl rfl rfl rfl rfl rfl rfl rfl (hp752013 rfl)

noncomputable def hp752015 := @BSN.binarySplit_of_base3 (BSN.sinOddP 654703870) (BSN.sinOddQ 536870912) 0 3 hp752011 hp642705 hp752010 rfl rfl rfl

noncomputable def hp752016 := nat_lit 2319834623435209092397559031341660266412019526567670832717491025333136801

noncomputable def hp752017 := nat_lit 276205976584490450527883354261152216923756180226377611045193994415521

noncomputable def hp752018 := nat_lit 6958951458352458296291621327316458494802211067342559742930382688010579361

noncomputable def hp752019 := BSN.cos_dyadic_bound_f 359049341 536870912 3 2 536870912 268435456 hp752016 hp708868 hp752017 hp752018 hp708870

noncomputable def hp752020 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 359049341) (BSN.cosEvenQ 536870912) 0 2 hp752016 hp708868 hp752017 rfl rfl rfl

noncomputable def hp752021 := hp752019 hp752017 421216970 rfl rfl rfl rfl rfl rfl rfl rfl (hp752020 rfl)

noncomputable def hp752022 := @BSN.binarySplit_of_base2 (BSN.cosOddP 359049341) (BSN.cosOddQ 536870912) 0 2 hp752018 hp708870 hp752017 rfl rfl rfl

noncomputable def hp752023 := hp752008 hd4928 hd4930 hd4932 hd4934 hd4918 (hp752014 (hp752015 rfl) rfl rfl rfl rfl) (hp752021 (hp752022 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752024 := hp751899 (BSN.cos_quad_nat1 137 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 150271954 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl rfl (hp752023 rfl rfl rfl rfl rfl) hp751975

noncomputable def hp752025 := nat_lit 119005811880624521806655687498449601998300637468167104617502147176288355330925055024460821144336695588821158400000

noncomputable def hp752026 := nat_lit 36543492973564058175546833305166911327896746091750523418123314535619383566125242348823102741441000000000000

noncomputable def hp752027 := nat_lit 594543673464416749349067361213868829184796788252476137797926580608501076159551770484052050120073513840521792000000

noncomputable def hp752028 := BSN.sin_dyadic_bound_f 758986710 536870912 4 3 536870912 268435456 hp752025 hp642702 hp752026 hp752027 hp642705

noncomputable def hp752029 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 758986710) (BSN.sinEvenQ 536870912) 0 3 hp752025 hp642702 hp752026 rfl rfl rfl

noncomputable def hp752030 := hp752028 hp752026 530261662 rfl rfl rfl rfl rfl rfl rfl rfl (hp752029 rfl)

noncomputable def hp752031 := @BSN.binarySplit_of_base3 (BSN.sinOddP 758986710) (BSN.sinOddQ 536870912) 0 3 hp752027 hp642705 hp752026 rfl rfl rfl

noncomputable def hp752032 := nat_lit 538116724552826984176687641760000

noncomputable def hp752033 := BSN.sin_dyadic_bound_f 152306740 536870912 2 1 536870912 268435456 hp752032 hp708890 hp752032 hp752032 hp708891

noncomputable def hp752034 := @BSN.binarySplit_of_base (BSN.sinEvenP 152306740) (BSN.sinEvenQ 536870912) 0 1 hp752032 hp708890 hp752032 rfl rfl rfl

noncomputable def hp752035 := hp752033 hp752032 150271954 rfl rfl rfl rfl rfl rfl rfl rfl (hp752034 rfl)

noncomputable def hp752036 := @BSN.binarySplit_of_base (BSN.sinOddP 152306740) (BSN.sinOddQ 536870912) 0 1 hp752032 hp708891 hp752032 rfl rfl rfl

noncomputable def hp752037 := hp752024 hd4936 hd4938 hd4940 hd4942 hd4918 (hp752030 (hp752031 rfl) rfl rfl rfl rfl) (hp752035 (hp752036 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752038 := hp751895 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 427469285 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl rfl (hp752037 rfl rfl rfl rfl rfl) hp751975

noncomputable def hp752039 := nat_lit 180050809701482423031157395568445924577165988345936001094060037171021583978154977363177615160223522030035181640625

noncomputable def hp752040 := nat_lit 126302131780859342653828585955848175088410347885769291827393498131554549985955073334679017126560211181640625

noncomputable def hp752041 := nat_lit 899144308549789420759793785631913929722235640529559141254176847843022033064526400732015892726802703909331181640625

noncomputable def hp752042 := BSN.sin_dyadic_bound_f 841622925 536870912 4 3 536870912 268435456 hp752039 hp642702 hp752040 hp752041 hp642705

noncomputable def hp752043 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 841622925) (BSN.sinEvenQ 536870912) 0 3 hp752039 hp642702 hp752040 rfl rfl rfl

noncomputable def hp752044 := hp752042 hp752040 536868245 rfl rfl rfl rfl rfl rfl rfl rfl (hp752043 rfl)

noncomputable def hp752045 := @BSN.binarySplit_of_base3 (BSN.sinOddP 841622925) (BSN.sinOddQ 536870912) 0 3 hp752041 hp642705 hp752040 rfl rfl rfl

noncomputable def hp752046 := nat_lit 15022223782731073137087574654308131049939096237564784428747101747457830625

noncomputable def hp752047 := nat_lit 3573873859497697773906874686988419140210593535912927965088034500390625

noncomputable def hp752048 := nat_lit 39338133158999338134071608202266171499803958708849624001441790616055590625

noncomputable def hp752049 := BSN.sin_dyadic_bound_f 494472795 536870912 3 2 536870912 268435456 hp752046 hp708845 hp752047 hp752048 hp708848

noncomputable def hp752050 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 494472795) (BSN.sinEvenQ 536870912) 0 2 hp752046 hp708845 hp752047 rfl rfl rfl

noncomputable def hp752051 := hp752049 hp752047 427469285 rfl rfl rfl rfl rfl rfl rfl rfl (hp752050 rfl)

noncomputable def hp752052 := @BSN.binarySplit_of_base2 (BSN.sinOddP 494472795) (BSN.sinOddQ 536870912) 0 2 hp752048 hp708848 hp752047 rfl rfl rfl

noncomputable def hp752053 := hp752038 hd4944 hd4946 hd4961 hd4963 hd4918 (hp752044 (hp752045 rfl) rfl rfl rfl rfl) (hp752051 (hp752052 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752054 := @hp751890 12395 16777216 (hp752053 rfl rfl rfl rfl rfl) (hp752053 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp752055 := @hp751888 Bool.true 938973639 268435456 12395 16777216 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 817260 1000)) (Enclosure.sfrac Bool.false 817260 1000) 11) hp752054

noncomputable def hp752056 := @Enclosure.Real.IsNear.mulLit_tf hp751879 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1))) 9935845 33554432 1

noncomputable def hp752057 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp751878 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752058 := @hp752057 1 1 0 1 9935845 33554432 1 33554432 9935845 33554432 1

noncomputable def hp752059 := @Enclosure.Real.IsNear.of_eq (hp751878 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752060 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 817260 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752061 := @hp752059 (@Inv.inv Real Real.instInv (Real.sqrt hp751880)) Bool.false 9935845 33554432 1 33554432 (hp752060 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 817260 1000) 817260 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000))))

noncomputable def hp752062 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp751880)) Bool.false 19871690 67108864 2 67108864 9935845 33554432

noncomputable def hp752063 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp751880) Bool.false 226633954 67108864 6 67108864 113316977 33554432 3 33554432

noncomputable def hp752064 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 817260 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752065 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 817260 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752066 := @hp752065 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 817260 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 436445730141

noncomputable def hp752067 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 817260 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 817260 1000 0

noncomputable def hp752068 := @hp752067 1 10680707 67108864 1 67108864 436445730141 3355443200 40863 3355443200 (Enclosure.Real.IsNear.const Bool.false 817260 1000) hd4949

noncomputable def hp752069 := @hp752066 3355443200 40863 3355443200 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 817260 1000) 817260 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000))) (hp752068 rfl)

noncomputable def hp752070 := @hp752064 436445730141 3355443200 40863 3355443200 382683775 382683812 33554432 hp752069 rfl rfl rfl

noncomputable def hp752071 := @Enclosure.Real.IsNear.recentre' hp751880 Bool.false 765367587 67108864 37 67108864 765367587 67108864 37 67108864 (hp752070 rfl rfl rfl)

noncomputable def hp752072 := @Enclosure.Real.IsNear.sqrt_image hp751880 765367587 67108864 37 67108864 113316974 113316980 33554432 (hp752071 rfl) rfl rfl

noncomputable def hp752073 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp751880) 113316977 33554432 3 33554432 9935844 9935846 33554432 (hp752063 (hp752072 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp752074 := @hp752058 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp752061 (@hp752062 1 33554432 (hp752073 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp752075 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752076 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp752077 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1))) (hp752075 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752076 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp752078 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 817260 1000) 817260 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl

noncomputable def hp752079 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752080 := @hp752079 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752076 (Enclosure.sfrac Bool.false 1 16)))) 81186009

noncomputable def hp752081 := @hp752080 67108864 351 67108864 1382257 4194304 145709027 22837985280000 112219929242313 281474976710656 30148642059139 3192981767061504000

noncomputable def hp752082 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752083 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752084 := @hp752082 (@Neg.neg Real Real.instNeg hp752083) Bool.true 81186009 67108864 351 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752085 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752086 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp752087 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp752088 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 85357333) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp752089 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1))) Bool.false 24025953360543266645065

noncomputable def hp752090 := nat_lit 199696958073603783534092583

noncomputable def hp752091 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp752092 := @Enclosure.Real.IsNear.subLit_ff_p hp751880 (Enclosure.sfrac Bool.false 11 1) 765367587 67108864 37 67108864 11 1 0

noncomputable def hp752093 := @hp752091 500000000000000 27170083 67108864 37 67108864 24025953360543266645065 9444732965739290427392 hp752090 hp645312 hd4948 (@hp752092 1 27170083 27170083 67108864 37 67108864 (hp752071 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752094 := @hp752088 85357333 33554432 233 67108864 Bool.true 55472608 67108864 1 10890000 (@hp752089 9444732965739290427392 hp752090 hp645312 85357333 33554432 233 67108864 (hp752093 rfl) rfl) (Enclosure.sfrac_false_div 85357333 33554432)

noncomputable def hp752095 := nat_lit 4705383151675782060834816

noncomputable def hp752096 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 85357333) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp752095) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp752097 := BSN.sin_reduce_arg_pos_rat_q1 85357333 33554432 226375608064910080 72057594037927936 0 hp752095 hp619237 rfl rfl rfl rfl

noncomputable def hp752098 := nat_lit 345247567913997361704681294214066571259664274880811278190610574337398928407554523182727330625

noncomputable def hp752099 := nat_lit 102320229530623621124337588653366042160182481602927638264832175705565272329423268937890625

noncomputable def hp752100 := nat_lit 904054159403133985268535414464735570183242329241434321942027490218235802055061827805053090625

noncomputable def hp752101 := BSN.sin_dyadic_bound_f 133735032695 137438953472 3 2 67108864 21801270 hp752098 hp738039 hp752099 hp752100 hp738042

noncomputable def hp752102 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 133735032695) (BSN.sinEvenQ 137438953472) 0 2 hp752098 hp738039 hp752099 rfl rfl rfl

noncomputable def hp752103 := hp752101 hp752099 55472608 rfl rfl rfl rfl rfl rfl rfl rfl (hp752102 rfl)

noncomputable def hp752104 := @BSN.binarySplit_of_base2 (BSN.sinOddP 133735032695) (BSN.sinOddQ 137438953472) 0 2 hp752100 hp738042 hp752099 rfl rfl rfl

noncomputable def hp752105 := @BSN.sin_arg_round Bool.false 55472608 67108864 hp752095 hp619237 133735032695 137438953472 21801270 21780000 (hp752103 (hp752104 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752106 := hp752096 55472608 67108864 0 1000000000000000 21780000 10890000 hp752097 BSN.pi_near_15 hp752105 rfl rfl

noncomputable def hp752107 := @hp752086 1733519 2097152 162779929 45675970560000 (@hp752087 55472608 67108864 2604478864 730815528960000 1733519 2097152 162779929 45675970560000 (hp752094 (hp752106 rfl rfl) rfl rfl) rfl)

noncomputable def hp752108 := @hp752085 1733519 2097152 162779929 45675970560000 40592829 40593180 33554432 hp752107 rfl rfl rfl

noncomputable def hp752109 := @Enclosure.Real.IsNear.recentre' hp752083 Bool.false 81186009 67108864 351 67108864 81186009 67108864 351 67108864 (hp752108 rfl rfl rfl)

noncomputable def hp752110 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752076 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp752111 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752076 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 127951727)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp752112 := nat_lit 1208469902895182643089726147845

noncomputable def hp752113 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752076 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp752112

noncomputable def hp752114 := nat_lit 121265046187280712466896345984517761

noncomputable def hp752115 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752076 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp752116 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp752117 := @hp752116 (Enclosure.sfrac Bool.false 1 16) 1085139994688823 4503599627370496 4493615479 4503599627370496 1 16 0

noncomputable def hp752118 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)) 738213410226889

noncomputable def hp752119 := @hp752118 4503599627370496 2010587511 4503599627370496 27170083 67108864 37 67108864 72822512324532945027072 1085139994688823 4503599627370496 4493615479

noncomputable def hp752120 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)) 27170083 67108864 37

noncomputable def hp752121 := @hp752120 67108864 27170083 67108864 37 67108864 738213410226889 4503599627370496 2010587511 4503599627370496 (@hp752092 1 27170083 27170083 67108864 37 67108864 (hp752071 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752122 := hp752121 (@hp752092 1 27170083 27170083 67108864 37 67108864 (hp752071 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752123 := @hp752119 4503599627370496 (hp752122 rfl) (@hp752092 1 27170083 27170083 67108864 37 67108864 (hp752071 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752124 := @hp752115 500000000000000 1366614971399479 4503599627370496 4493615479 4503599627370496 hp752112 hp627574 hp752114 hp738055 hd4948 (@hp752117 1 21865839542391664 1366614971399479 4503599627370496 4493615479 4503599627370496 (hp752123 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp752125 := @hp752111 127951727 67108864 211 33554432 Bool.true 11058056 33554432 1 10890000 (@hp752113 hp627574 hp752114 hp738055 127951727 67108864 211 33554432 (hp752124 rfl) rfl) (Enclosure.sfrac_true_div 127951727 67108864)

noncomputable def hp752126 := nat_lit 2217971738653690211211068445680039386442028703826295956103416507948548034808473437613375275795444267201

noncomputable def hp752127 := nat_lit 19255456745028460931129907280431138967422793173741830283625994721996641928760887619790184734128321

noncomputable def hp752128 := nat_lit 13385587008263228332609836537769645905692014051686511149414265036091366820025760175438992048109491976385

noncomputable def hp752129 := BSN.cos_dyadic_bound_t 127951727 67108864 4 3 33554432 10890000 hp752126 hp745658 hp752127 hp752128 hp745661

noncomputable def hp752130 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 127951727) (BSN.cosEvenQ 67108864) 0 3 hp752126 hp745658 hp752127 rfl rfl rfl

noncomputable def hp752131 := hp752129 hp752127 11058056 rfl rfl rfl rfl rfl rfl rfl rfl (hp752130 rfl)

noncomputable def hp752132 := @BSN.binarySplit_of_base3 (BSN.cosOddP 127951727) (BSN.cosOddQ 67108864) 0 3 hp752128 hp745661 hp752127 rfl rfl rfl

noncomputable def hp752133 := hp752125 (BSN.cos_neg_of_bound 127951727 67108864 Bool.true 11058056 33554432 1 10890000 (hp752131 (hp752132 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp752134 := hp752081 (hp752084 (@Enclosure.Real.IsNear.neg hp752083 Bool.false 81186009 67108864 351 67108864 (hp752109 rfl))) (@hp752110 11058056 33554432 2331344432 365407764480000 1382257 4194304 145709027 22837985280000 (hp752133 rfl) rfl)

noncomputable def hp752135 := @hp752056 33554432 112219929242313 281474976710656 30148642059139 3192981767061504000 1114999822862589409485 9444732965739290427392 1203301037724281938751 hp751876 (hp752074 rfl) (@hp752077 Bool.false 112219929242313 281474976710656 30148642059139 3192981767061504000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp751880 (Enclosure.sfrac Bool.false 11 1)) (hp752078 rfl (hp751883 rfl rfl))) (hp752134 rfl))

noncomputable def hp752136 := @hp751877 317819373059543018578751 hp751876 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 817260 1000))) (@hp751882 317819373059543018578751 hp751876 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 817260 1000) 11 (hp751883 rfl rfl)) (@hp751886 317819373059543018578751 hp751876 hp752055 (hp752135 rfl) rfl rfl))

theorem hd5018 : hp751875 hp751876 := hp752136

noncomputable def hp752137 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 818551 1000)) Bool.false 10339502890598671513357 18889465931478580854784 636496280585817785703743

noncomputable def hp752138 := nat_lit 857109516640840606285824000

noncomputable def hp752139 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 818551 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 818551 1000)) Bool.false 10339502890598671513357 18889465931478580854784

noncomputable def hp752140 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 818551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752141 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp752140 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752142 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 818551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752143 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp752141 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp752144 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 818551 1000)) hp752143 Bool.false 10339502890598671513357 18889465931478580854784

noncomputable def hp752145 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 818551 1000) 818551 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl

noncomputable def hp752146 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp752141 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp752147 := nat_lit 693872293312793125170549096448

noncomputable def hp752148 := @hp752146 28871697 67108864 198631 268435456 2212842649926554810125 18889465931478580854784 2271119212624184679743 hp752138 hp752147 10339502890598671513357 18889465931478580854784

noncomputable def hp752149 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) 11)

noncomputable def hp752150 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) 11) hp752149

noncomputable def hp752151 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) 11)

noncomputable def hp752152 := @hp752151 115486788 536870912 198631 536870912 115486788 536870912 198631 536870912 124002994395021312 28871697 67108864

noncomputable def hp752153 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp752154 := hp752153 BSN.quadSignNeg 9 10 11 818551 1000 191 241 536870912 268435456 9007199254740992

noncomputable def hp752155 := hp752154 Bool.false 850061967900 3730 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp752156 := hp752155 Bool.false 72383736 170519 Bool.true 750237727 Bool.true 469147116 28296951008113761 1 Bool.false 528822725

noncomputable def hp752157 := hp752156 Bool.false Bool.false 411677340 Bool.true Bool.false 115486788 198631 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 528822725 536870912) BSN.abs_quadSignNeg

noncomputable def hp752158 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp752159 := hp752158 BSN.quadSignPos 7 8 9 818551 1000 75 136 536870912 268435456 9007199254740992

noncomputable def hp752160 := hp752159 Bool.false 850061967900 3730 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp752161 := hp752160 Bool.true 86643866 139263 Bool.true 512940641 Bool.true 831210972 28296951008113761 1 Bool.false 438387288

noncomputable def hp752162 := hp752161 Bool.false Bool.false 12102859 Bool.false Bool.false 72383736 170519 BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 438387288 536870912) BSN.abs_quadSignPos

noncomputable def hp752163 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp752164 := hp752163 BSN.quadSignNeg 5 6 7 818551 1000 74 6 536870912 268435456 9007199254740992

noncomputable def hp752165 := hp752164 Bool.false 850061967900 3730 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp752166 := hp752165 Bool.false 310699433 103489 Bool.false 256827635 Bool.true 20452598 28296951008113761 1 Bool.false 476603080

noncomputable def hp752167 := hp752166 Bool.true Bool.false 536481378 Bool.true Bool.true 86643866 139263 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 476603080 536870912) BSN.abs_quadSignNeg

noncomputable def hp752168 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp752169 := hp752168 BSN.quadSignNeg 3 4 5 818551 1000 285 169 536870912 268435456 9007199254740992

noncomputable def hp752170 := hp752169 Bool.false 850061967900 3730 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp752171 := hp752170 Bool.false 640028340 61168 Bool.false 501562847 Bool.false 264265762 28296951008113761 1 Bool.false 431721384

noncomputable def hp752172 := hp752171 Bool.true Bool.false 253722649 Bool.true Bool.false 310699433 103489 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 285 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 431721384 536870912) BSN.abs_quadSignNeg

noncomputable def hp752173 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp752174 := hp752173 BSN.quadSignPos 1 2 3 818551 1000 646 435 536870912 268435456 9007199254740992

noncomputable def hp752175 := hp752174 Bool.false 850061967900 3730 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp752176 := hp752175 Bool.false 536870584 3786 Bool.false 672741658 Bool.false 428003990 28296951008113761 1 Bool.false 167717915

noncomputable def hp752177 := hp752176 Bool.true Bool.false 384086129 Bool.false Bool.false 640028340 61168 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 646 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 167717915 536870912) BSN.abs_quadSignPos

noncomputable def hp752178 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) 1) Bool.false

noncomputable def hp752179 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)))

noncomputable def hp752180 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000))) Bool.false 67108823 67108864

noncomputable def hp752181 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 106257745987) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 106257745987 67108864

noncomputable def hp752182 := nat_lit 15443578123426282283613957359302799812717792832579418498293

noncomputable def hp752183 := nat_lit 9753651127508335371536882749634165660294543668622131200

noncomputable def hp752184 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) Bool.false hp752182 hp752183 113801439274781857

noncomputable def hp752185 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 818551 4000) (Real.log (Enclosure.sfrac Bool.false 2680103958404 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1637102))))))

noncomputable def hp752186 := nat_lit 176388539755259884204667160520480000

noncomputable def hp752187 := nat_lit 866298244473669798141280540238732546880

noncomputable def hp752188 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp752185 (Enclosure.sfrac Bool.false 818551 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 818551 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp752186 hp752187)) Bool.false

noncomputable def hp752189 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 818551 1000) 818551 1000 2680103958404 16000000 1637102

noncomputable def hp752190 := hp752189 4000 2000 hp752186 hp752187 (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl rfl rfl rfl

noncomputable def hp752191 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp752185 (Enclosure.sfrac Bool.false 818551 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 818551 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp752186 hp752187) 5704670033131187968877 3602879701896396800

noncomputable def hp752192 := nat_lit 4941944999496410330756466354976895940069693706425413919453760

noncomputable def hp752193 := @hp752191 113801439274781857 16384000000000000000000 hp752186 hp752187 0 1 hp752192 hp752182 hp752183 113801439274781857 16384000000000000000000

noncomputable def hp752194 := @Enclosure.Real.IsNear.subLit_ff_p (hp752185 (Enclosure.sfrac Bool.false 818551 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 818551 2000) (Real.log Real.pi)) 36963274120117241383201 18014398509481984000 9487513915867 4000000000000000000

noncomputable def hp752195 := nat_lit 1914169627091381937809014128640000

noncomputable def hp752196 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 818551 4000) (Real.log (Enclosure.sfrac Bool.false 2680103958404 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1637102))))))

noncomputable def hp752197 := @hp752196 (Enclosure.sfrac Bool.false 818551 2000) 44336126077284735125793 18014398509481984000 9487513915867 4000000000000000000 818551 2000 0

noncomputable def hp752198 := nat_lit 73926548240234482766402000

noncomputable def hp752199 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 818551 4000) (Real.log (Enclosure.sfrac Bool.false 2680103958404 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1637102))))) 44343197564110210477793

noncomputable def hp752200 := nat_lit 99836080440355431826222419052188401664

noncomputable def hp752201 := @hp752199 18014398509481984000 10231902653834663 4356000000000000000000 883935853184419 2251799813685248 200000001089 8712000000000000000 hp752200 44336126077284735125793 18014398509481984000 9487513915867

noncomputable def hp752202 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 818551 4000) (Real.log (Enclosure.sfrac Bool.false 2680103958404 16000000)) 818551 4000 0 1 54172797497175143 4503599627370496

noncomputable def hp752203 := nat_lit 116335196791598945784561664

noncomputable def hp752204 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2680103958404) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp752203 hp617687

noncomputable def hp752205 := BSN.log_rat_reduce_isNear 2680103958404 16000000 17 5360207916808 4194304000000 65840600 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp752206 := nat_lit 256365685606590063135652686867164926900258139097791343462651616822386486605208711451087703952259609067520

noncomputable def hp752207 := nat_lit 1283959736289047167226280348548431111511083061880152179075670358920866618756537417852703868401742249984

noncomputable def hp752208 := nat_lit 1400397813927640821903411041589520590854126648195499872685379095589649184045113181574375938785280

noncomputable def hp752209 := BSN.log_dyadic_bound 582951958404 4777255958404 5 4 hp752206 268435456 87120000 hp752207 hp752208 65840600 5360207916808

noncomputable def hp752210 := hp752209 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp752211 := @BSN.binarySplit_of_base4 (BSN.artanhP 582951958404) (BSN.artanhQ 4777255958404) 0 4 hp752207 hp752206 hp752208 rfl rfl rfl

noncomputable def hp752212 := hp752205 rfl rfl rfl rfl (hp752210 (hp752211 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp752213 := @hp752202 12500018513 1089000000000000000 44343197564110210477793 18014398509481984000 10231902653834663 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 818551 4000) (BSN.isNear_log_sfrac 2680103958404 16000000 54172797497175143 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp752204 1000001481040000 87120000000000000000000 54172797497175143 4503599627370496 12500018513 1089000000000000000 (hp752212 rfl rfl rfl) rfl)) rfl

noncomputable def hp752214 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1637102)))) 1 4

noncomputable def hp752215 := @hp752214 0 1 883935853184419 562949953421312 200000001089 2178000000000000000 883935853184419 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp752216 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1637102))) 884279719003555 562949953421312 1

noncomputable def hp752217 := @hp752216 2000000000000000 20496 33554432 1 10890000 29659965478038570795008 883935853184419 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp752218 := BSN.arctan_dyadic_bound_f 1000 1637102 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp752219 := hp752218 1 20496 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1637102) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1637102) 0 0 rfl)

noncomputable def hp752220 := hp752215 (hp752217 (hp752219 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp752221 := @hp752194 31441166827311 67108864000 2455653 536870912000 hp752195 5704670033131187968877 3602879701896396800 113801439274781857 16384000000000000000000 (@hp752197 1 hp752198 36963274120117241383201 18014398509481984000 9487513915867 4000000000000000000 (@hp752201 4000000000000000000 hp752213 hp752220 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 818551 2000) rfl rfl)

noncomputable def hp752222 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 818551 2000) (Real.log Real.pi) 818551 2000 0 1 38410761 33554432

noncomputable def hp752223 := hp752221 (@hp752222 3 268435456 31441166827311 67108864000 2455653 536870912000 (Enclosure.Real.IsNear.const Bool.false 818551 2000) hd4909 rfl) rfl

noncomputable def hp752224 := @hp752184 16384000000000000000000 106257745987 67108864 467 67108864 (@hp752188 hp752182 hp752183 113801439274781857 16384000000000000000000 (hp752190 rfl rfl rfl rfl rfl) (hp752193 (hp752223 rfl) (Enclosure.Real.IsNear.const Bool.true hp752186 hp752187) rfl rfl)) rfl

noncomputable def hp752225 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 106257745987) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 10673731307973801672704) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp752226 := BSN.sin_reduce_arg_pos_rat_q0 106257745987 67108864 226375608064910080 72057594037927936 252 10673731307973801672704 hp617687 rfl rfl rfl rfl

noncomputable def hp752227 := BSN.cos_dyadic_bound_f 151682844 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp752228 := hp752227 1 67108823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 151682844) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp752229 := hp752228 (@BSN.binarySplit_of_le (BSN.cosOddP 151682844) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp752230 := @BSN.cos_arg_round Bool.false 67108823 67108864 10673731307973801672704 hp617687 151682844 137438953472 21801270 21780000 hp752229 rfl

noncomputable def hp752231 := hp752225 67108823 67108864 252 1000000000000000 21780000 10890000 hp752226 BSN.pi_near_15 hp752230 rfl rfl

noncomputable def hp752232 := @hp752181 467 67108864 Bool.false 67108823 67108864 1 10890000 hp752224 (Enclosure.sfrac_false_div 106257745987 67108864) (hp752231 rfl rfl) rfl

noncomputable def hp752233 := @hp752178 67108823 67108864 322046179 45675970560000 536870584 536870912 3786 536870912 (@hp752179 Bool.false 67108823 67108864 322046179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000)) (@hp752180 5152738864 730815528960000 67108823 67108864 322046179 45675970560000 (hp752232 rfl) rfl))

noncomputable def hp752234 := @hp752184 16384000000000000000000 850061967900 536870912 3730 536870912 (@hp752188 hp752182 hp752183 113801439274781857 16384000000000000000000 (hp752190 rfl rfl rfl rfl rfl) (hp752193 (hp752223 rfl) (Enclosure.Real.IsNear.const Bool.true hp752186 hp752187) rfl rfl)) rfl

noncomputable def hp752235 := hp752177 (BSN.cos_quad_nat3 435 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 384086129 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl rfl (hp752233 rfl) hp752234

noncomputable def hp752236 := nat_lit 28256283027834961692252379819885956821071312765070245039060805937082249783125798155061739510703308834883187183616

noncomputable def hp752237 := nat_lit 8593693388643564443859942962941274603980735764787118447943343831827910585543490205888214850967602902798336

noncomputable def hp752238 := nat_lit 171253935145706925775636648404910767347918717306665207856638611882749188195332549262866759925785530677278229073920

noncomputable def hp752239 := BSN.cos_dyadic_bound_f 672741658 536870912 4 3 536870912 268435456 hp752236 hp716712 hp752237 hp752238 hp716714

noncomputable def hp752240 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 672741658) (BSN.cosEvenQ 536870912) 0 3 hp752236 hp716712 hp752237 rfl rfl rfl

noncomputable def hp752241 := hp752239 hp752237 167717915 rfl rfl rfl rfl rfl rfl rfl rfl (hp752240 rfl)

noncomputable def hp752242 := @BSN.binarySplit_of_base3 (BSN.cosOddP 672741658) (BSN.cosOddQ 536870912) 0 3 hp752238 hp716714 hp752237 rfl rfl rfl

noncomputable def hp752243 := nat_lit 8431611008517473394306170390988831360020406175385090024242500819924640000

noncomputable def hp752244 := nat_lit 1126114476277682705499120277213335086020001412598636279807680100000000

noncomputable def hp752245 := nat_lit 22080967503631790260707257210236212924199888552292933223801146855831200000

noncomputable def hp752246 := BSN.sin_dyadic_bound_f 428003990 536870912 3 2 536870912 268435456 hp752243 hp708845 hp752244 hp752245 hp708848

noncomputable def hp752247 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 428003990) (BSN.sinEvenQ 536870912) 0 2 hp752243 hp708845 hp752244 rfl rfl rfl

noncomputable def hp752248 := hp752246 hp752244 384086129 rfl rfl rfl rfl rfl rfl rfl rfl (hp752247 rfl)

noncomputable def hp752249 := @BSN.binarySplit_of_base2 (BSN.sinOddP 428003990) (BSN.sinOddQ 536870912) 0 2 hp752245 hp708848 hp752244 rfl rfl rfl

noncomputable def hp752250 := hp752235 hd4911 hd4913 hd4915 hd4917 hd4918 (hp752241 (hp752242 rfl) rfl rfl rfl rfl) (hp752248 (hp752249 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752251 := hp752172 (BSN.cos_quad_nat1 169 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 253722649 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl rfl (hp752250 rfl rfl rfl rfl rfl) hp752234

noncomputable def hp752252 := nat_lit 15902745450315684557492281848847430675468115964700164629455603146523967745

noncomputable def hp752253 := nat_lit 4005003233535522569110117876283669627390903833118365315443900401352961

noncomputable def hp752254 := nat_lit 41643563317020116328320274175181668684924527968008715723777765735484391681

noncomputable def hp752255 := BSN.sin_dyadic_bound_f 501562847 536870912 3 2 536870912 268435456 hp752252 hp708845 hp752253 hp752254 hp708848

noncomputable def hp752256 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 501562847) (BSN.sinEvenQ 536870912) 0 2 hp752252 hp708845 hp752253 rfl rfl rfl

noncomputable def hp752257 := hp752255 hp752253 431721384 rfl rfl rfl rfl rfl rfl rfl rfl (hp752256 rfl)

noncomputable def hp752258 := @BSN.binarySplit_of_base2 (BSN.sinOddP 501562847) (BSN.sinOddQ 536870912) 0 2 hp752254 hp708848 hp752253 rfl rfl rfl

noncomputable def hp752259 := nat_lit 1225274273794269281017765612779585645859817639863256409971940657169465600

noncomputable def hp752260 := nat_lit 23786316880589265247111423460188166092783018985414842597038217789696

noncomputable def hp752261 := nat_lit 3209013158281470020045652710213312577363943598563504687800401754519798016

noncomputable def hp752262 := BSN.sin_dyadic_bound_f 264265762 536870912 3 2 536870912 268435456 hp752259 hp708845 hp752260 hp752261 hp708848

noncomputable def hp752263 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 264265762) (BSN.sinEvenQ 536870912) 0 2 hp752259 hp708845 hp752260 rfl rfl rfl

noncomputable def hp752264 := hp752262 hp752260 253722649 rfl rfl rfl rfl rfl rfl rfl rfl (hp752263 rfl)

noncomputable def hp752265 := @BSN.binarySplit_of_base2 (BSN.sinOddP 264265762) (BSN.sinOddQ 536870912) 0 2 hp752261 hp708848 hp752260 rfl rfl rfl

noncomputable def hp752266 := hp752251 hd4920 hd4922 hd4924 hd4926 hd4918 (hp752257 (hp752258 rfl) rfl rfl rfl rfl) (hp752264 (hp752265 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752267 := hp752167 (BSN.cos_quad_nat2 6 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536481378 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl rfl (hp752266 rfl rfl rfl rfl rfl) hp752234

noncomputable def hp752268 := nat_lit 607252521939712822672564555720933580977893988473320173474729731470190625

noncomputable def hp752269 := nat_lit 18929276746226974943056655188372327858263484150456135047698625390625

noncomputable def hp752270 := nat_lit 1821719707265646014067807553852423998277965438451659608154093797159790625

noncomputable def hp752271 := BSN.cos_dyadic_bound_f 256827635 536870912 3 2 536870912 268435456 hp752268 hp708868 hp752269 hp752270 hp708870

noncomputable def hp752272 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 256827635) (BSN.cosEvenQ 536870912) 0 2 hp752268 hp708868 hp752269 rfl rfl rfl

noncomputable def hp752273 := hp752271 hp752269 476603080 rfl rfl rfl rfl rfl rfl rfl rfl (hp752272 rfl)

noncomputable def hp752274 := @BSN.binarySplit_of_base2 (BSN.cosOddP 256827635) (BSN.cosOddQ 536870912) 0 2 hp752270 hp708870 hp752269 rfl rfl rfl

noncomputable def hp752275 := nat_lit 174982222833663047960659756816

noncomputable def hp752276 := BSN.cos_dyadic_bound_f 20452598 536870912 2 1 536870912 268435456 hp752275 hp708767 hp752275 hp752275 hp708768

noncomputable def hp752277 := @BSN.binarySplit_of_base (BSN.cosEvenP 20452598) (BSN.cosEvenQ 536870912) 0 1 hp752275 hp708767 hp752275 rfl rfl rfl

noncomputable def hp752278 := hp752276 hp752275 536481378 rfl rfl rfl rfl rfl rfl rfl rfl (hp752277 rfl)

noncomputable def hp752279 := @BSN.binarySplit_of_base (BSN.cosOddP 20452598) (BSN.cosOddQ 536870912) 0 1 hp752275 hp708768 hp752275 rfl rfl rfl

noncomputable def hp752280 := hp752267 hd4928 hd4930 hd4932 hd4934 hd4918 (hp752273 (hp752274 rfl) rfl rfl rfl rfl) (hp752278 (hp752279 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752281 := hp752162 (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 12102859 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl rfl (hp752280 rfl rfl rfl rfl rfl) hp752234

noncomputable def hp752282 := nat_lit 17395999231440385882190720695141772693098432078364410865712401721122145025

noncomputable def hp752283 := nat_lit 4792221480364600712719099623186003751176067013890374634353834590257921

noncomputable def hp752284 := nat_lit 45553191533280420337917008992648055904422560858646205946505431632649962241

noncomputable def hp752285 := BSN.sin_dyadic_bound_f 512940641 536870912 3 2 536870912 268435456 hp752282 hp708845 hp752283 hp752284 hp708848

noncomputable def hp752286 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 512940641) (BSN.sinEvenQ 536870912) 0 2 hp752282 hp708845 hp752283 rfl rfl rfl

noncomputable def hp752287 := hp752285 hp752283 438387288 rfl rfl rfl rfl rfl rfl rfl rfl (hp752286 rfl)

noncomputable def hp752288 := @BSN.binarySplit_of_base2 (BSN.sinOddP 512940641) (BSN.sinOddQ 536870912) 0 2 hp752284 hp708848 hp752283 rfl rfl rfl

noncomputable def hp752289 := nat_lit 65980158954010382969946202300126709880786349091586072552889518630134481883077923745548727030152426319777990967296

noncomputable def hp752290 := nat_lit 108776531701408332357291830232391368022432271916739210328233506589711840084492413909819078192699792389308416

noncomputable def hp752291 := nat_lit 399369491375774672156771386875043399156145010768639533888675664277244180725685543786016116573799391483186045255680

noncomputable def hp752292 := BSN.cos_dyadic_bound_f 831210972 536870912 4 3 536870912 268435456 hp752289 hp716712 hp752290 hp752291 hp716714

noncomputable def hp752293 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 831210972) (BSN.cosEvenQ 536870912) 0 3 hp752289 hp716712 hp752290 rfl rfl rfl

noncomputable def hp752294 := hp752292 hp752290 12102859 rfl rfl rfl rfl rfl rfl rfl rfl (hp752293 rfl)

noncomputable def hp752295 := @BSN.binarySplit_of_base3 (BSN.cosOddP 831210972) (BSN.cosOddQ 536870912) 0 3 hp752291 hp716714 hp752290 rfl rfl rfl

noncomputable def hp752296 := hp752281 hd4936 hd4938 hd4940 hd4942 hd4918 (hp752287 (hp752288 rfl) rfl rfl rfl rfl) (hp752294 (hp752295 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752297 := hp752157 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 411677340 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl rfl (hp752296 rfl rfl rfl rfl rfl) hp752234

noncomputable def hp752298 := nat_lit 113605958168908855248563093277760967219791616702006398948309393827515183296649109028976720349198306776950985877121

noncomputable def hp752299 := nat_lit 31797047477965794141003655647266086142100724982068451809084898587630590243411329760957895767539083806664321

noncomputable def hp752300 := nat_lit 567587407171928113281643804953040549968096136649138999014478440352208816759189625722702711530316570347359717975681

noncomputable def hp752301 := BSN.sin_dyadic_bound_f 750237727 536870912 4 3 536870912 268435456 hp752298 hp642702 hp752299 hp752300 hp642705

noncomputable def hp752302 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 750237727) (BSN.sinEvenQ 536870912) 0 3 hp752298 hp642702 hp752299 rfl rfl rfl

noncomputable def hp752303 := hp752301 hp752299 528822725 rfl rfl rfl rfl rfl rfl rfl rfl (hp752302 rfl)

noncomputable def hp752304 := @BSN.binarySplit_of_base3 (BSN.sinOddP 750237727) (BSN.sinOddQ 536870912) 0 3 hp752300 hp642705 hp752299 rfl rfl rfl

noncomputable def hp752305 := nat_lit 12172540397360808709406742284915783476289915825179403096111016165207244800

noncomputable def hp752306 := nat_lit 2346780156696784353367647683758167502243807512516026051814457931268096

noncomputable def hp752307 := nat_lit 31876663396643656588064586935672395880993765758544839304778295119844540416

noncomputable def hp752308 := BSN.sin_dyadic_bound_f 469147116 536870912 3 2 536870912 268435456 hp752305 hp708845 hp752306 hp752307 hp708848

noncomputable def hp752309 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 469147116) (BSN.sinEvenQ 536870912) 0 2 hp752305 hp708845 hp752306 rfl rfl rfl

noncomputable def hp752310 := hp752308 hp752306 411677340 rfl rfl rfl rfl rfl rfl rfl rfl (hp752309 rfl)

noncomputable def hp752311 := @BSN.binarySplit_of_base2 (BSN.sinOddP 469147116) (BSN.sinOddQ 536870912) 0 2 hp752307 hp708848 hp752306 rfl rfl rfl

noncomputable def hp752312 := hp752297 hd4944 hd4946 hd4961 hd4963 hd4918 (hp752303 (hp752304 rfl) rfl rfl rfl rfl) (hp752310 (hp752311 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752313 := @hp752152 198631 268435456 (hp752312 rfl rfl rfl rfl rfl) (hp752312 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp752314 := @hp752150 Bool.false 28871697 67108864 198631 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 818551 1000)) (Enclosure.sfrac Bool.false 818551 1000) 11) hp752313

noncomputable def hp752315 := @Enclosure.Real.IsNear.mulLit_tf hp752141 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1))) 9931925 33554432 1

noncomputable def hp752316 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp752140 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752317 := @hp752316 1 1 0 1 9931925 33554432 1 33554432 9931925 33554432 1

noncomputable def hp752318 := @Enclosure.Real.IsNear.of_eq (hp752140 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752319 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 818551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752320 := @hp752318 (@Inv.inv Real Real.instInv (Real.sqrt hp752142)) Bool.false 9931925 33554432 1 33554432 (hp752319 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 818551 1000) 818551 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000))))

noncomputable def hp752321 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp752142)) Bool.false 19863850 67108864 2 67108864 9931925 33554432

noncomputable def hp752322 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp752142) Bool.false 226723403 67108864 7 67108864 226723403 67108864 7 67108864

noncomputable def hp752323 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 818551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752324 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 818551 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752325 := @hp752324 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 818551 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8742703395557

noncomputable def hp752326 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 818551 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 818551 1000 0

noncomputable def hp752327 := @hp752326 1 10680707 67108864 1 67108864 8742703395557 67108864000 818551 67108864000 (Enclosure.Real.IsNear.const Bool.false 818551 1000) hd4949

noncomputable def hp752328 := @hp752325 67108864000 818551 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 818551 1000) 818551 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000))) (hp752327 rfl)

noncomputable def hp752329 := @hp752323 8742703395557 67108864000 818551 67108864000 382985913 382985949 33554432 hp752328 rfl rfl rfl

noncomputable def hp752330 := @Enclosure.Real.IsNear.recentre' hp752142 Bool.false 765971862 67108864 36 67108864 382985931 33554432 9 16777216 (hp752329 rfl rfl rfl)

noncomputable def hp752331 := @Enclosure.Real.IsNear.sqrt_image hp752142 382985931 33554432 9 16777216 113361698 113361705 33554432 (hp752330 rfl) rfl rfl

noncomputable def hp752332 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp752142) 226723403 67108864 7 67108864 9931924 9931926 33554432 (hp752322 (hp752331 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp752333 := @hp752317 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp752320 (@hp752321 1 33554432 (hp752332 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp752334 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752335 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp752336 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1))) (hp752334 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752335 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp752337 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 818551 1000) 818551 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl

noncomputable def hp752338 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752339 := @hp752338 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752335 (Enclosure.sfrac Bool.false 1 16)))) 19574243

noncomputable def hp752340 := @hp752339 16777216 159 33554432 11382355 33554432 142986527 22837985280000 222800982682265 562949953421312 170738003235851 19157890602369024000

noncomputable def hp752341 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752342 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752343 := @hp752341 (@Neg.neg Real Real.instNeg hp752342) Bool.true 19574243 16777216 159 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752344 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752345 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp752346 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp752347 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 87255719) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp752348 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1))) Bool.false 12280150743872069921345

noncomputable def hp752349 := nat_lit 242874678741041388735218687

noncomputable def hp752350 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp752351 := @Enclosure.Real.IsNear.subLit_ff_p hp752142 (Enclosure.sfrac Bool.false 11 1) 382985931 33554432 9 16777216 11 1 0

noncomputable def hp752352 := @hp752350 500000000000000 13887179 33554432 9 16777216 12280150743872069921345 4722366482869645213696 hp752349 hp631123 hd4948 (@hp752351 1 13887179 13887179 33554432 9 16777216 (hp752330 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752353 := @hp752347 87255719 33554432 227 67108864 Bool.true 57519461 67108864 1 10890000 (@hp752348 4722366482869645213696 hp752349 hp631123 87255719 33554432 227 67108864 (hp752352 rfl) rfl) (Enclosure.sfrac_false_div 87255719 33554432)

noncomputable def hp752354 := nat_lit 4978969407106353786257408

noncomputable def hp752355 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 87255719) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp752354) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp752356 := BSN.sin_reduce_arg_pos_rat_q1 87255719 33554432 226375608064910080 72057594037927936 0 hp752354 hp619237 rfl rfl rfl rfl

noncomputable def hp752357 := nat_lit 432853699365221094069784533306674133352929859686578065881229163379043824124574943023221799745

noncomputable def hp752358 := nat_lit 160811544577837126194981032505945693796949580939814120575210615506464354827183595794824001

noncomputable def hp752359 := nat_lit 1133404089170072081502262856036279770515335523667135235398478420234294787561309410667627379521

noncomputable def hp752360 := BSN.sin_dyadic_bound_f 141510821751 137438953472 3 2 67108864 21801270 hp752357 hp738039 hp752358 hp752359 hp738042

noncomputable def hp752361 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 141510821751) (BSN.sinEvenQ 137438953472) 0 2 hp752357 hp738039 hp752358 rfl rfl rfl

noncomputable def hp752362 := hp752360 hp752358 57519461 rfl rfl rfl rfl rfl rfl rfl rfl (hp752361 rfl)

noncomputable def hp752363 := @BSN.binarySplit_of_base2 (BSN.sinOddP 141510821751) (BSN.sinOddQ 137438953472) 0 2 hp752359 hp738042 hp752358 rfl rfl rfl

noncomputable def hp752364 := @BSN.sin_arg_round Bool.false 57519461 67108864 hp752354 hp619237 141510821751 137438953472 21801270 21780000 (hp752362 (hp752363 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752365 := hp752355 57519461 67108864 0 1000000000000000 21780000 10890000 hp752356 BSN.pi_near_15 hp752364 rfl rfl

noncomputable def hp752366 := @hp752345 57519461 67108864 158696179 45675970560000 (@hp752346 57519461 67108864 2539138864 730815528960000 57519461 67108864 158696179 45675970560000 (hp752353 (hp752365 rfl rfl) rfl rfl) rfl)

noncomputable def hp752367 := @hp752344 57519461 67108864 158696179 45675970560000 39148327 39148645 33554432 hp752366 rfl rfl rfl

noncomputable def hp752368 := @Enclosure.Real.IsNear.recentre' hp752342 Bool.false 78296972 67108864 318 67108864 19574243 16777216 159 33554432 (hp752367 rfl rfl rfl)

noncomputable def hp752369 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752335 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp752370 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752335 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 64319973)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp752371 := nat_lit 303742484885927967658749810805

noncomputable def hp752372 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752335 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp752371

noncomputable def hp752373 := nat_lit 372380363459708447625193769947663

noncomputable def hp752374 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752335 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp752375 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp752376 := @hp752375 (Enclosure.sfrac Bool.false 1 16) 273122662849287 1125899906842624 68994909 70368744177664 1 16 0

noncomputable def hp752377 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)) 192853740578041

noncomputable def hp752378 := @hp752377 1125899906842624 31246173 70368744177664 13887179 33554432 9 16777216 9164475818235326889984 273122662849287 1125899906842624 68994909

noncomputable def hp752379 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)) 13887179 33554432 9

noncomputable def hp752380 := @hp752379 16777216 13887179 33554432 9 16777216 192853740578041 1125899906842624 31246173 70368744177664 (@hp752351 1 13887179 13887179 33554432 9 16777216 (hp752330 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752381 := hp752380 (@hp752351 1 13887179 13887179 33554432 9 16777216 (hp752330 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752382 := @hp752378 70368744177664 (hp752381 rfl) (@hp752351 1 13887179 13887179 33554432 9 16777216 (hp752330 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752383 := @hp752374 500000000000000 343491407026951 1125899906842624 68994909 70368744177664 hp752371 hp682141 hp752373 hp632690 hd4948 (@hp752376 1 5495862512431216 343491407026951 1125899906842624 68994909 70368744177664 (hp752382 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp752384 := @hp752370 64319973 33554432 207 33554432 Bool.true 11382355 33554432 1 10890000 (@hp752372 hp682141 hp752373 hp632690 64319973 33554432 207 33554432 (hp752383 rfl) rfl) (Enclosure.sfrac_true_div 64319973 33554432)

noncomputable def hp752385 := nat_lit 553335485416164964325778862289256376210064756458266100993581939850031340765505991419585961620782801

noncomputable def hp752386 := nat_lit 5013606459179224115275533574143759985235089528682568143735710547562806014823217744862024679121

noncomputable def hp752387 := nat_lit 3339034617614934574658594090937820411308790164070713531812480146814595861720717949172571677539811025

noncomputable def hp752388 := BSN.cos_dyadic_bound_t 64319973 33554432 4 3 33554432 10890000 hp752385 hp681868 hp752386 hp752387 hp681871

noncomputable def hp752389 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 64319973) (BSN.cosEvenQ 33554432) 0 3 hp752385 hp681868 hp752386 rfl rfl rfl

noncomputable def hp752390 := hp752388 hp752386 11382355 rfl rfl rfl rfl rfl rfl rfl rfl (hp752389 rfl)

noncomputable def hp752391 := @BSN.binarySplit_of_base3 (BSN.cosOddP 64319973) (BSN.cosOddQ 33554432) 0 3 hp752387 hp681871 hp752386 rfl rfl rfl

noncomputable def hp752392 := hp752384 (BSN.cos_neg_of_bound 64319973 33554432 Bool.true 11382355 33554432 1 10890000 (hp752390 (hp752391 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp752393 := hp752340 (hp752343 (@Enclosure.Real.IsNear.neg hp752342 Bool.false 19574243 16777216 159 33554432 (hp752368 rfl))) (@hp752369 11382355 33554432 2287784432 365407764480000 11382355 33554432 142986527 22837985280000 (hp752392 rfl) rfl)

noncomputable def hp752394 := @hp752315 33554432 222800982682265 562949953421312 170738003235851 19157890602369024000 2212842649926554810125 18889465931478580854784 2271119212624184679743 hp752138 (hp752333 rfl) (@hp752336 Bool.false 222800982682265 562949953421312 170738003235851 19157890602369024000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752142 (Enclosure.sfrac Bool.false 11 1)) (hp752337 rfl (hp752145 rfl rfl))) (hp752393 rfl))

noncomputable def hp752395 := @hp752139 636496280585817785703743 hp752138 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 818551 1000))) (@hp752144 636496280585817785703743 hp752138 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 818551 1000) 11 (hp752145 rfl rfl)) (@hp752148 636496280585817785703743 hp752138 hp752314 (hp752394 rfl) rfl rfl))

theorem hd5019 : hp752137 hp752138 := hp752395

noncomputable def hp752396 := nat_lit 4781309478186806873653129

noncomputable def hp752397 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 819841 1000)) Bool.true 15780327723276270924517 9444732965739290427392 hp752396

noncomputable def hp752398 := nat_lit 6428321374806304547143680000

noncomputable def hp752399 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 819841 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 819841 1000)) Bool.true 15780327723276270924517 9444732965739290427392

noncomputable def hp752400 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 819841 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752401 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp752400 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752402 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 819841 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752403 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp752401 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp752404 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 819841 1000)) hp752403 Bool.true 15780327723276270924517 9444732965739290427392

noncomputable def hp752405 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 819841 1000) 819841 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl

noncomputable def hp752406 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp752401 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp752407 := nat_lit 2117999734113553799801131237376

noncomputable def hp752408 := @hp752406 239865355 134217728 99473 134217728 1098696079803287506203 9444732965739290427392 17077348463172062773129 hp752398 hp752407 15780327723276270924517 9444732965739290427392

noncomputable def hp752409 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) 11)

noncomputable def hp752410 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) 11) hp752409

noncomputable def hp752411 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) 11)

noncomputable def hp752412 := @hp752411 479730710 536870912 198946 536870912 479730710 536870912 198946 536870912 515106927584215040 239865355 134217728

noncomputable def hp752413 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp752414 := hp752413 BSN.quadSignNeg 9 10 11 819841 1000 191 241 536870912 268435456 9007199254740992

noncomputable def hp752415 := hp752414 Bool.false 851748514294 3736 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp752416 := hp752415 Bool.true 520550363 170790 Bool.true 658377666 Bool.true 443295406 28296951008113761 1 Bool.false 505331768

noncomputable def hp752417 := hp752416 Bool.false Bool.false 394612991 Bool.true Bool.true 479730710 198946 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 505331768 536870912) BSN.abs_quadSignNeg

noncomputable def hp752418 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp752419 := hp752418 BSN.quadSignPos 7 8 9 819841 1000 75 136 536870912 268435456 9007199254740992

noncomputable def hp752420 := hp752419 Bool.false 851748514294 3736 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp752421 := hp752420 Bool.true 668878287 139484 Bool.true 266539509 Bool.true 666382051 28296951008113761 1 Bool.false 255724174

noncomputable def hp752422 := hp752421 Bool.false Bool.false 173747322 Bool.false Bool.true 520550363 170790 BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 255724174 536870912) BSN.abs_quadSignPos

noncomputable def hp752423 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp752424 := hp752423 BSN.quadSignNeg 5 6 7 819841 1000 74 5 536870912 268435456 9007199254740992

noncomputable def hp752425 := hp752424 Bool.false 851748514294 3736 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp752426 := hp752425 Bool.true 443774513 103654 Bool.false 702466872 Bool.true 524887339 28296951008113761 1 Bool.false 139237834

noncomputable def hp752427 := hp752426 Bool.true Bool.false 445174543 Bool.true Bool.true 668878287 139484 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 139237834 536870912) BSN.abs_quadSignNeg

noncomputable def hp752428 := hp752423 BSN.quadSignNeg 3 4 5 819841 1000 286 169 536870912 268435456 9007199254740992

noncomputable def hp752429 := hp752428 Bool.false 851748514294 3736 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp752430 := hp752429 Bool.true 1279899 61267 Bool.false 384697561 Bool.false 836174261 28296951008113761 1 Bool.false 404839759

noncomputable def hp752431 := hp752430 Bool.true Bool.false 536823426 Bool.true Bool.true 443774513 103654 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 286 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 404839759 536870912) BSN.abs_quadSignNeg

noncomputable def hp752432 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp752433 := hp752432 BSN.quadSignPos 1 2 3 819841 1000 648 436 536870912 268435456 9007199254740992

noncomputable def hp752434 := hp752433 Bool.false 851748514294 3736 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp752435 := hp752434 Bool.true 536870664 3794 Bool.false 192609937 Bool.false 510376788 28296951008113761 1 Bool.false 502689163

noncomputable def hp752436 := hp752435 Bool.false Bool.false 312004439 Bool.false Bool.true 1279899 61267 BSN.abs_quadSignPos (BSN.cos_quad_nat0 648 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 502689163 536870912) BSN.abs_quadSignPos

noncomputable def hp752437 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) 1) Bool.true

noncomputable def hp752438 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)))

noncomputable def hp752439 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000))) Bool.true 67108833 67108864

noncomputable def hp752440 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 53234282143) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 53234282143 33554432

noncomputable def hp752441 := nat_lit 78105581681465373547694689240555358266300079765685205301167

noncomputable def hp752442 := nat_lit 49231215747213736474887246450191095626913836586500096000

noncomputable def hp752443 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) Bool.false hp752441 hp752442 41374809888278171981

noncomputable def hp752444 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 819841 4000) (Real.log (Enclosure.sfrac Bool.false 2688558061124 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1639682))))))

noncomputable def hp752445 := nat_lit 177782829485629590373994509696480000

noncomputable def hp752446 := nat_lit 874522068045524329613855599955327158080

noncomputable def hp752447 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp752444 (Enclosure.sfrac Bool.false 819841 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 819841 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp752445 hp752446)) Bool.false

noncomputable def hp752448 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 819841 1000) 819841 1000 2688558061124 16000000 1639682

noncomputable def hp752449 := hp752448 4000 2000 hp752445 hp752446 (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl rfl rfl rfl

noncomputable def hp752450 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp752444 (Enclosure.sfrac Bool.false 819841 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 819841 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp752445 hp752446) 28579941266180346824743 18014398509481984000

noncomputable def hp752451 := nat_lit 24993786138068919535262300556977714645216025525019265696373440

noncomputable def hp752452 := @hp752450 41374809888278171981 hp737908 hp752445 hp752446 0 1 hp752451 hp752441 hp752442 41374809888278171981 hp737908

noncomputable def hp752453 := @Enclosure.Real.IsNear.subLit_ff_p (hp752444 (Enclosure.sfrac Bool.false 819841 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 819841 2000) (Real.log Real.pi)) 37033166165727849564199 18014398509481984000 3449342559420311 1452000000000000000000

noncomputable def hp752454 := nat_lit 1917967391560084694534509821952000

noncomputable def hp752455 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 819841 4000) (Real.log (Enclosure.sfrac Bool.false 2688558061124 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1639682))))))

noncomputable def hp752456 := @hp752455 (Enclosure.sfrac Bool.false 819841 2000) 44417637409933959186471 18014398509481984000 3449342559420311 1452000000000000000000 819841 2000 0

noncomputable def hp752457 := nat_lit 74066332331455699128398000

noncomputable def hp752458 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 819841 4000) (Real.log (Enclosure.sfrac Bool.false 2688558061124 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1639682))))) 44424708901188619562471

noncomputable def hp752459 := nat_lit 100019627644028190838327455594533879808

noncomputable def hp752460 := @hp752458 18014398509481984000 931638879792403 396000000000000000000 883936406832547 2251799813685248 200000001089 8712000000000000000 hp752459 44417637409933959186471 18014398509481984000 3449342559420311

noncomputable def hp752461 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 819841 4000) (Real.log (Enclosure.sfrac Bool.false 2688558061124 16000000)) 819841 4000 0 1 54186981257571431 4503599627370496

noncomputable def hp752462 := nat_lit 116365656185117124264460288

noncomputable def hp752463 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2688558061124) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp752462 hp617687

noncomputable def hp752464 := BSN.log_rat_reduce_isNear 2688558061124 16000000 17 5377116122248 4194304000000 66686018 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp752465 := nat_lit 260017679226891263938453513613596854180850218759783752193781739764725985518765657817381280858362461880320

noncomputable def hp752466 := nat_lit 1335872992316443802519862928034418720864734766950913090146017595784168306121537666947933925874342559744

noncomputable def hp752467 := nat_lit 1571359184431693448280227573338388870133846769689874674564844780026669773495944060415317855764480

noncomputable def hp752468 := BSN.log_dyadic_bound 591406061124 4785710061124 5 4 hp752465 268435456 87120000 hp752466 hp752467 66686018 5377116122248

noncomputable def hp752469 := hp752468 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp752470 := @BSN.binarySplit_of_base4 (BSN.artanhP 591406061124) (BSN.artanhQ 4785710061124) 0 4 hp752466 hp752465 hp752467 rfl rfl rfl

noncomputable def hp752471 := hp752464 rfl rfl rfl rfl (hp752469 (hp752470 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp752472 := @hp752461 12500018513 1089000000000000000 44424708901188619562471 18014398509481984000 931638879792403 396000000000000000000 (Enclosure.Real.IsNear.const Bool.false 819841 4000) (BSN.isNear_log_sfrac 2688558061124 16000000 54186981257571431 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp752463 1000001481040000 87120000000000000000000 54186981257571431 4503599627370496 12500018513 1089000000000000000 (hp752471 rfl rfl rfl) rfl)) rfl

noncomputable def hp752473 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1639682)))) 1 4

noncomputable def hp752474 := @hp752473 0 1 883936406832547 562949953421312 200000001089 2178000000000000000 883936406832547 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp752475 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1639682))) 884279719003555 562949953421312 1

noncomputable def hp752476 := @hp752475 2000000000000000 20463 33554432 1 10890000 29659984055387033698304 883936406832547 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp752477 := BSN.arctan_dyadic_bound_f 1000 1639682 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp752478 := hp752477 1 20463 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1639682) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1639682) 0 0 rfl)

noncomputable def hp752479 := hp752474 (hp752476 (hp752478 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp752480 := @hp752453 31490716709001 67108864000 2459523 536870912000 hp752454 28579941266180346824743 18014398509481984000 41374809888278171981 hp737908 (@hp752456 1 hp752457 37033166165727849564199 18014398509481984000 3449342559420311 1452000000000000000000 (@hp752460 1452000000000000000000 hp752472 hp752479 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 819841 2000) rfl rfl)

noncomputable def hp752481 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 819841 2000) (Real.log Real.pi) 819841 2000 0 1 38410761 33554432

noncomputable def hp752482 := hp752480 (@hp752481 3 268435456 31490716709001 67108864000 2459523 536870912000 (Enclosure.Real.IsNear.const Bool.false 819841 2000) hd4909 rfl) rfl

noncomputable def hp752483 := @hp752443 hp737908 53234282143 33554432 117 16777216 (@hp752447 hp752441 hp752442 41374809888278171981 hp737908 (hp752449 rfl rfl rfl rfl rfl) (hp752452 (hp752482 rfl) (Enclosure.Real.IsNear.const Bool.true hp752445 hp752446) rfl rfl)) rfl

noncomputable def hp752484 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 53234282143) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 4586376217142121988096) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp752485 := BSN.sin_reduce_arg_pos_rat_q2 53234282143 33554432 226375608064910080 72057594037927936 252 4586376217142121988096 hp619237 rfl rfl rfl rfl

noncomputable def hp752486 := BSN.cos_dyadic_bound_f 130352652 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp752487 := hp752486 1 67108833 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 130352652) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp752488 := hp752487 (@BSN.binarySplit_of_le (BSN.cosOddP 130352652) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp752489 := @BSN.cos_arg_round Bool.false 67108833 67108864 4586376217142121988096 hp619237 130352652 137438953472 21801270 21780000 hp752488 rfl

noncomputable def hp752490 := hp752484 67108833 67108864 252 1000000000000000 21780000 10890000 hp752485 BSN.pi_near_15 hp752489 rfl rfl

noncomputable def hp752491 := @hp752440 117 16777216 Bool.true 67108833 67108864 1 10890000 hp752483 (Enclosure.sfrac_false_div 53234282143 33554432) (hp752490 rfl rfl) rfl

noncomputable def hp752492 := @hp752437 67108833 67108864 80681701 11418992640000 536870664 536870912 3794 536870912 (@hp752438 Bool.true 67108833 67108864 80681701 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000)) (@hp752439 1290907216 182703882240000 67108833 67108864 80681701 11418992640000 (hp752491 rfl) rfl))

noncomputable def hp752493 := @hp752443 hp737908 851748514294 536870912 3736 536870912 (@hp752447 hp752441 hp752442 41374809888278171981 hp737908 (hp752449 rfl rfl rfl rfl rfl) (hp752452 (hp752482 rfl) (Enclosure.Real.IsNear.const Bool.true hp752445 hp752446) rfl rfl)) rfl

noncomputable def hp752494 := hp752436 (BSN.cos_quad_nat0 436 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 312004439 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl rfl (hp752492 rfl) hp752493

noncomputable def hp752495 := nat_lit 192091354148309855557632876385780976723816720495739652907035916897308801

noncomputable def hp752496 := nat_lit 1894216056025842198131163302939152351343056563496417868485333307521

noncomputable def hp752497 := nat_lit 576270274012817514988502366830737051866747475374091965885370780025311361

noncomputable def hp752498 := BSN.cos_dyadic_bound_f 192609937 536870912 3 2 536870912 268435456 hp752495 hp708868 hp752496 hp752497 hp708870

noncomputable def hp752499 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 192609937) (BSN.cosEvenQ 536870912) 0 2 hp752495 hp708868 hp752496 rfl rfl rfl

noncomputable def hp752500 := hp752498 hp752496 502689163 rfl rfl rfl rfl rfl rfl rfl rfl (hp752499 rfl)

noncomputable def hp752501 := @BSN.binarySplit_of_base2 (BSN.cosOddP 192609937) (BSN.cosOddQ 536870912) 0 2 hp752497 hp708870 hp752496 rfl rfl rfl

noncomputable def hp752502 := nat_lit 9351030460502388584119811378546644760090967566075134657004322551151369682002592213987033118669362135916542427136

noncomputable def hp752503 := nat_lit 312385576041825330981876285748981651170349867079612617040732370491939317985873151882596045139646617747456

noncomputable def hp752504 := nat_lit 56711205893103303467072065752351643101679728340393575453747856800789726514350206587881454866632852543775713525760

noncomputable def hp752505 := BSN.cos_dyadic_bound_f 510376788 536870912 4 3 536870912 268435456 hp752502 hp716712 hp752503 hp752504 hp716714

noncomputable def hp752506 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 510376788) (BSN.cosEvenQ 536870912) 0 3 hp752502 hp716712 hp752503 rfl rfl rfl

noncomputable def hp752507 := hp752505 hp752503 312004439 rfl rfl rfl rfl rfl rfl rfl rfl (hp752506 rfl)

noncomputable def hp752508 := @BSN.binarySplit_of_base3 (BSN.cosOddP 510376788) (BSN.cosOddQ 536870912) 0 3 hp752504 hp716714 hp752503 rfl rfl rfl

noncomputable def hp752509 := hp752494 hd4911 hd4913 hd4915 hd4917 hd4918 (hp752500 (hp752501 rfl) rfl rfl rfl rfl) (hp752507 (hp752508 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752510 := hp752431 (BSN.cos_quad_nat1 169 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536823426 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl rfl (hp752509 rfl rfl rfl rfl rfl) hp752493

noncomputable def hp752511 := nat_lit 3057276063226292000806055443737243038530467599978653712737700009405760961

noncomputable def hp752512 := nat_lit 479684254327919545345072794895184009416305871662086426767483997177281

noncomputable def hp752513 := nat_lit 9170868821170220163327476185621938747572570188192636965359565060222928321

noncomputable def hp752514 := BSN.cos_dyadic_bound_f 384697561 536870912 3 2 536870912 268435456 hp752511 hp708868 hp752512 hp752513 hp708870

noncomputable def hp752515 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 384697561) (BSN.cosEvenQ 536870912) 0 2 hp752511 hp708868 hp752512 rfl rfl rfl

noncomputable def hp752516 := hp752514 hp752512 404839759 rfl rfl rfl rfl rfl rfl rfl rfl (hp752515 rfl)

noncomputable def hp752517 := @BSN.binarySplit_of_base2 (BSN.cosOddP 384697561) (BSN.cosOddQ 536870912) 0 2 hp752513 hp708870 hp752512 rfl rfl rfl

noncomputable def hp752518 := nat_lit 175424326019315506042390186256196004831933214205892902520477497090812154018136650639001661087903635371200870213521

noncomputable def hp752519 := nat_lit 116831927113684730565203158666247940259941214956853233894373991847899005512322489793997200590955875871352721

noncomputable def hp752520 := nat_lit 876068092448953158688434483363701631170822361157163024355651938860680464486608668876337062902984481545376296200081

noncomputable def hp752521 := BSN.sin_dyadic_bound_f 836174261 536870912 4 3 536870912 268435456 hp752518 hp642702 hp752519 hp752520 hp642705

noncomputable def hp752522 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 836174261) (BSN.sinEvenQ 536870912) 0 3 hp752518 hp642702 hp752519 rfl rfl rfl

noncomputable def hp752523 := hp752521 hp752519 536823426 rfl rfl rfl rfl rfl rfl rfl rfl (hp752522 rfl)

noncomputable def hp752524 := @BSN.binarySplit_of_base3 (BSN.sinOddP 836174261) (BSN.sinOddQ 536870912) 0 3 hp752520 hp642705 hp752519 rfl rfl rfl

noncomputable def hp752525 := hp752510 hd4920 hd4922 hd4924 hd4926 hd4918 (hp752516 (hp752517 rfl) rfl rfl rfl rfl) (hp752523 (hp752524 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752526 := hp752427 (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 445174543 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl rfl (hp752525 rfl rfl rfl rfl rfl) hp752493

noncomputable def hp752527 := nat_lit 33600468850798707556915325414557732451224825080082475889063085286033696786069372368966503037968089219695374237696

noncomputable def hp752528 := nat_lit 14438104316176694842929941583865625023728733638296112282195317456725021163617528173317340349386838367010816

noncomputable def hp752529 := nat_lit 203606091189485067267551103533513191970152331515686503640600724090235947417414613351666616150970783705124548116480

noncomputable def hp752530 := BSN.cos_dyadic_bound_f 702466872 536870912 4 3 536870912 268435456 hp752527 hp716712 hp752528 hp752529 hp716714

noncomputable def hp752531 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 702466872) (BSN.cosEvenQ 536870912) 0 3 hp752527 hp716712 hp752528 rfl rfl rfl

noncomputable def hp752532 := hp752530 hp752528 139237834 rfl rfl rfl rfl rfl rfl rfl rfl (hp752531 rfl)

noncomputable def hp752533 := @BSN.binarySplit_of_base3 (BSN.cosOddP 702466872) (BSN.cosOddQ 536870912) 0 3 hp752529 hp716714 hp752528 rfl rfl rfl

noncomputable def hp752534 := nat_lit 19074662774184999662836633521625194037239449032230082742462811361622558305

noncomputable def hp752535 := nat_lit 5761409931823048993501243556304189144053269655664356839111211282794081

noncomputable def hp752536 := nat_lit 49948122125832999894773133400403396648441518362112474414424992557410748001

noncomputable def hp752537 := BSN.sin_dyadic_bound_f 524887339 536870912 3 2 536870912 268435456 hp752534 hp708845 hp752535 hp752536 hp708848

noncomputable def hp752538 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 524887339) (BSN.sinEvenQ 536870912) 0 2 hp752534 hp708845 hp752535 rfl rfl rfl

noncomputable def hp752539 := hp752537 hp752535 445174543 rfl rfl rfl rfl rfl rfl rfl rfl (hp752538 rfl)

noncomputable def hp752540 := @BSN.binarySplit_of_base2 (BSN.sinOddP 524887339) (BSN.sinOddQ 536870912) 0 2 hp752536 hp708848 hp752535 rfl rfl rfl

noncomputable def hp752541 := hp752526 hd4928 hd4930 hd4932 hd4934 hd4918 (hp752532 (hp752533 rfl) rfl rfl rfl rfl) (hp752539 (hp752540 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752542 := hp752422 (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 173747322 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl rfl (hp752541 rfl rfl rfl rfl rfl) hp752493

noncomputable def hp752543 := nat_lit 1267991616848480015854275737027010758251480478594561543853774881537731425

noncomputable def hp752544 := nat_lit 25473742055112872560423810745923857934413058338391808476234336250721

noncomputable def hp752545 := nat_lit 3320889181877929858777052910805725252031507441843684742403306024625843041

noncomputable def hp752546 := BSN.sin_dyadic_bound_f 266539509 536870912 3 2 536870912 268435456 hp752543 hp708845 hp752544 hp752545 hp708848

noncomputable def hp752547 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 266539509) (BSN.sinEvenQ 536870912) 0 2 hp752543 hp708845 hp752544 rfl rfl rfl

noncomputable def hp752548 := hp752546 hp752544 255724174 rfl rfl rfl rfl rfl rfl rfl rfl (hp752547 rfl)

noncomputable def hp752549 := @BSN.binarySplit_of_base2 (BSN.sinOddP 266539509) (BSN.sinOddQ 536870912) 0 2 hp752545 hp708848 hp752544 rfl rfl rfl

noncomputable def hp752550 := nat_lit 27201394800654540013837657584877994901243249585753555821084880746335406877889476034829074554257577697343775565681

noncomputable def hp752551 := nat_lit 7667953843436207645564557753277152429359021090398397106247768312410921727149813616452072907383524023199601

noncomputable def hp752552 := nat_lit 164866538610625549179033534435662697789752145938504079966720903698884909434548618888730578538107614102368094906225

noncomputable def hp752553 := BSN.cos_dyadic_bound_f 666382051 536870912 4 3 536870912 268435456 hp752550 hp716712 hp752551 hp752552 hp716714

noncomputable def hp752554 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 666382051) (BSN.cosEvenQ 536870912) 0 3 hp752550 hp716712 hp752551 rfl rfl rfl

noncomputable def hp752555 := hp752553 hp752551 173747322 rfl rfl rfl rfl rfl rfl rfl rfl (hp752554 rfl)

noncomputable def hp752556 := @BSN.binarySplit_of_base3 (BSN.cosOddP 666382051) (BSN.cosOddQ 536870912) 0 3 hp752552 hp716714 hp752551 rfl rfl rfl

noncomputable def hp752557 := hp752542 hd4936 hd4938 hd4940 hd4942 hd4918 (hp752548 (hp752549 rfl) rfl rfl rfl rfl) (hp752555 (hp752556 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752558 := hp752417 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 394612991 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl rfl (hp752557 rfl rfl rfl rfl rfl) hp752493

noncomputable def hp752559 := nat_lit 67341556646681710521119545957353367974078126170046890424403004702561485837629592897023943446632248357607096979456

noncomputable def hp752560 := nat_lit 6632863803123296420120739703942948101663817920232368779350163318540779645755617172052754693867907236499456

noncomputable def hp752561 := nat_lit 336552201788968755910891685778564507244948900839240546935816049026096186407233522480827874625253399837805833097216

noncomputable def hp752562 := BSN.sin_dyadic_bound_f 658377666 536870912 4 3 536870912 268435456 hp752559 hp642702 hp752560 hp752561 hp642705

noncomputable def hp752563 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 658377666) (BSN.sinEvenQ 536870912) 0 3 hp752559 hp642702 hp752560 rfl rfl rfl

noncomputable def hp752564 := hp752562 hp752560 505331768 rfl rfl rfl rfl rfl rfl rfl rfl (hp752563 rfl)

noncomputable def hp752565 := @BSN.binarySplit_of_base3 (BSN.sinOddP 658377666) (BSN.sinOddQ 536870912) 0 3 hp752561 hp642705 hp752560 rfl rfl rfl

noncomputable def hp752566 := nat_lit 9702886651181526207242754779129389429750182113428750762525941179588296960

noncomputable def hp752567 := nat_lit 1491234164190023778905847759645764862400877615144557964643151781314816

noncomputable def hp752568 := nat_lit 25409907802542927647136605429918498220520875542841256046101376081751982336

noncomputable def hp752569 := BSN.sin_dyadic_bound_f 443295406 536870912 3 2 536870912 268435456 hp752566 hp708845 hp752567 hp752568 hp708848

noncomputable def hp752570 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 443295406) (BSN.sinEvenQ 536870912) 0 2 hp752566 hp708845 hp752567 rfl rfl rfl

noncomputable def hp752571 := hp752569 hp752567 394612991 rfl rfl rfl rfl rfl rfl rfl rfl (hp752570 rfl)

noncomputable def hp752572 := @BSN.binarySplit_of_base2 (BSN.sinOddP 443295406) (BSN.sinOddQ 536870912) 0 2 hp752568 hp708848 hp752567 rfl rfl rfl

noncomputable def hp752573 := hp752558 hd4944 hd4946 hd4961 hd4963 hd4918 (hp752564 (hp752565 rfl) rfl rfl rfl rfl) (hp752571 (hp752572 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752574 := @hp752412 99473 134217728 (hp752573 rfl rfl rfl rfl rfl) (hp752573 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp752575 := @hp752410 Bool.true 239865355 134217728 99473 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 819841 1000)) (Enclosure.sfrac Bool.false 819841 1000) 11) hp752574

noncomputable def hp752576 := @Enclosure.Real.IsNear.mulLit_tf hp752401 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1))) 19856031 67108864 1

noncomputable def hp752577 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp752400 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752578 := @hp752577 1 1 0 1 19856031 67108864 1 67108864 19856031 67108864 1

noncomputable def hp752579 := @Enclosure.Real.IsNear.of_eq (hp752400 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752580 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 819841 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752581 := @hp752579 (@Inv.inv Real Real.instInv (Real.sqrt hp752402)) Bool.false 19856031 67108864 1 67108864 (hp752580 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 819841 1000) 819841 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000))))

noncomputable def hp752582 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp752402)) Bool.false 19856031 67108864 1 67108864 19856031 67108864

noncomputable def hp752583 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp752402) Bool.false 226812677 67108864 7 67108864 226812677 67108864 7 67108864

noncomputable def hp752584 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 819841 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752585 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 819841 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752586 := @hp752585 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 819841 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8756481507587

noncomputable def hp752587 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 819841 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 819841 1000 0

noncomputable def hp752588 := @hp752587 1 10680707 67108864 1 67108864 8756481507587 67108864000 819841 67108864000 (Enclosure.Real.IsNear.const Bool.false 819841 1000) hd4949

noncomputable def hp752589 := @hp752586 67108864000 819841 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 819841 1000) 819841 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000))) (hp752588 rfl)

noncomputable def hp752590 := @hp752584 8756481507587 67108864000 819841 67108864000 383287578 383287615 33554432 hp752589 rfl rfl rfl

noncomputable def hp752591 := @Enclosure.Real.IsNear.recentre' hp752402 Bool.false 766575193 67108864 37 67108864 766575193 67108864 37 67108864 (hp752590 rfl rfl rfl)

noncomputable def hp752592 := @Enclosure.Real.IsNear.sqrt_image hp752402 766575193 67108864 37 67108864 113406335 113406342 33554432 (hp752591 rfl) rfl rfl

noncomputable def hp752593 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp752402) 226812677 67108864 7 67108864 9928015 9928016 33554432 (hp752583 (hp752592 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp752594 := @hp752578 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp752581 (@hp752582 1 67108864 (hp752593 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp752595 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752596 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp752597 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1))) (hp752595 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752596 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp752598 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 819841 1000) 819841 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl

noncomputable def hp752599 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752600 := @hp752599 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752596 (Enclosure.sfrac Bool.false 1 16)))) 4740273

noncomputable def hp752601 := @hp752600 4194304 77 16777216 11672981 33554432 297543679 45675970560000 55333116663813 140737488355328 6865294077142001 766315624094760960000

noncomputable def hp752602 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752603 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752604 := @hp752602 (@Neg.neg Real Real.instNeg hp752603) Bool.true 4740273 4194304 77 16777216 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752605 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752606 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp752607 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp752608 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 89151139) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp752609 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1))) Bool.false 25093814854890273684395

noncomputable def hp752610 := nat_lit 998484790378392174223369667

noncomputable def hp752611 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp752612 := @Enclosure.Real.IsNear.subLit_ff_p hp752402 (Enclosure.sfrac Bool.false 11 1) 766575193 67108864 37 67108864 11 1 0

noncomputable def hp752613 := @hp752611 500000000000000 28377689 67108864 37 67108864 25093814854890273684395 9444732965739290427392 hp752610 hp738031 hd4948 (@hp752612 1 28377689 28377689 67108864 37 67108864 (hp752591 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752614 := @hp752608 89151139 33554432 117 33554432 Bool.true 59379487 67108864 1 10890000 (@hp752609 9444732965739290427392 hp752610 hp738031 89151139 33554432 117 33554432 (hp752613 rfl) rfl) (Enclosure.sfrac_false_div 89151139 33554432)

noncomputable def hp752615 := nat_lit 5252128216889092523163648

noncomputable def hp752616 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 89151139) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp752615) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp752617 := BSN.sin_reduce_arg_pos_rat_q1 89151139 33554432 226375608064910080 72057594037927936 0 hp752615 hp619237 rfl rfl rfl rfl

noncomputable def hp752618 := nat_lit 535997802193222617816642104805671328580089305638147268096262575446663502273631963374316911425

noncomputable def hp752619 := nat_lit 246538141956359317730431162079255367213850016093054604327804349172631987258468329888381761

noncomputable def hp752620 := nat_lit 1403404610657177512529165766895296589972363852835758851845109347699743958927760479160534530881

noncomputable def hp752621 := BSN.sin_dyadic_bound_f 149274462071 137438953472 3 2 67108864 21801270 hp752618 hp738039 hp752619 hp752620 hp738042

noncomputable def hp752622 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 149274462071) (BSN.sinEvenQ 137438953472) 0 2 hp752618 hp738039 hp752619 rfl rfl rfl

noncomputable def hp752623 := hp752621 hp752619 59379487 rfl rfl rfl rfl rfl rfl rfl rfl (hp752622 rfl)

noncomputable def hp752624 := @BSN.binarySplit_of_base2 (BSN.sinOddP 149274462071) (BSN.sinOddQ 137438953472) 0 2 hp752620 hp738042 hp752619 rfl rfl rfl

noncomputable def hp752625 := @BSN.sin_arg_round Bool.false 59379487 67108864 hp752615 hp619237 149274462071 137438953472 21801270 21780000 (hp752623 (hp752624 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752626 := hp752616 59379487 67108864 0 1000000000000000 21780000 10890000 hp752617 BSN.pi_near_15 hp752625 rfl rfl

noncomputable def hp752627 := @hp752606 59379487 67108864 81730277 22837985280000 (@hp752607 59379487 67108864 1307684432 365407764480000 59379487 67108864 81730277 22837985280000 (hp752614 (hp752626 rfl rfl) rfl rfl) rfl)

noncomputable def hp752628 := @hp752605 59379487 67108864 81730277 22837985280000 37922030 37922338 33554432 hp752627 rfl rfl rfl

noncomputable def hp752629 := @Enclosure.Real.IsNear.recentre' hp752603 Bool.false 75844368 67108864 308 67108864 4740273 4194304 77 16777216 (hp752628 rfl rfl rfl)

noncomputable def hp752630 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752596 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp752631 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752596 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 129258873)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp752632 := nat_lit 1220815547874585871396067896205

noncomputable def hp752633 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752596 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp752632

noncomputable def hp752634 := nat_lit 123676598634351277863383277203473093

noncomputable def hp752635 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752596 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp752636 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp752637 := @hp752636 (Enclosure.sfrac Bool.false 1 16) 1099101238754575 4503599627370496 4582978323 4503599627370496 1 16 0

noncomputable def hp752638 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)) 805293232980721

noncomputable def hp752639 := @hp752638 4503599627370496 2099950355 4503599627370496 28377689 67108864 37 67108864 73759435553812303052800 1099101238754575 4503599627370496 4582978323

noncomputable def hp752640 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)) 28377689 67108864 37

noncomputable def hp752641 := @hp752640 67108864 28377689 67108864 37 67108864 805293232980721 4503599627370496 2099950355 4503599627370496 (@hp752612 1 28377689 28377689 67108864 37 67108864 (hp752591 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752642 := hp752641 (@hp752612 1 28377689 28377689 67108864 37 67108864 (hp752591 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752643 := @hp752639 4503599627370496 (hp752642 rfl) (@hp752612 1 28377689 28377689 67108864 37 67108864 (hp752591 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752644 := @hp752635 500000000000000 1380576215465231 4503599627370496 4582978323 4503599627370496 hp752632 hp627574 hp752634 hp738055 hd4948 (@hp752637 1 22089219447443696 1380576215465231 4503599627370496 4582978323 4503599627370496 (hp752643 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp752645 := @hp752631 129258873 67108864 431 67108864 Bool.true 11672981 33554432 1 10890000 (@hp752633 hp627574 hp752634 hp738055 129258873 67108864 431 67108864 (hp752644 rfl) rfl) (Enclosure.sfrac_true_div 129258873 67108864)

noncomputable def hp752646 := nat_lit 2310754461928947333959498403670951990772335188145691016513244548176674381029741208101977802646847789601

noncomputable def hp752647 := nat_lit 21753261479411885450220162194564751194506429741603693074518606632946777792830299348896020655282721

noncomputable def hp752648 := nat_lit 13942525595052313101083530959035372025162057458228797522139726390308475627651890378594899241179155569185

noncomputable def hp752649 := BSN.cos_dyadic_bound_t 129258873 67108864 4 3 33554432 10890000 hp752646 hp745658 hp752647 hp752648 hp745661

noncomputable def hp752650 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 129258873) (BSN.cosEvenQ 67108864) 0 3 hp752646 hp745658 hp752647 rfl rfl rfl

noncomputable def hp752651 := hp752649 hp752647 11672981 rfl rfl rfl rfl rfl rfl rfl rfl (hp752650 rfl)

noncomputable def hp752652 := @BSN.binarySplit_of_base3 (BSN.cosOddP 129258873) (BSN.cosOddQ 67108864) 0 3 hp752648 hp745661 hp752647 rfl rfl rfl

noncomputable def hp752653 := hp752645 (BSN.cos_neg_of_bound 129258873 67108864 Bool.true 11672981 33554432 1 10890000 (hp752651 (hp752652 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp752654 := hp752601 (hp752604 (@Enclosure.Real.IsNear.neg hp752603 Bool.false 4740273 4194304 77 16777216 (hp752629 rfl))) (@hp752630 11672981 33554432 4760698864 730815528960000 11672981 33554432 297543679 45675970560000 (hp752653 rfl) rfl)

noncomputable def hp752655 := @hp752576 67108864 55333116663813 140737488355328 6865294077142001 766315624094760960000 1098696079803287506203 9444732965739290427392 17077348463172062773129 hp752398 (hp752594 rfl) (@hp752597 Bool.false 55333116663813 140737488355328 6865294077142001 766315624094760960000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752402 (Enclosure.sfrac Bool.false 11 1)) (hp752598 rfl (hp752405 rfl rfl))) (hp752654 rfl))

noncomputable def hp752656 := @hp752399 hp752396 hp752398 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 819841 1000))) (@hp752404 hp752396 hp752398 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 819841 1000) 11 (hp752405 rfl rfl)) (@hp752408 hp752396 hp752398 hp752575 (hp752655 rfl) rfl rfl))

theorem hd5020 : hp752397 hp752398 := hp752656

noncomputable def hp752657 := nat_lit 9578311737997894812847643

noncomputable def hp752658 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821372 1000)) Bool.false 152880999490992134501 295147905179352825856 hp752657

noncomputable def hp752659 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821372 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821372 1000)) Bool.false 152880999490992134501 295147905179352825856

noncomputable def hp752660 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 821372 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752661 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp752660 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752662 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 821372 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752663 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp752661 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp752664 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821372 1000)) hp752663 Bool.false 152880999490992134501 295147905179352825856

noncomputable def hp752665 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 821372 1000) 821372 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl

noncomputable def hp752666 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp752661 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp752667 := nat_lit 41038680812100241517189267456

noncomputable def hp752668 := @hp752666 108047441 268435456 99655 134217728 34081581760050813285 295147905179352825856 32413798102469379247643 hp742094 hp752667 152880999490992134501 295147905179352825856

noncomputable def hp752669 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) 11)

noncomputable def hp752670 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) 11) hp752669

noncomputable def hp752671 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) 11)

noncomputable def hp752672 := @hp752671 108047441 536870912 199310 536870912 108047441 536870912 199310 536870912 116015056377872384 108047441 268435456

noncomputable def hp752673 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp752674 := hp752673 BSN.quadSignNeg 9 10 11 821372 1000 191 241 536870912 268435456 9007199254740992

noncomputable def hp752675 := hp752674 Bool.false 853750851616 3743 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp752676 := hp752675 Bool.false 75573779 171101 Bool.true 548648697 Bool.true 411906581 28296951008113761 1 Bool.false 458015644

noncomputable def hp752677 := hp752676 Bool.false Bool.false 372667939 Bool.true Bool.false 108047441 199310 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 458015644 536870912) BSN.abs_quadSignNeg

noncomputable def hp752678 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp752679 := hp752678 BSN.quadSignPos 7 8 9 821372 1000 74 136 536870912 268435456 9007199254740992

noncomputable def hp752680 := hp752679 Bool.false 853750851616 3743 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp752681 := hp752680 Bool.true 29661425 139737 Bool.true 816712700 Bool.true 470052056 28296951008113761 1 Bool.false 26591272

noncomputable def hp752682 := hp752681 Bool.true Bool.false 343909923 Bool.false Bool.false 75573779 171101 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 26591272 536870912) BSN.abs_quadSignPos

noncomputable def hp752683 := hp752673 BSN.quadSignNeg 5 6 7 821372 1000 75 5 536870912 268435456 9007199254740992

noncomputable def hp752684 := hp752683 Bool.false 853750851616 3743 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp752685 := hp752684 Bool.true 129147210 103840 Bool.false 388753788 Bool.true 121989607 28296951008113761 1 Bool.false 355660488

noncomputable def hp752686 := hp752685 Bool.false Bool.false 120942583 Bool.true Bool.true 29661425 139737 BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 355660488 536870912) BSN.abs_quadSignNeg

noncomputable def hp752687 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp752688 := hp752687 BSN.quadSignNeg 3 4 5 821372 1000 287 170 536870912 268435456 9007199254740992

noncomputable def hp752689 := hp752688 Bool.false 853750851616 3743 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp752690 := hp752689 Bool.true 237524155 61374 Bool.false 404256276 Bool.false 672320278 28296951008113761 1 Bool.false 367123354

noncomputable def hp752691 := hp752690 Bool.false Bool.false 168118154 Bool.true Bool.true 129147210 103840 BSN.abs_quadSignPos (BSN.cos_quad_nat3 287 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 367123354 536870912) BSN.abs_quadSignNeg

noncomputable def hp752692 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp752693 := hp752692 BSN.quadSignNeg 1 2 3 821372 1000 649 437 536870912 268435456 9007199254740992

noncomputable def hp752694 := hp752693 Bool.false 853750851616 3743 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp752695 := hp752694 Bool.false 446406440 3794 Bool.false 781900539 Bool.false 766395588 28296951008113761 1 Bool.false 533362054

noncomputable def hp752696 := hp752695 Bool.true Bool.false 531370092 Bool.true Bool.true 237524155 61374 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 649 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533362054 536870912) BSN.abs_quadSignNeg

noncomputable def hp752697 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) 1) Bool.false

noncomputable def hp752698 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)))

noncomputable def hp752699 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000))) Bool.false 55800805 67108864

noncomputable def hp752700 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 26679714113) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false 26679714113 16777216

noncomputable def hp752701 := nat_lit 120804598686406815576765716616089650176721648092381833

noncomputable def hp752702 := nat_lit 75966512885745932822077553331053253100650784358400

noncomputable def hp752703 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) Bool.false hp752701 hp752702 31088864775322605689

noncomputable def hp752704 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821372 4000) (Real.log (Enclosure.sfrac Bool.false 2698608849536 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1642744))))))

noncomputable def hp752705 := nat_lit 179449029922658332954892567183360000

noncomputable def hp752706 := nat_lit 884366604566410333175183661876400619520

noncomputable def hp752707 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp752704 (Enclosure.sfrac Bool.false 821372 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821372 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp752705 hp752706)) Bool.false

noncomputable def hp752708 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 821372 1000) 821372 1000 2698608849536 16000000 1642744

noncomputable def hp752709 := hp752708 4000 2000 hp752705 hp752706 (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl rfl rfl rfl

noncomputable def hp752710 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp752704 (Enclosure.sfrac Bool.false 821372 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821372 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp752705 hp752706) 1432356427543245976629 900719925474099200

noncomputable def hp752711 := nat_lit 1266728028721977130502226880664328210237060788701173729198080

noncomputable def hp752712 := @hp752710 31088864775322605689 hp739140 hp752705 hp752706 0 1 hp752711 hp752701 hp752702 31088864775322605689 hp739140

noncomputable def hp752713 := @Enclosure.Real.IsNear.subLit_ff_p (hp752704 (Enclosure.sfrac Bool.false 821372 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821372 2000) (Real.log Real.pi)) 9279034825185852474633 4503599627370496000 647947825412771 272250000000000000000

noncomputable def hp752714 := nat_lit 120154765869406935455178424320000

noncomputable def hp752715 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821372 4000) (Real.log (Enclosure.sfrac Bool.false 2698608849536 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1642744))))))

noncomputable def hp752716 := @hp752715 (Enclosure.sfrac Bool.false 821372 2000) 11128600141752131994889 4503599627370496000 647947825412771 272250000000000000000 821372 2000 0

noncomputable def hp752717 := nat_lit 18558069650371704949266000

noncomputable def hp752718 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821372 4000) (Real.log (Enclosure.sfrac Bool.false 2698608849536 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1642744))))) 11130368015840865504889

noncomputable def hp752719 := nat_lit 25059379725775075308377732100990697472

noncomputable def hp752720 := @hp752718 4503599627370496000 2566791301514959 1089000000000000000000 883937044366755 2251799813685248 200000001089 8712000000000000000 hp752719 11128600141752131994889 4503599627370496000 647947825412771

noncomputable def hp752721 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 821372 4000) (Real.log (Enclosure.sfrac Bool.false 2698608849536 16000000)) 821372 4000 0 1 54203785937874023 4503599627370496

noncomputable def hp752722 := nat_lit 116401743961276808276475904

noncomputable def hp752723 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2698608849536) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp752722 hp617687

noncomputable def hp752724 := BSN.log_rat_reduce_isNear 2698608849536 16000000 17 5397217699072 4194304000000 67687655 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp752725 := nat_lit 264418570096213771539408417483971224963948178095990539142264205069694959339052825978604276807003715665920

noncomputable def hp752726 := nat_lit 1399555442659853276333948425075130459986198818172078956258271228065094790006306158725345009165888651264

noncomputable def hp752727 := nat_lit 1798146615300841582723409057676501729006672882584282316975603998699397570327415899417756963962880

noncomputable def hp752728 := BSN.log_dyadic_bound 601456849536 4795760849536 5 4 hp752725 268435456 87120000 hp752726 hp752727 67687655 5397217699072

noncomputable def hp752729 := hp752728 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp752730 := @BSN.binarySplit_of_base4 (BSN.artanhP 601456849536) (BSN.artanhQ 4795760849536) 0 4 hp752726 hp752725 hp752727 rfl rfl rfl

noncomputable def hp752731 := hp752724 rfl rfl rfl rfl (hp752729 (hp752730 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp752732 := @hp752721 12500018513 1089000000000000000 11130368015840865504889 4503599627370496000 2566791301514959 1089000000000000000000 (Enclosure.Real.IsNear.const Bool.false 821372 4000) (BSN.isNear_log_sfrac 2698608849536 16000000 54203785937874023 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp752723 1000001481040000 87120000000000000000000 54203785937874023 4503599627370496 12500018513 1089000000000000000 (hp752731 rfl rfl rfl) rfl)) rfl

noncomputable def hp752733 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1642744)))) 1 4

noncomputable def hp752734 := @hp752733 0 1 883937044366755 562949953421312 200000001089 2178000000000000000 883937044366755 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp752735 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1642744))) 884279719003555 562949953421312 1

noncomputable def hp752736 := @hp752735 2000000000000000 20425 33554432 1 10890000 29660005447485263708160 883937044366755 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp752737 := BSN.arctan_dyadic_bound_f 1000 1642744 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp752738 := hp752737 1 20425 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1642744) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1642744) 0 0 rfl)

noncomputable def hp752739 := hp752734 (hp752736 (hp752738 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp752740 := @hp752713 7887380896023 16777216000 616029 134217728000 hp752714 1432356427543245976629 900719925474099200 31088864775322605689 hp739140 (@hp752716 1 hp752717 9279034825185852474633 4503599627370496000 647947825412771 272250000000000000000 (@hp752720 272250000000000000000 hp752732 hp752739 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 821372 2000) rfl rfl)

noncomputable def hp752741 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 821372 2000) (Real.log Real.pi) 821372 2000 0 1 38410761 33554432

noncomputable def hp752742 := hp752740 (@hp752741 3 268435456 7887380896023 16777216000 616029 134217728000 (Enclosure.Real.IsNear.const Bool.false 821372 2000) hd4909 rfl) rfl

noncomputable def hp752743 := @hp752703 hp739140 26679714113 16777216 117 16777216 (@hp752707 hp752701 hp752702 31088864775322605689 hp739140 (hp752709 rfl rfl rfl rfl rfl) (hp752712 (hp752742 rfl) (Enclosure.Real.IsNear.const Bool.true hp752705 hp752706) rfl rfl)) rfl

noncomputable def hp752744 := nat_lit 1424113885086728822194176

noncomputable def hp752745 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 26679714113) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp752744) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp752746 := BSN.sin_reduce_arg_pos_rat_q0 26679714113 16777216 226375608064910080 72057594037927936 253 hp752744 hp619230 rfl rfl rfl rfl

noncomputable def hp752747 := nat_lit 25744199830497599622944203982531807990469029291323188574863221478026954681373615538400390625

noncomputable def hp752748 := nat_lit 1844162950942441037965541951459441877748879395330657678947728882687417770239410400390625

noncomputable def hp752749 := nat_lit 77228911165590913986756680863692505087651590115178904409231768976315489208580367794400390625

noncomputable def hp752750 := BSN.cos_dyadic_bound_f 80951502075 137438953472 3 2 67108864 21801270 hp752747 hp746621 hp752748 hp752749 hp746624

noncomputable def hp752751 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 80951502075) (BSN.cosEvenQ 137438953472) 0 2 hp752747 hp746621 hp752748 rfl rfl rfl

noncomputable def hp752752 := hp752750 hp752748 55800805 rfl rfl rfl rfl rfl rfl rfl rfl (hp752751 rfl)

noncomputable def hp752753 := @BSN.binarySplit_of_base2 (BSN.cosOddP 80951502075) (BSN.cosOddQ 137438953472) 0 2 hp752749 hp746624 hp752748 rfl rfl rfl

noncomputable def hp752754 := @BSN.cos_arg_round Bool.false 55800805 67108864 hp752744 hp619230 80951502075 137438953472 21801270 21780000 (hp752752 (hp752753 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752755 := hp752745 55800805 67108864 253 1000000000000000 21780000 10890000 hp752746 BSN.pi_near_15 hp752754 rfl rfl

noncomputable def hp752756 := @hp752700 117 16777216 Bool.false 55800805 67108864 1 10890000 hp752743 (Enclosure.sfrac_false_div 26679714113 16777216) (hp752755 rfl rfl) rfl

noncomputable def hp752757 := @hp752697 55800805 67108864 80681701 11418992640000 446406440 536870912 3794 536870912 (@hp752698 Bool.false 55800805 67108864 80681701 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000)) (@hp752699 1290907216 182703882240000 55800805 67108864 80681701 11418992640000 (hp752756 rfl) rfl))

noncomputable def hp752758 := @hp752703 hp739140 853750851616 536870912 3743 536870912 (@hp752707 hp752701 hp752702 31088864775322605689 hp739140 (hp752709 rfl rfl rfl rfl rfl) (hp752712 (hp752742 rfl) (Enclosure.Real.IsNear.const Bool.true hp752705 hp752706) rfl rfl)) rfl

noncomputable def hp752759 := hp752696 (BSN.cos_quad_nat1 437 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 531370092 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl rfl (hp752757 rfl) hp752758

noncomputable def hp752760 := nat_lit 134063312836616778717119703304722742200401334750735062678908980778582300029627647550389576980402977973839088227921

noncomputable def hp752761 := nat_lit 52217749452443733904751519415296610103483903659570334519630671128236712705407293122915380699149467876759121

noncomputable def hp752762 := nat_lit 669700760271327709598330993962723254607130161694270987875414176405525694410777778456350834974326462276263297062481

noncomputable def hp752763 := BSN.sin_dyadic_bound_f 781900539 536870912 4 3 536870912 268435456 hp752760 hp642702 hp752761 hp752762 hp642705

noncomputable def hp752764 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 781900539) (BSN.sinEvenQ 536870912) 0 3 hp752760 hp642702 hp752761 rfl rfl rfl

noncomputable def hp752765 := hp752763 hp752761 533362054 rfl rfl rfl rfl rfl rfl rfl rfl (hp752764 rfl)

noncomputable def hp752766 := @BSN.binarySplit_of_base3 (BSN.sinOddP 781900539) (BSN.sinOddQ 536870912) 0 3 hp752762 hp642705 hp752761 rfl rfl rfl

noncomputable def hp752767 := nat_lit 123727483386584479228086027619960177741076116161540865918298433234721686827594662942170315637504916332754717638656

noncomputable def hp752768 := nat_lit 41061607853500758499430855570322640400855508566520572443045677364350712797795345971018587694782259612614656

noncomputable def hp752769 := nat_lit 618112799196472333418340105915936127487896860217107523132630425649608453372971800903926320642393378412920272060416

noncomputable def hp752770 := BSN.sin_dyadic_bound_f 766395588 536870912 4 3 536870912 268435456 hp752767 hp642702 hp752768 hp752769 hp642705

noncomputable def hp752771 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 766395588) (BSN.sinEvenQ 536870912) 0 3 hp752767 hp642702 hp752768 rfl rfl rfl

noncomputable def hp752772 := hp752770 hp752768 531370092 rfl rfl rfl rfl rfl rfl rfl rfl (hp752771 rfl)

noncomputable def hp752773 := @BSN.binarySplit_of_base3 (BSN.sinOddP 766395588) (BSN.sinOddQ 536870912) 0 3 hp752769 hp642705 hp752768 rfl rfl rfl

noncomputable def hp752774 := hp752759 hd4911 hd4913 hd4915 hd4917 hd4918 (hp752765 (hp752766 rfl) rfl rfl rfl rfl) (hp752772 (hp752773 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752775 := hp752691 (BSN.cos_quad_nat2 170 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 168118154 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl rfl (hp752774 rfl rfl rfl rfl rfl) hp752758

noncomputable def hp752776 := nat_lit 6710185623989484953954981438710959848112078828549726115342209528369315840

noncomputable def hp752777 := nat_lit 713270344375707789981352248165127669818323840876285868726026019864576

noncomputable def hp752778 := nat_lit 17573140863224423733460219673936437014542405359983102029727849484554141696

noncomputable def hp752779 := BSN.sin_dyadic_bound_f 404256276 536870912 3 2 536870912 268435456 hp752776 hp708845 hp752777 hp752778 hp708848

noncomputable def hp752780 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 404256276) (BSN.sinEvenQ 536870912) 0 2 hp752776 hp708845 hp752777 rfl rfl rfl

noncomputable def hp752781 := hp752779 hp752777 367123354 rfl rfl rfl rfl rfl rfl rfl rfl (hp752780 rfl)

noncomputable def hp752782 := @BSN.binarySplit_of_base2 (BSN.sinOddP 404256276) (BSN.sinOddQ 536870912) 0 2 hp752778 hp708848 hp752777 rfl rfl rfl

noncomputable def hp752783 := nat_lit 28185451403876966828768470493364338833073501976909314805850550790240619747739006482421949204081711661146886967296

noncomputable def hp752784 := nat_lit 8529322262932896629916674579848837650883132429436379924256273020400892993069661768829579014130576965308416

noncomputable def hp752785 := nat_lit 170825060965987683591439271837134505858668716125958978910467900057084489669444252718737261265555576519663037255680

noncomputable def hp752786 := BSN.cos_dyadic_bound_f 672320278 536870912 4 3 536870912 268435456 hp752783 hp716712 hp752784 hp752785 hp716714

noncomputable def hp752787 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 672320278) (BSN.cosEvenQ 536870912) 0 3 hp752783 hp716712 hp752784 rfl rfl rfl

noncomputable def hp752788 := hp752786 hp752784 168118154 rfl rfl rfl rfl rfl rfl rfl rfl (hp752787 rfl)

noncomputable def hp752789 := @BSN.binarySplit_of_base3 (BSN.cosOddP 672320278) (BSN.cosOddQ 536870912) 0 3 hp752785 hp716714 hp752784 rfl rfl rfl

noncomputable def hp752790 := hp752775 hd4920 hd4922 hd4924 hd4926 hd4918 (hp752781 (hp752782 rfl) rfl rfl rfl rfl) (hp752788 (hp752789 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752791 := hp752686 (BSN.cos_quad_nat1 5 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 120942583 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl rfl (hp752790 rfl rfl rfl rfl rfl) hp752758

noncomputable def hp752792 := nat_lit 5738512094561624631956365991486302193196463121293513007329686056509440000

noncomputable def hp752793 := nat_lit 521671451300704994483187835801138465236043196123774700276365089898496

noncomputable def hp752794 := nat_lit 15028591827216434799418461959301399138951783152498809860158254128331554816

noncomputable def hp752795 := BSN.sin_dyadic_bound_f 388753788 536870912 3 2 536870912 268435456 hp752792 hp708845 hp752793 hp752794 hp708848

noncomputable def hp752796 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 388753788) (BSN.sinEvenQ 536870912) 0 2 hp752792 hp708845 hp752793 rfl rfl rfl

noncomputable def hp752797 := hp752795 hp752793 355660488 rfl rfl rfl rfl rfl rfl rfl rfl (hp752796 rfl)

noncomputable def hp752798 := @BSN.binarySplit_of_base2 (BSN.sinOddP 388753788) (BSN.sinOddQ 536870912) 0 2 hp752794 hp708848 hp752793 rfl rfl rfl

noncomputable def hp752799 := nat_lit 221457977212518539208914176773601

noncomputable def hp752800 := BSN.sin_dyadic_bound_f 121989607 536870912 2 1 536870912 268435456 hp752799 hp708890 hp752799 hp752799 hp708891

noncomputable def hp752801 := @BSN.binarySplit_of_base (BSN.sinEvenP 121989607) (BSN.sinEvenQ 536870912) 0 1 hp752799 hp708890 hp752799 rfl rfl rfl

noncomputable def hp752802 := hp752800 hp752799 120942583 rfl rfl rfl rfl rfl rfl rfl rfl (hp752801 rfl)

noncomputable def hp752803 := @BSN.binarySplit_of_base (BSN.sinOddP 121989607) (BSN.sinOddQ 536870912) 0 1 hp752799 hp708891 hp752799 rfl rfl rfl

noncomputable def hp752804 := hp752791 hd4928 hd4930 hd4932 hd4934 hd4918 (hp752797 (hp752798 rfl) rfl rfl rfl rfl) (hp752802 (hp752803 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752805 := hp752682 (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 343909923 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl rfl (hp752804 rfl rfl rfl rfl rfl) hp752758

noncomputable def hp752806 := nat_lit 61481550035354323854175456887274341343588053803883850252286500273167707438379650986656170126426957578240000000000

noncomputable def hp752807 := nat_lit 88070752643041679394918316283147806217172887450361289296039174464988899341229658721000000000000000000000000

noncomputable def hp752808 := nat_lit 372197474463654310023351699238513854854326006879602062878188598786385990938788043182483326093553195974656000000000

noncomputable def hp752809 := BSN.cos_dyadic_bound_f 816712700 536870912 4 3 536870912 268435456 hp752806 hp716712 hp752807 hp752808 hp716714

noncomputable def hp752810 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 816712700) (BSN.cosEvenQ 536870912) 0 3 hp752806 hp716712 hp752807 rfl rfl rfl

noncomputable def hp752811 := hp752809 hp752807 26591272 rfl rfl rfl rfl rfl rfl rfl rfl (hp752810 rfl)

noncomputable def hp752812 := @BSN.binarySplit_of_base3 (BSN.cosOddP 816712700) (BSN.cosOddQ 536870912) 0 3 hp752808 hp716714 hp752807 rfl rfl rfl

noncomputable def hp752813 := nat_lit 6815920028899119040980668249149820262063927969809842544551141315597828096

noncomputable def hp752814 := nat_lit 2383239306084687955779610588056377935060270909790733024008090750550016

noncomputable def hp752815 := nat_lit 20442993608085187747030445526273348030321663367609946167605407765292384256

noncomputable def hp752816 := BSN.cos_dyadic_bound_f 470052056 536870912 3 2 536870912 268435456 hp752813 hp708868 hp752814 hp752815 hp708870

noncomputable def hp752817 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 470052056) (BSN.cosEvenQ 536870912) 0 2 hp752813 hp708868 hp752814 rfl rfl rfl

noncomputable def hp752818 := hp752816 hp752814 343909923 rfl rfl rfl rfl rfl rfl rfl rfl (hp752817 rfl)

noncomputable def hp752819 := @BSN.binarySplit_of_base2 (BSN.cosOddP 470052056) (BSN.cosOddQ 536870912) 0 2 hp752815 hp708870 hp752814 rfl rfl rfl

noncomputable def hp752820 := hp752805 hd4936 hd4938 hd4940 hd4942 hd4918 (hp752811 (hp752812 rfl) rfl rfl rfl rfl) (hp752818 (hp752819 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752821 := hp752677 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 372667939 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl rfl (hp752820 rfl rfl rfl rfl rfl) hp752758

noncomputable def hp752822 := nat_lit 22771692114331269714293776823869413083150890973095039419506075776676490945

noncomputable def hp752823 := nat_lit 8210220423155033180392725723081222424260738237696913096435891234631361

noncomputable def hp752824 := nat_lit 59626853275896788721810684411344426571946387543816451096550254638820454081

noncomputable def hp752825 := BSN.sin_dyadic_bound_f 548648697 536870912 3 2 536870912 268435456 hp752822 hp708845 hp752823 hp752824 hp708848

noncomputable def hp752826 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 548648697) (BSN.sinEvenQ 536870912) 0 2 hp752822 hp708845 hp752823 rfl rfl rfl

noncomputable def hp752827 := hp752825 hp752823 458015644 rfl rfl rfl rfl rfl rfl rfl rfl (hp752826 rfl)

noncomputable def hp752828 := @BSN.binarySplit_of_base2 (BSN.sinOddP 548648697) (BSN.sinOddQ 536870912) 0 2 hp752824 hp708848 hp752823 rfl rfl rfl

noncomputable def hp752829 := nat_lit 7232791870737851505662310124886633867775891594498505095889648506408818785

noncomputable def hp752830 := nat_lit 828685701898299709974680042036267372932827563161174966857205957023841

noncomputable def hp752831 := nat_lit 18941684646510347172442281797492172839856872455250966682145596326187915361

noncomputable def hp752832 := BSN.sin_dyadic_bound_f 411906581 536870912 3 2 536870912 268435456 hp752829 hp708845 hp752830 hp752831 hp708848

noncomputable def hp752833 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 411906581) (BSN.sinEvenQ 536870912) 0 2 hp752829 hp708845 hp752830 rfl rfl rfl

noncomputable def hp752834 := hp752832 hp752830 372667939 rfl rfl rfl rfl rfl rfl rfl rfl (hp752833 rfl)

noncomputable def hp752835 := @BSN.binarySplit_of_base2 (BSN.sinOddP 411906581) (BSN.sinOddQ 536870912) 0 2 hp752831 hp708848 hp752830 rfl rfl rfl

noncomputable def hp752836 := hp752821 hd4944 hd4946 hd4961 hd4963 hd4918 (hp752827 (hp752828 rfl) rfl rfl rfl rfl) (hp752834 (hp752835 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752837 := @hp752672 99655 134217728 (hp752836 rfl rfl rfl rfl rfl) (hp752836 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp752838 := @hp752670 Bool.false 108047441 268435456 99655 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821372 1000)) (Enclosure.sfrac Bool.false 821372 1000) 11) hp752837

noncomputable def hp752839 := @Enclosure.Real.IsNear.mulLit_tf hp752661 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1))) 4961693 16777216 1

noncomputable def hp752840 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp752660 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752841 := @hp752840 1 1 0 1 4961693 16777216 1 33554432 4961693 16777216 1

noncomputable def hp752842 := @Enclosure.Real.IsNear.of_eq (hp752660 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752843 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 821372 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752844 := @hp752842 (@Inv.inv Real Real.instInv (Real.sqrt hp752662)) Bool.false 4961693 16777216 1 33554432 (hp752843 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 821372 1000) 821372 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000))))

noncomputable def hp752845 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp752662)) Bool.false 19846772 67108864 2 67108864 4961693 16777216

noncomputable def hp752846 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp752662) Bool.false 226918492 67108864 6 67108864 56729623 16777216 3 33554432

noncomputable def hp752847 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 821372 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752848 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 821372 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752849 := @hp752848 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821372 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2193208417501

noncomputable def hp752850 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 821372 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 821372 1000 0

noncomputable def hp752851 := @hp752850 1 10680707 67108864 1 67108864 2193208417501 16777216000 205343 16777216000 (Enclosure.Real.IsNear.const Bool.false 821372 1000) hd4949

noncomputable def hp752852 := @hp752849 16777216000 205343 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 821372 1000) 821372 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000))) (hp752851 rfl)

noncomputable def hp752853 := @hp752847 2193208417501 16777216000 205343 16777216000 383645294 383645330 33554432 hp752852 rfl rfl rfl

noncomputable def hp752854 := @Enclosure.Real.IsNear.recentre' hp752662 Bool.false 767290624 67108864 36 67108864 2997229 262144 9 16777216 (hp752853 rfl rfl rfl)

noncomputable def hp752855 := @Enclosure.Real.IsNear.sqrt_image hp752662 2997229 262144 9 16777216 113459243 113459249 33554432 (hp752854 rfl) rfl rfl

noncomputable def hp752856 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp752662) 56729623 16777216 3 33554432 9923385 9923387 33554432 (hp752846 (hp752855 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp752857 := @hp752841 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp752844 (@hp752845 1 33554432 (hp752856 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp752858 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752859 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp752860 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1))) (hp752858 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752859 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp752861 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 821372 1000) 821372 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl

noncomputable def hp752862 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752863 := @hp752862 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752859 (Enclosure.sfrac Bool.false 1 16)))) 1147207

noncomputable def hp752864 := @hp752863 1048576 35 8388608 5987535 16777216 292098679 45675970560000 6868942064745 17592186044416 3251328658682689 383157812047380480000

noncomputable def hp752865 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752866 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752867 := @hp752865 (@Neg.neg Real Real.instNeg hp752866) Bool.true 1147207 1048576 35 8388608 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752868 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp752869 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp752870 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp752871 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 22849683) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false

noncomputable def hp752872 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1))) Bool.false 100493968666159007975

noncomputable def hp752873 := nat_lit 242874678743873408565822463

noncomputable def hp752874 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp752875 := @Enclosure.Real.IsNear.subLit_ff_p hp752662 (Enclosure.sfrac Bool.false 11 1) 2997229 262144 9 16777216 11 1 0

noncomputable def hp752876 := @hp752874 500000000000000 113645 262144 9 16777216 100493968666159007975 36893488147419103232 hp752873 hp631123 hd4948 (@hp752875 1 113645 113645 262144 9 16777216 (hp752854 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752877 := @hp752871 22849683 8388608 227 67108864 Bool.true 61339186 67108864 1 10890000 (@hp752872 36893488147419103232 hp752873 hp631123 22849683 8388608 227 67108864 (hp752876 rfl) rfl) (Enclosure.sfrac_false_div 22849683 8388608)

noncomputable def hp752878 := nat_lit 1394010126200517412519936

noncomputable def hp752879 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 22849683) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp752878) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp752880 := BSN.sin_reduce_arg_pos_rat_q1 22849683 8388608 226375608064910080 72057594037927936 0 hp752878 hp630689 rfl rfl rfl rfl

noncomputable def hp752881 := nat_lit 681050684351060372788846882001156475150625352459916146817445821311171241880866067574701095745

noncomputable def hp752882 := nat_lit 397932050481496980108432007798033412323515571430502007853095508787764902772322841207176001

noncomputable def hp752883 := nat_lit 1783059902361521409812518658180879666536447374088892905080595948800744490321589273333691251521

noncomputable def hp752884 := BSN.sin_dyadic_bound_f 158480602999 137438953472 3 2 67108864 21801270 hp752881 hp738039 hp752882 hp752883 hp738042

noncomputable def hp752885 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 158480602999) (BSN.sinEvenQ 137438953472) 0 2 hp752881 hp738039 hp752882 rfl rfl rfl

noncomputable def hp752886 := hp752884 hp752882 61339186 rfl rfl rfl rfl rfl rfl rfl rfl (hp752885 rfl)

noncomputable def hp752887 := @BSN.binarySplit_of_base2 (BSN.sinOddP 158480602999) (BSN.sinOddQ 137438953472) 0 2 hp752883 hp738042 hp752882 rfl rfl rfl

noncomputable def hp752888 := @BSN.sin_arg_round Bool.false 61339186 67108864 hp752878 hp630689 158480602999 137438953472 21801270 21780000 (hp752886 (hp752887 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp752889 := hp752879 61339186 67108864 0 1000000000000000 21780000 10890000 hp752880 BSN.pi_near_15 hp752888 rfl rfl

noncomputable def hp752890 := @hp752869 30669593 33554432 158696179 45675970560000 (@hp752870 61339186 67108864 2539138864 730815528960000 30669593 33554432 158696179 45675970560000 (hp752877 (hp752889 rfl rfl) rfl rfl) rfl)

noncomputable def hp752891 := @hp752868 30669593 33554432 158696179 45675970560000 36710484 36710764 33554432 hp752890 rfl rfl rfl

noncomputable def hp752892 := @Enclosure.Real.IsNear.recentre' hp752866 Bool.false 73421248 67108864 280 67108864 1147207 1048576 35 8388608 (hp752891 rfl rfl rfl)

noncomputable def hp752893 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752859 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp752894 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752859 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 8119029)) (@Nat.cast Real Real.instNatCast 4194304)) Bool.true

noncomputable def hp752895 := nat_lit 18721206326592284958016805

noncomputable def hp752896 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752859 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp752895

noncomputable def hp752897 := nat_lit 7607754217705037750191565287386487

noncomputable def hp752898 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp752859 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp752899 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp752900 := @hp752899 (Enclosure.sfrac Bool.false 1 16) 16876168855 68719476736 281914065 281474976710656 1 16 0

noncomputable def hp752901 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)) 12915186025

noncomputable def hp752902 := @hp752901 68719476736 130919121 281474976710656 113645 262144 9 16777216 4423986408325120 16876168855 68719476736 281914065

noncomputable def hp752903 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)) 113645 262144 9

noncomputable def hp752904 := @hp752903 16777216 113645 262144 9 16777216 12915186025 68719476736 130919121 281474976710656 (@hp752875 1 113645 113645 262144 9 16777216 (hp752854 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752905 := hp752904 (@hp752875 1 113645 113645 262144 9 16777216 (hp752854 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752906 := @hp752902 281474976710656 (hp752905 rfl) (@hp752875 1 113645 113645 262144 9 16777216 (hp752854 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp752907 := @hp752898 500000000000000 21171136151 68719476736 281914065 281474976710656 hp752895 hp617687 hp752897 hp631148 hd4948 (@hp752900 1 338738178416 21171136151 68719476736 281914065 281474976710656 (hp752906 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp752908 := @hp752894 8119029 4194304 423 67108864 Bool.true 11975070 33554432 1 10890000 (@hp752896 hp617687 hp752897 hp631148 8119029 4194304 423 67108864 (hp752907 rfl) rfl) (Enclosure.sfrac_true_div 8119029 4194304)

noncomputable def hp752909 := nat_lit 8376065074489951143258486349354354187044391166660589090141098867233993593366598268709521

noncomputable def hp752910 := nat_lit 82044431818610263189273351566680417107945488614129950639771106270970996714539281041

noncomputable def hp752911 := nat_lit 50533611050744093396957790357962848094764916422292612949593347064423771215603519772387985

noncomputable def hp752912 := BSN.cos_dyadic_bound_t 8119029 4194304 4 3 33554432 10890000 hp752909 hp633286 hp752910 hp752911 hp633289

noncomputable def hp752913 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 8119029) (BSN.cosEvenQ 4194304) 0 3 hp752909 hp633286 hp752910 rfl rfl rfl

noncomputable def hp752914 := hp752912 hp752910 11975070 rfl rfl rfl rfl rfl rfl rfl rfl (hp752913 rfl)

noncomputable def hp752915 := @BSN.binarySplit_of_base3 (BSN.cosOddP 8119029) (BSN.cosOddQ 4194304) 0 3 hp752911 hp633289 hp752910 rfl rfl rfl

noncomputable def hp752916 := hp752908 (BSN.cos_neg_of_bound 8119029 4194304 Bool.true 11975070 33554432 1 10890000 (hp752914 (hp752915 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp752917 := hp752864 (hp752867 (@Enclosure.Real.IsNear.neg hp752866 Bool.false 1147207 1048576 35 8388608 (hp752892 rfl))) (@hp752893 11975070 33554432 4673578864 730815528960000 5987535 16777216 292098679 45675970560000 (hp752916 rfl) rfl)

noncomputable def hp752918 := @hp752839 33554432 6868942064745 17592186044416 3251328658682689 383157812047380480000 34081581760050813285 295147905179352825856 32413798102469379247643 hp742094 (hp752857 rfl) (@hp752860 Bool.false 6868942064745 17592186044416 3251328658682689 383157812047380480000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752662 (Enclosure.sfrac Bool.false 11 1)) (hp752861 rfl (hp752665 rfl rfl))) (hp752917 rfl))

noncomputable def hp752919 := @hp752659 hp752657 hp742094 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821372 1000))) (@hp752664 hp752657 hp742094 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 821372 1000) 11 (hp752665 rfl rfl)) (@hp752668 hp752657 hp742094 hp752838 (hp752918 rfl) rfl rfl))

theorem hd5021 : hp752658 hp742094 := hp752919

noncomputable def hp752920 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821936 1000)) Bool.true 8332312934964312657227 37778931862957161709568 85207062108651627797619

noncomputable def hp752921 := nat_lit 114281268885445414171443200

noncomputable def hp752922 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821936 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821936 1000)) Bool.true 8332312934964312657227 37778931862957161709568

noncomputable def hp752923 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 821936 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752924 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp752923 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp752925 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 821936 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp752926 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp752924 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp752927 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821936 1000)) hp752926 Bool.true 8332312934964312657227 37778931862957161709568

noncomputable def hp752928 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 821936 1000) 821936 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl

noncomputable def hp752929 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp752924 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp752930 := nat_lit 559172055557960902967325360128

noncomputable def hp752931 := @hp752929 22531333 67108864 99727 134217728 4351699927905757311669 37778931862957161709568 293330726320265288819 hp752921 hp752930 8332312934964312657227 37778931862957161709568

noncomputable def hp752932 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) 11)

noncomputable def hp752933 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) 11) hp752932

noncomputable def hp752934 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) 11)

noncomputable def hp752935 := @hp752934 90125332 536870912 199454 536870912 90125332 536870912 199454 536870912 96771338370285568 22531333 67108864

noncomputable def hp752936 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp752937 := hp752936 BSN.quadSignNeg 9 10 11 821936 1000 191 241 536870912 268435456 9007199254740992

noncomputable def hp752938 := hp752937 Bool.false 854488679069 3746 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp752939 := hp752938 Bool.true 118068595 171226 Bool.true 508032944 Bool.true 400150292 28296951008113761 1 Bool.false 435535991

noncomputable def hp752940 := hp752939 Bool.false Bool.false 364116714 Bool.true Bool.true 90125332 199454 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 435535991 536870912) BSN.abs_quadSignNeg

noncomputable def hp752941 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp752942 := hp752941 BSN.quadSignPos 7 8 9 821936 1000 74 136 536870912 268435456 9007199254740992

noncomputable def hp752943 := hp752942 Bool.false 854488679069 3746 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp752944 := hp752943 Bool.true 203012101 139840 Bool.true 708530152 Bool.true 397533637 28296951008113761 1 Bool.false 133373265

noncomputable def hp752945 := hp752944 Bool.true Bool.false 396294238 Bool.false Bool.true 118068595 171226 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 133373265 536870912) BSN.abs_quadSignPos

noncomputable def hp752946 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp752947 := hp752946 BSN.quadSignPos 5 6 7 821936 1000 75 4 536870912 268435456 9007199254740992

noncomputable def hp752948 := hp752947 Bool.false 854488679069 3746 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp752949 := hp752948 Bool.true 407182935 103918 Bool.false 584045089 Bool.true 816689244 28296951008113761 1 Bool.false 475473941

noncomputable def hp752950 := hp752949 Bool.false Bool.false 26614699 Bool.false Bool.true 203012101 139840 BSN.abs_quadSignPos (BSN.cos_quad_nat3 75 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 475473941 536870912) BSN.abs_quadSignPos

noncomputable def hp752951 := hp752936 BSN.quadSignPos 3 4 5 821936 1000 287 171 536870912 268435456 9007199254740992

noncomputable def hp752952 := hp752951 Bool.false 854488679069 3746 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp752953 := hp752952 Bool.true 704255009 61422 Bool.false 722320466 Bool.false 79502818 28296951008113761 1 Bool.false 523294293

noncomputable def hp752954 := hp752953 Bool.false Bool.false 79212562 Bool.false Bool.true 407182935 103918 BSN.abs_quadSignPos (BSN.cos_quad_nat3 287 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 523294293 536870912) BSN.abs_quadSignPos

noncomputable def hp752955 := hp752941 BSN.quadSignNeg 1 2 3 821936 1000 650 438 536870912 268435456 9007199254740992

noncomputable def hp752956 := hp752955 Bool.false 854488679069 3746 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp752957 := hp752956 Bool.true 205359840 3802 Bool.false 466531509 Bool.false 328253666 28296951008113761 1 Bool.false 346605901

noncomputable def hp752958 := hp752957 Bool.true Bool.false 439607975 Bool.true Bool.true 704255009 61422 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 650 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 346605901 536870912) BSN.abs_quadSignNeg

noncomputable def hp752959 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) 1) Bool.true

noncomputable def hp752960 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)))

noncomputable def hp752961 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000))) Bool.true 25669980 67108864

noncomputable def hp752962 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 106811084883) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 106811084883 67108864

noncomputable def hp752963 := nat_lit 1214079933328359609979444561683573944281501840519689281

noncomputable def hp752964 := nat_lit 762800276952192652454480171915619387372843565056000

noncomputable def hp752965 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) Bool.false hp752963 hp752964 7777535454206269133

noncomputable def hp752966 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821936 4000) (Real.log (Enclosure.sfrac Bool.false 2702316152384 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1643872))))))

noncomputable def hp752967 := nat_lit 180065975120032973728847752724480000

noncomputable def hp752968 := nat_lit 888016397310645147755835405452665159680

noncomputable def hp752969 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp752966 (Enclosure.sfrac Bool.false 821936 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821936 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp752967 hp752968)) Bool.false

noncomputable def hp752970 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 821936 1000) 821936 1000 2702316152384 16000000 1643872

noncomputable def hp752971 := hp752970 4000 2000 hp752967 hp752968 (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl rfl rfl rfl

noncomputable def hp752972 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp752966 (Enclosure.sfrac Bool.false 821936 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821936 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp752967 hp752968) 1791992870590809857649 1125899906842624000

noncomputable def hp752973 := nat_lit 1591318850212147507992257575889894040248650092405967134392320

noncomputable def hp752974 := @hp752972 7777535454206269133 1115136000000000000000000 hp752967 hp752968 0 1 hp752973 hp752963 hp752964 7777535454206269133 1115136000000000000000000

noncomputable def hp752975 := @Enclosure.Real.IsNear.subLit_ff_p (hp752966 (Enclosure.sfrac Bool.false 821936 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821936 2000) (Real.log Real.pi)) 464333899703160712317 225179981368524800 2593553804261417 1089000000000000000000

noncomputable def hp752976 := nat_lit 1503232573018103229835326259200

noncomputable def hp752977 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821936 4000) (Real.log (Enclosure.sfrac Bool.false 2702316152384 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1643872))))))

noncomputable def hp752978 := @hp752977 (Enclosure.sfrac Bool.false 821936 2000) 2784378331431103061617 1125899906842624000 2593553804261417 1089000000000000000000 821936 2000 0

noncomputable def hp752979 := nat_lit 4643338997031607123170000

noncomputable def hp752980 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821936 4000) (Real.log (Enclosure.sfrac Bool.false 2702316152384 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1643872))))) 2784820300070726951117

noncomputable def hp752981 := nat_lit 6269862607945799579389388588387926016

noncomputable def hp752982 := @hp752980 1125899906842624000 642138451031323 272250000000000000000 883937279247779 2251799813685248 200000001089 8712000000000000000 hp752981 2784378331431103061617 1125899906842624000 2593553804261417

noncomputable def hp752983 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 821936 4000) (Real.log (Enclosure.sfrac Bool.false 2702316152384 16000000)) 821936 4000 0 1 54209968660737127 4503599627370496

noncomputable def hp752984 := nat_lit 116415021257525439858999296

noncomputable def hp752985 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2702316152384) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp752984 hp617687

noncomputable def hp752986 := BSN.log_rat_reduce_isNear 2702316152384 16000000 17 5404632304768 4194304000000 68056174 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp752987 := nat_lit 266058245015373453045416591508902396104495730428035734319385854697762847388343428151148189841995040030720

noncomputable def hp752988 := nat_lit 1423593462437088294420807448046520758778142107023705920033886764359496425759676677013709749966470119424

noncomputable def hp752989 := nat_lit 1888751631050067584335840458327003485701833008577026222405608332567520578698010787366813386670080

noncomputable def hp752990 := BSN.log_dyadic_bound 605164152384 4799468152384 5 4 hp752987 268435456 87120000 hp752988 hp752989 68056174 5404632304768

noncomputable def hp752991 := hp752990 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp752992 := @BSN.binarySplit_of_base4 (BSN.artanhP 605164152384) (BSN.artanhQ 4799468152384) 0 4 hp752988 hp752987 hp752989 rfl rfl rfl

noncomputable def hp752993 := hp752986 rfl rfl rfl rfl (hp752991 (hp752992 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp752994 := @hp752983 12500018513 1089000000000000000 2784820300070726951117 1125899906842624000 642138451031323 272250000000000000000 (Enclosure.Real.IsNear.const Bool.false 821936 4000) (BSN.isNear_log_sfrac 2702316152384 16000000 54209968660737127 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp752985 1000001481040000 87120000000000000000000 54209968660737127 4503599627370496 12500018513 1089000000000000000 (hp752993 rfl rfl rfl) rfl)) rfl

noncomputable def hp752995 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1643872)))) 1 4

noncomputable def hp752996 := @hp752995 0 1 883937279247779 562949953421312 200000001089 2178000000000000000 883937279247779 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp752997 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1643872))) 884279719003555 562949953421312 1

noncomputable def hp752998 := @hp752997 2000000000000000 20411 33554432 1 10890000 29660013328784611606528 883937279247779 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp752999 := BSN.arctan_dyadic_bound_f 1000 1643872 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp753000 := hp752999 1 20411 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1643872) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1643872) 0 0 rfl)

noncomputable def hp753001 := hp752996 (hp752998 (hp753000 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp753002 := @hp752975 1973199203331 4194304000 154113 33554432000 hp752976 1791992870590809857649 1125899906842624000 7777535454206269133 1115136000000000000000000 (@hp752978 1 hp752979 464333899703160712317 225179981368524800 2593553804261417 1089000000000000000000 (@hp752982 1089000000000000000000 hp752994 hp753001 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 821936 2000) rfl rfl)

noncomputable def hp753003 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 821936 2000) (Real.log Real.pi) 821936 2000 0 1 38410761 33554432

noncomputable def hp753004 := hp753002 (@hp753003 3 268435456 1973199203331 4194304000 154113 33554432000 (Enclosure.Real.IsNear.const Bool.false 821936 2000) hd4909 rfl) rfl

noncomputable def hp753005 := @hp752965 1115136000000000000000000 106811084883 67108864 469 67108864 (@hp752969 hp752963 hp752964 7777535454206269133 1115136000000000000000000 (hp752971 rfl rfl rfl rfl rfl) (hp752974 (hp753004 rfl) (Enclosure.Real.IsNear.const Bool.true hp752967 hp752968) rfl rfl)) rfl

noncomputable def hp753006 := nat_lit 3796163325307657614524416

noncomputable def hp753007 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 106811084883) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp753006) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp753008 := BSN.sin_reduce_arg_pos_rat_q1 106811084883 67108864 226375608064910080 72057594037927936 253 hp753006 hp617687 rfl rfl rfl rfl

noncomputable def hp753009 := nat_lit 8469550354887874302009214721355686569948561

noncomputable def hp753010 := BSN.sin_dyadic_bound_f 53946725491 137438953472 2 1 67108864 21801270 hp753009 hp749778 hp753009 hp753009 hp749779

noncomputable def hp753011 := @BSN.binarySplit_of_base (BSN.sinEvenP 53946725491) (BSN.sinEvenQ 137438953472) 0 1 hp753009 hp749778 hp753009 rfl rfl rfl

noncomputable def hp753012 := hp753010 hp753009 25669980 rfl rfl rfl rfl rfl rfl rfl rfl (hp753011 rfl)

noncomputable def hp753013 := @BSN.binarySplit_of_base (BSN.sinOddP 53946725491) (BSN.sinOddQ 137438953472) 0 1 hp753009 hp749779 hp753009 rfl rfl rfl

noncomputable def hp753014 := @BSN.sin_arg_round Bool.false 25669980 67108864 hp753006 hp617687 53946725491 137438953472 21801270 21780000 (hp753012 (hp753013 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753015 := hp753007 25669980 67108864 253 1000000000000000 21780000 10890000 hp753008 BSN.pi_near_15 hp753014 rfl rfl

noncomputable def hp753016 := @hp752962 469 67108864 Bool.true 25669980 67108864 1 10890000 hp753005 (Enclosure.sfrac_false_div 106811084883 67108864) (hp753015 rfl rfl) rfl

noncomputable def hp753017 := @hp752959 6417495 16777216 323407429 45675970560000 205359840 536870912 3802 536870912 (@hp752960 Bool.true 6417495 16777216 323407429 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000)) (@hp752961 5174518864 730815528960000 6417495 16777216 323407429 45675970560000 (hp753016 rfl) rfl))

noncomputable def hp753018 := @hp752965 1115136000000000000000000 854488679069 536870912 3746 536870912 (@hp752969 hp752963 hp752964 7777535454206269133 1115136000000000000000000 (hp752971 rfl rfl rfl rfl rfl) (hp752974 (hp753004 rfl) (Enclosure.Real.IsNear.const Bool.true hp752967 hp752968) rfl rfl)) rfl

noncomputable def hp753019 := hp752958 (BSN.cos_quad_nat2 438 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 439607975 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl rfl (hp753017 rfl) hp753018

noncomputable def hp753020 := nat_lit 6613937467316958999237729928602117260899463002313618254559491718352284001

noncomputable def hp753021 := nat_lit 2244129147673366452270824813132264401288831552176648810711312962234721

noncomputable def hp753022 := nat_lit 19837324143655530264808648136180087253895811343836501466057052529132382561

noncomputable def hp753023 := BSN.cos_dyadic_bound_f 466531509 536870912 3 2 536870912 268435456 hp753020 hp708868 hp753021 hp753022 hp708870

noncomputable def hp753024 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 466531509) (BSN.cosEvenQ 536870912) 0 2 hp753020 hp708868 hp753021 rfl rfl rfl

noncomputable def hp753025 := hp753023 hp753021 346605901 rfl rfl rfl rfl rfl rfl rfl rfl (hp753024 rfl)

noncomputable def hp753026 := @BSN.binarySplit_of_base2 (BSN.cosOddP 466531509) (BSN.cosOddQ 536870912) 0 2 hp753022 hp708870 hp753021 rfl rfl rfl

noncomputable def hp753027 := nat_lit 1620553020705201262615220086195696236731274111463447899711708698444267776

noncomputable def hp753028 := nat_lit 134795899328820642598733030609278355911844153762772120718666794762496

noncomputable def hp753029 := nat_lit 4861389470316946146560462792525870153481998646082818154893688761743278336

noncomputable def hp753030 := BSN.cos_dyadic_bound_f 328253666 536870912 3 2 536870912 268435456 hp753027 hp708868 hp753028 hp753029 hp708870

noncomputable def hp753031 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 328253666) (BSN.cosEvenQ 536870912) 0 2 hp753027 hp708868 hp753028 rfl rfl rfl

noncomputable def hp753032 := hp753030 hp753028 439607975 rfl rfl rfl rfl rfl rfl rfl rfl (hp753031 rfl)

noncomputable def hp753033 := @BSN.binarySplit_of_base2 (BSN.cosOddP 328253666) (BSN.cosOddQ 536870912) 0 2 hp753029 hp708870 hp753028 rfl rfl rfl

noncomputable def hp753034 := hp753019 hd4911 hd4913 hd4915 hd4917 hd4918 (hp753025 (hp753026 rfl) rfl rfl rfl rfl) (hp753032 (hp753033 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753035 := hp752954 (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 79212562 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl rfl (hp753034 rfl rfl rfl rfl rfl) hp753018

noncomputable def hp753036 := nat_lit 97599629756584710333733667000473469780561095846148908316677216959255285533268347452276282790657852508582124589056

noncomputable def hp753037 := nat_lit 20172468332533892710389686250254212027983526390402787004071470799931410738353278953950933416045081992237056

noncomputable def hp753038 := nat_lit 487671538630126107000058837439040998225386926394421006514354447867989196269851385655301065079404870714191725858816

noncomputable def hp753039 := BSN.sin_dyadic_bound_f 722320466 536870912 4 3 536870912 268435456 hp753036 hp642702 hp753037 hp753038 hp642705

noncomputable def hp753040 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 722320466) (BSN.sinEvenQ 536870912) 0 3 hp753036 hp642702 hp753037 rfl rfl rfl

noncomputable def hp753041 := hp753039 hp753037 523294293 rfl rfl rfl rfl rfl rfl rfl rfl (hp753040 rfl)

noncomputable def hp753042 := @BSN.binarySplit_of_base3 (BSN.sinOddP 722320466) (BSN.sinOddQ 536870912) 0 3 hp753038 hp642705 hp753037 rfl rfl rfl

noncomputable def hp753043 := nat_lit 39951224091357450060864826383376

noncomputable def hp753044 := BSN.sin_dyadic_bound_f 79502818 536870912 2 1 536870912 268435456 hp753043 hp708890 hp753043 hp753043 hp708891

noncomputable def hp753045 := @BSN.binarySplit_of_base (BSN.sinEvenP 79502818) (BSN.sinEvenQ 536870912) 0 1 hp753043 hp708890 hp753043 rfl rfl rfl

noncomputable def hp753046 := hp753044 hp753043 79212562 rfl rfl rfl rfl rfl rfl rfl rfl (hp753045 rfl)

noncomputable def hp753047 := @BSN.binarySplit_of_base (BSN.sinOddP 79502818) (BSN.sinOddQ 536870912) 0 1 hp753043 hp708891 hp753043 rfl rfl rfl

noncomputable def hp753048 := hp753035 hd4920 hd4922 hd4924 hd4926 hd4918 (hp753041 (hp753042 rfl) rfl rfl rfl rfl) (hp753046 (hp753047 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753049 := hp752950 (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 26614699 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl rfl (hp753048 rfl rfl rfl rfl rfl) hp753018

noncomputable def hp753050 := nat_lit 29244748298254759135374341491787932887420734703231940592824751788051202305

noncomputable def hp753051 := nat_lit 13538514417980259322498492267052553975112200045727541834576031384142081

noncomputable def hp753052 := nat_lit 76571468900657163029934468252916977236808885422676285532523131584559776001

noncomputable def hp753053 := BSN.sin_dyadic_bound_f 584045089 536870912 3 2 536870912 268435456 hp753050 hp708845 hp753051 hp753052 hp708848

noncomputable def hp753054 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 584045089) (BSN.sinEvenQ 536870912) 0 2 hp753050 hp708845 hp753051 rfl rfl rfl

noncomputable def hp753055 := hp753053 hp753051 475473941 rfl rfl rfl rfl rfl rfl rfl rfl (hp753054 rfl)

noncomputable def hp753056 := @BSN.binarySplit_of_base2 (BSN.sinOddP 584045089) (BSN.sinOddQ 536870912) 0 2 hp753052 hp708848 hp753051 rfl rfl rfl

noncomputable def hp753057 := nat_lit 61474464875349114859162508634470075065701088875814773046120421427804518157608532166244758525261595518324615151616

noncomputable def hp753058 := nat_lit 88040404718343993132822728665220427430068309605473077900587583786057169628609583434348962017243693198606336

noncomputable def hp753059 := nat_lit 372154672839979819044059518195172616368532771579564315148882801318528697842217892559048682854520249629986961489920

noncomputable def hp753060 := BSN.cos_dyadic_bound_f 816689244 536870912 4 3 536870912 268435456 hp753057 hp716712 hp753058 hp753059 hp716714

noncomputable def hp753061 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 816689244) (BSN.cosEvenQ 536870912) 0 3 hp753057 hp716712 hp753058 rfl rfl rfl

noncomputable def hp753062 := hp753060 hp753058 26614699 rfl rfl rfl rfl rfl rfl rfl rfl (hp753061 rfl)

noncomputable def hp753063 := @BSN.binarySplit_of_base3 (BSN.cosOddP 816689244) (BSN.cosOddQ 536870912) 0 3 hp753059 hp716714 hp753058 rfl rfl rfl

noncomputable def hp753064 := hp753049 hd4928 hd4930 hd4932 hd4934 hd4918 (hp753055 (hp753056 rfl) rfl rfl rfl rfl) (hp753062 (hp753063 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753065 := hp752945 (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 396294238 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl rfl (hp753064 rfl rfl rfl rfl rfl) hp753018

noncomputable def hp753066 := nat_lit 34777772288561255887502968348371900039763368777868930269609726128977679486967431767889195145578792181351344766976

noncomputable def hp753067 := nat_lit 16006634940913580027330912565613397498082253032827574790775020712636146136586178317486154973428535573610496

noncomputable def hp753068 := nat_lit 210731545366868139294645182291606888770045968155886024628988443553942823606334458805532949502906663914154114416640

noncomputable def hp753069 := BSN.cos_dyadic_bound_f 708530152 536870912 4 3 536870912 268435456 hp753066 hp716712 hp753067 hp753068 hp716714

noncomputable def hp753070 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 708530152) (BSN.cosEvenQ 536870912) 0 3 hp753066 hp716712 hp753067 rfl rfl rfl

noncomputable def hp753071 := hp753069 hp753067 133373265 rfl rfl rfl rfl rfl rfl rfl rfl (hp753070 rfl)

noncomputable def hp753072 := @BSN.binarySplit_of_base3 (BSN.cosOddP 708530152) (BSN.cosOddQ 536870912) 0 3 hp753068 hp716714 hp753067 rfl rfl rfl

noncomputable def hp753073 := nat_lit 3486277977195753001221596296823788764154305463377599344962375362832837601

noncomputable def hp753074 := nat_lit 623721990651256365277984143360824287369170450291192473191832874724321

noncomputable def hp753075 := nat_lit 10457586487605956490934232922184644643888178049232215649940742422749064161

noncomputable def hp753076 := BSN.cos_dyadic_bound_f 397533637 536870912 3 2 536870912 268435456 hp753073 hp708868 hp753074 hp753075 hp708870

noncomputable def hp753077 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 397533637) (BSN.cosEvenQ 536870912) 0 2 hp753073 hp708868 hp753074 rfl rfl rfl

noncomputable def hp753078 := hp753076 hp753074 396294238 rfl rfl rfl rfl rfl rfl rfl rfl (hp753077 rfl)

noncomputable def hp753079 := @BSN.binarySplit_of_base2 (BSN.cosOddP 397533637) (BSN.cosOddQ 536870912) 0 2 hp753075 hp708870 hp753074 rfl rfl rfl

noncomputable def hp753080 := hp753065 hd4936 hd4938 hd4940 hd4942 hd4918 (hp753071 (hp753072 rfl) rfl rfl rfl rfl) (hp753078 (hp753079 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753081 := hp752940 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 364116714 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl rfl (hp753080 rfl rfl rfl rfl rfl) hp753018

noncomputable def hp753082 := nat_lit 16739555738230180054559754984702600563245865924228530162226622322243010560

noncomputable def hp753083 := nat_lit 4437465650685285829518767241468077250960624397167227196987967082070016

noncomputable def hp753084 := nat_lit 43834509131930314442027756479639672207237617362050736818941268421075009536

noncomputable def hp753085 := BSN.sin_dyadic_bound_f 508032944 536870912 3 2 536870912 268435456 hp753082 hp708845 hp753083 hp753084 hp708848

noncomputable def hp753086 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 508032944) (BSN.sinEvenQ 536870912) 0 2 hp753082 hp708845 hp753083 rfl rfl rfl

noncomputable def hp753087 := hp753085 hp753083 435535991 rfl rfl rfl rfl rfl rfl rfl rfl (hp753086 rfl)

noncomputable def hp753088 := @BSN.binarySplit_of_base2 (BSN.sinOddP 508032944) (BSN.sinOddQ 536870912) 0 2 hp753084 hp708848 hp753083 rfl rfl rfl

noncomputable def hp753089 := nat_lit 6441665300863548670068236300363728464481342136504244203620362004646133760

noncomputable def hp753090 := nat_lit 657332499786446636102499510810235803574734985787261185084358268092416

noncomputable def hp753091 := nat_lit 16869963916309639888958357692220834168054870310391269729467954384496295936

noncomputable def hp753092 := BSN.sin_dyadic_bound_f 400150292 536870912 3 2 536870912 268435456 hp753089 hp708845 hp753090 hp753091 hp708848

noncomputable def hp753093 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 400150292) (BSN.sinEvenQ 536870912) 0 2 hp753089 hp708845 hp753090 rfl rfl rfl

noncomputable def hp753094 := hp753092 hp753090 364116714 rfl rfl rfl rfl rfl rfl rfl rfl (hp753093 rfl)

noncomputable def hp753095 := @BSN.binarySplit_of_base2 (BSN.sinOddP 400150292) (BSN.sinOddQ 536870912) 0 2 hp753091 hp708848 hp753090 rfl rfl rfl

noncomputable def hp753096 := hp753081 hd4944 hd4946 hd4961 hd4963 hd4918 (hp753087 (hp753088 rfl) rfl rfl rfl rfl) (hp753094 (hp753095 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753097 := @hp752935 99727 134217728 (hp753096 rfl rfl rfl rfl rfl) (hp753096 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp753098 := @hp752933 Bool.true 22531333 67108864 99727 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 821936 1000)) (Enclosure.sfrac Bool.false 821936 1000) 11) hp753097

noncomputable def hp753099 := @Enclosure.Real.IsNear.mulLit_tf hp752924 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1))) 19843367 67108864 1

noncomputable def hp753100 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp752923 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753101 := @hp753100 1 1 0 1 19843367 67108864 1 67108864 19843367 67108864 1

noncomputable def hp753102 := @Enclosure.Real.IsNear.of_eq (hp752923 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753103 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 821936 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753104 := @hp753102 (@Inv.inv Real Real.instInv (Real.sqrt hp752925)) Bool.false 19843367 67108864 1 67108864 (hp753103 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 821936 1000) 821936 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000))))

noncomputable def hp753105 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp752925)) Bool.false 19843367 67108864 1 67108864 19843367 67108864

noncomputable def hp753106 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp752925) Bool.false 226957436 67108864 6 67108864 56739359 16777216 3 33554432

noncomputable def hp753107 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 821936 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753108 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 821936 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753109 := @hp753108 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 821936 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 548678599297

noncomputable def hp753110 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 821936 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 821936 1000 0

noncomputable def hp753111 := @hp753110 1 10680707 67108864 1 67108864 548678599297 4194304000 51371 4194304000 (Enclosure.Real.IsNear.const Bool.false 821936 1000) hd4949

noncomputable def hp753112 := @hp753109 4194304000 51371 4194304000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 821936 1000) 821936 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000))) (hp753111 rfl)

noncomputable def hp753113 := @hp753107 548678599297 4194304000 51371 4194304000 383776987 383777024 33554432 hp753112 rfl rfl rfl

noncomputable def hp753114 := @Enclosure.Real.IsNear.recentre' hp752925 Bool.false 767554011 67108864 37 67108864 767554011 67108864 37 67108864 (hp753113 rfl rfl rfl)

noncomputable def hp753115 := @Enclosure.Real.IsNear.sqrt_image hp752925 767554011 67108864 37 67108864 113478715 113478721 33554432 (hp753114 rfl) rfl rfl

noncomputable def hp753116 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp752925) 56739359 16777216 3 33554432 9921683 9921684 33554432 (hp753106 (hp753115 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp753117 := @hp753101 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp753104 (@hp753105 1 67108864 (hp753116 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp753118 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753119 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp753120 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1))) (hp753118 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753119 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp753121 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 821936 1000) 821936 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl

noncomputable def hp753122 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753123 := @hp753122 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753119 (Enclosure.sfrac Bool.false 1 16)))) 36324159

noncomputable def hp753124 := @hp753123 33554432 141 33554432 6037373 16777216 301627429 45675970560000 219302496794307 562949953421312 5530827785903 638596353412300800

noncomputable def hp753125 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753126 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753127 := @hp753125 (@Neg.neg Real Real.instNeg hp753126) Bool.true 36324159 33554432 141 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753128 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753129 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp753130 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp753131 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 184452373) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp753132 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1))) Bool.false 25959363760885895382385

noncomputable def hp753133 := nat_lit 998484790386800156820841923

noncomputable def hp753134 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp753135 := @Enclosure.Real.IsNear.subLit_ff_p hp752925 (Enclosure.sfrac Bool.false 11 1) 767554011 67108864 37 67108864 11 1 0

noncomputable def hp753136 := @hp753134 500000000000000 29356507 67108864 37 67108864 25959363760885895382385 9444732965739290427392 hp753133 hp738031 hd4948 (@hp753135 1 29356507 29356507 67108864 37 67108864 (hp753114 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753137 := @hp753131 184452373 67108864 233 67108864 Bool.true 61991795 67108864 1 10890000 (@hp753132 9444732965739290427392 hp753133 hp738031 184452373 67108864 233 67108864 (hp753136 rfl) rfl) (Enclosure.sfrac_false_div 184452373 67108864)

noncomputable def hp753138 := nat_lit 11390578531387565865435136

noncomputable def hp753139 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 184452373) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp753138) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp753140 := BSN.sin_reduce_arg_pos_rat_q1 184452373 67108864 226375608064910080 72057594037927936 0 hp753138 hp617687 rfl rfl rfl rfl

noncomputable def hp753141 := nat_lit 741244211428745682998226178192421625780452875135103179947223405913993212751319582494685510465

noncomputable def hp753142 := nat_lit 471333009634955345371799405285697509474438848442728964527948831599597495485223929720978241

noncomputable def hp753143 := nat_lit 1940590776488258289674276124800165509647751295789696291062063669761678113641718067790342372161

noncomputable def hp753144 := BSN.sin_dyadic_bound_f 161869856631 137438953472 3 2 67108864 21801270 hp753141 hp738039 hp753142 hp753143 hp738042

noncomputable def hp753145 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 161869856631) (BSN.sinEvenQ 137438953472) 0 2 hp753141 hp738039 hp753142 rfl rfl rfl

noncomputable def hp753146 := hp753144 hp753142 61991795 rfl rfl rfl rfl rfl rfl rfl rfl (hp753145 rfl)

noncomputable def hp753147 := @BSN.binarySplit_of_base2 (BSN.sinOddP 161869856631) (BSN.sinOddQ 137438953472) 0 2 hp753143 hp738042 hp753142 rfl rfl rfl

noncomputable def hp753148 := @BSN.sin_arg_round Bool.false 61991795 67108864 hp753138 hp617687 161869856631 137438953472 21801270 21780000 (hp753146 (hp753147 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753149 := hp753139 61991795 67108864 0 1000000000000000 21780000 10890000 hp753140 BSN.pi_near_15 hp753148 rfl rfl

noncomputable def hp753150 := @hp753129 61991795 67108864 162779929 45675970560000 (@hp753130 61991795 67108864 2604478864 730815528960000 61991795 67108864 162779929 45675970560000 (hp753137 (hp753149 rfl rfl) rfl rfl) rfl)

noncomputable def hp753151 := @hp753128 61991795 67108864 162779929 45675970560000 36324018 36324300 33554432 hp753150 rfl rfl rfl

noncomputable def hp753152 := @Enclosure.Real.IsNear.recentre' hp753126 Bool.false 72648318 67108864 282 67108864 36324159 33554432 141 33554432 (hp753151 rfl rfl rfl)

noncomputable def hp753153 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753119 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp753154 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753119 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 130118001)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp753155 := nat_lit 1228929781506058034268320413525

noncomputable def hp753156 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753119 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp753155

noncomputable def hp753157 := nat_lit 25126253681010019164125067602063709

noncomputable def hp753158 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753119 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp753159 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp753160 := @hp753159 (Enclosure.sfrac Bool.false 1 16) 1108277332536999 4503599627370496 4655410855 4503599627370496 1 16 0

noncomputable def hp753161 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)) 861804503241049

noncomputable def hp753162 := @hp753161 4503599627370496 2172382887 4503599627370496 29356507 67108864 37 67108864 74375232783508240859136 1108277332536999 4503599627370496 4655410855

noncomputable def hp753163 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)) 29356507 67108864 37

noncomputable def hp753164 := @hp753163 67108864 29356507 67108864 37 67108864 861804503241049 4503599627370496 2172382887 4503599627370496 (@hp753135 1 29356507 29356507 67108864 37 67108864 (hp753114 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753165 := hp753164 (@hp753135 1 29356507 29356507 67108864 37 67108864 (hp753114 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753166 := @hp753162 4503599627370496 (hp753165 rfl) (@hp753135 1 29356507 29356507 67108864 37 67108864 (hp753114 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753167 := @hp753158 500000000000000 1389752309247655 4503599627370496 4655410855 4503599627370496 hp753155 hp627574 hp753157 hp742826 hd4948 (@hp753160 1 22236036947962480 1389752309247655 4503599627370496 4655410855 4503599627370496 (hp753166 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp753168 := @hp753154 130118001 67108864 437 67108864 Bool.true 12074746 33554432 1 10890000 (@hp753156 hp627574 hp753157 hp742826 130118001 67108864 437 67108864 (hp753167 rfl) rfl) (Enclosure.sfrac_true_div 130118001 67108864)

noncomputable def hp753169 := nat_lit 2373322982479910789656381457469816144144761233866011117712617751956561293591282546062918183076313756481

noncomputable def hp753170 := nat_lit 23553127944939403063889870236307650808406189837182146612269682063815666666426184313212840545416001

noncomputable def hp753171 := nat_lit 14317965648498474340321673026313933948082530099892259429669081990301189714397838190574629911630384526145

noncomputable def hp753172 := BSN.cos_dyadic_bound_t 130118001 67108864 4 3 33554432 10890000 hp753169 hp745658 hp753170 hp753171 hp745661

noncomputable def hp753173 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 130118001) (BSN.cosEvenQ 67108864) 0 3 hp753169 hp745658 hp753170 rfl rfl rfl

noncomputable def hp753174 := hp753172 hp753170 12074746 rfl rfl rfl rfl rfl rfl rfl rfl (hp753173 rfl)

noncomputable def hp753175 := @BSN.binarySplit_of_base3 (BSN.cosOddP 130118001) (BSN.cosOddQ 67108864) 0 3 hp753171 hp745661 hp753170 rfl rfl rfl

noncomputable def hp753176 := hp753168 (BSN.cos_neg_of_bound 130118001 67108864 Bool.true 12074746 33554432 1 10890000 (hp753174 (hp753175 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp753177 := hp753124 (hp753127 (@Enclosure.Real.IsNear.neg hp753126 Bool.false 36324159 33554432 141 33554432 (hp753152 rfl))) (@hp753153 12074746 33554432 4826038864 730815528960000 6037373 16777216 301627429 45675970560000 (hp753176 rfl) rfl)

noncomputable def hp753178 := @hp753099 67108864 219302496794307 562949953421312 5530827785903 638596353412300800 4351699927905757311669 37778931862957161709568 293330726320265288819 hp752921 (hp753117 rfl) (@hp753120 Bool.false 219302496794307 562949953421312 5530827785903 638596353412300800 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp752925 (Enclosure.sfrac Bool.false 11 1)) (hp753121 rfl (hp752928 rfl rfl))) (hp753177 rfl))

noncomputable def hp753179 := @hp752922 85207062108651627797619 hp752921 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821936 1000))) (@hp752927 85207062108651627797619 hp752921 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 821936 1000) 11 (hp752928 rfl rfl)) (@hp752931 85207062108651627797619 hp752921 hp753098 (hp753178 rfl) rfl rfl))

theorem hd5022 : hp752920 hp752921 := hp753179

noncomputable def hp753180 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 822983 1000)) Bool.false 20487540792335008318061 4722366482869645213696 799794236235346227622709

noncomputable def hp753181 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 822983 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 822983 1000)) Bool.false 20487540792335008318061 4722366482869645213696

noncomputable def hp753182 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 822983 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753183 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp753182 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753184 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 822983 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753185 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp753183 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp753186 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 822983 1000)) hp753185 Bool.false 20487540792335008318061 4722366482869645213696

noncomputable def hp753187 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 822983 1000) 822983 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl

noncomputable def hp753188 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp753183 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp753189 := nat_lit 1374895588727262315655624392704

noncomputable def hp753190 := @hp753188 283447773 67108864 199707 268435456 541676966369431175789 4722366482869645213696 2718224042156503462709 hp750331 hp753189 20487540792335008318061 4722366482869645213696

noncomputable def hp753191 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) 11)

noncomputable def hp753192 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) 11) hp753191

noncomputable def hp753193 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) 11)

noncomputable def hp753194 := @hp753193 1133791092 536870912 199707 536870912 1133791092 536870912 199707 536870912 1217398915159031808 283447773 67108864

noncomputable def hp753195 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp753196 := hp753195 BSN.quadSignNeg 9 10 11 822983 1000 191 241 536870912 268435456 9007199254740992

noncomputable def hp753197 := hp753196 Bool.false 855858644583 3750 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp753198 := hp753197 Bool.false 1116171270 171443 Bool.true 432359361 Bool.true 378050928 28296951008113761 1 Bool.false 387116549

noncomputable def hp753199 := hp753198 Bool.false Bool.false 347572951 Bool.true Bool.false 1133791092 199707 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 387116549 536870912) BSN.abs_quadSignNeg

noncomputable def hp753200 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp753201 := hp753200 BSN.quadSignPos 7 8 9 822983 1000 74 136 536870912 268435456 9007199254740992

noncomputable def hp753202 := hp753201 Bool.false 855858644583 3750 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp753203 := hp753202 Bool.false 1069361564 140018 Bool.true 507426723 Bool.true 262636491 28296951008113761 1 Bool.false 314400462

noncomputable def hp753204 := hp753203 Bool.true Bool.false 473901183 Bool.false Bool.false 1116171270 171443 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 314400462 536870912) BSN.abs_quadSignPos

noncomputable def hp753205 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp753206 := hp753205 BSN.quadSignPos 5 6 7 822983 1000 76 4 536870912 268435456 9007199254740992

noncomputable def hp753207 := hp753206 Bool.false 855858644583 3750 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp753208 := hp753207 Bool.false 745776739 104051 Bool.false 103540867 Bool.true 540527290 28296951008113761 1 Bool.false 526917380

noncomputable def hp753209 := hp753208 Bool.false Bool.false 286989152 Bool.false Bool.false 1069361564 140018 BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 526917380 536870912) BSN.abs_quadSignPos

noncomputable def hp753210 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp753211 := hp753210 BSN.quadSignPos 3 4 5 822983 1000 288 171 536870912 268435456 9007199254740992

noncomputable def hp753212 := hp753211 Bool.false 855858644583 3750 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp753213 := hp753212 Bool.false 369771145 61502 Bool.false 469729748 Bool.false 544797110 28296951008113761 1 Bool.false 344157358

noncomputable def hp753214 := hp753213 Bool.false Bool.false 455994448 Bool.false Bool.false 745776739 104051 BSN.abs_quadSignPos (BSN.cos_quad_nat0 288 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 344157358 536870912) BSN.abs_quadSignPos

noncomputable def hp753215 := hp753195 BSN.quadSignPos 1 2 3 822983 1000 651 439 536870912 268435456 9007199254740992

noncomputable def hp753216 := hp753215 Bool.false 855858644583 3750 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp753217 := hp753216 Bool.true 105248712 3810 Bool.false 603561487 Bool.false 237370137 28296951008113761 1 Bool.false 484220722

noncomputable def hp753218 := hp753217 Bool.false Bool.false 229711678 Bool.false Bool.false 369771145 61502 BSN.abs_quadSignPos (BSN.cos_quad_nat3 651 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 484220722 536870912) BSN.abs_quadSignPos

noncomputable def hp753219 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) 1) Bool.true

noncomputable def hp753220 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)))

noncomputable def hp753221 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000))) Bool.true 13156089 67108864

noncomputable def hp753222 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 26745582643) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false 26745582643 16777216

noncomputable def hp753223 := nat_lit 80304541938018898545436649210693183422466537210973074332313

noncomputable def hp753224 := nat_lit 50374174451433976699438068116360376440388968528216064000

noncomputable def hp753225 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) Bool.false hp753223 hp753224 124598560618031419409

noncomputable def hp753226 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 822983 4000) (Real.log (Enclosure.sfrac Bool.false 2709205073156 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1645966))))))

noncomputable def hp753227 := nat_lit 181215760030584115908930845668640000

noncomputable def hp753228 := nat_lit 894825093159461045989610072772542118720

noncomputable def hp753229 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp753226 (Enclosure.sfrac Bool.false 822983 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 822983 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp753227 hp753228)) Bool.false

noncomputable def hp753230 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 822983 1000) 822983 1000 2709205073156 16000000 1645966

noncomputable def hp753231 := hp753230 4000 2000 hp753227 hp753228 (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl rfl rfl rfl

noncomputable def hp753232 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp753226 (Enclosure.sfrac Bool.false 822983 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 822983 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp753227 hp753228) 28717854339473229135953 18014398509481984000

noncomputable def hp753233 := nat_lit 25697453420166047534539727747421818695189291907511383786340160

noncomputable def hp753234 := @hp753232 124598560618031419409 hp738659 hp753227 hp753228 0 1 hp753233 hp753223 hp753224 124598560618031419409 hp738659

noncomputable def hp753235 := @Enclosure.Real.IsNear.subLit_ff_p (hp753226 (Enclosure.sfrac Bool.false 822983 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 822983 2000) (Real.log Real.pi)) 37203475804494254489681 18014398509481984000 10387302736428779 4356000000000000000000

noncomputable def hp753236 := nat_lit 1927222581239518765725507387392000

noncomputable def hp753237 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 822983 4000) (Real.log (Enclosure.sfrac Bool.false 2709205073156 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1645966))))))

noncomputable def hp753238 := @hp753237 (Enclosure.sfrac Bool.false 822983 2000) 44616247668758760308817 18014398509481984000 10387302736428779 4356000000000000000000 822983 2000 0

noncomputable def hp753239 := nat_lit 74406951608988508979362000

noncomputable def hp753240 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 822983 4000) (Real.log (Enclosure.sfrac Bool.false 2709205073156 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1645966))))) 44623319170482403468817

noncomputable def hp753241 := nat_lit 100466858187845856888027545835317231616

noncomputable def hp753242 := @hp753240 18014398509481984000 10287302735884279 4356000000000000000000 883937715455395 2251799813685248 200000001089 8712000000000000000 hp753241 44616247668758760308817 18014398509481984000 10387302736428779

noncomputable def hp753243 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 822983 4000) (Real.log (Enclosure.sfrac Bool.false 2709205073156 16000000)) 822983 4000 0 1 54221434914794599 4503599627370496

noncomputable def hp753244 := nat_lit 116439644850617674631217152

noncomputable def hp753245 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2709205073156) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp753244 hp617687

noncomputable def hp753246 := BSN.log_rat_reduce_isNear 2709205073156 16000000 17 5418410146312 4194304000000 68739616 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp753247 := nat_lit 269128732583169813665504223640193261566910147757163443561860621987432136701242149572304620828690647941120

noncomputable def hp753248 := nat_lit 1469058547180773888242460582542381624449823654303693253779671989134676952738718136948930854747757871104

noncomputable def hp753249 := nat_lit 2067768724541092292807886114122676427700789941835087533283131284031620803274919012925287334215680

noncomputable def hp753250 := BSN.log_dyadic_bound 612053073156 4806357073156 5 4 hp753247 268435456 87120000 hp753248 hp753249 68739616 5418410146312

noncomputable def hp753251 := hp753250 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp753252 := @BSN.binarySplit_of_base4 (BSN.artanhP 612053073156) (BSN.artanhQ 4806357073156) 0 4 hp753248 hp753247 hp753249 rfl rfl rfl

noncomputable def hp753253 := hp753246 rfl rfl rfl rfl (hp753251 (hp753252 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp753254 := @hp753243 12500018513 1089000000000000000 44623319170482403468817 18014398509481984000 10287302735884279 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 822983 4000) (BSN.isNear_log_sfrac 2709205073156 16000000 54221434914794599 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp753245 1000001481040000 87120000000000000000000 54221434914794599 4503599627370496 12500018513 1089000000000000000 (hp753253 rfl rfl rfl) rfl)) rfl

noncomputable def hp753255 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1645966)))) 1 4

noncomputable def hp753256 := @hp753255 0 1 883937715455395 562949953421312 200000001089 2178000000000000000 883937715455395 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp753257 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1645966))) 884279719003555 562949953421312 1

noncomputable def hp753258 := @hp753257 2000000000000000 20385 33554432 1 10890000 29660027965483400560640 883937715455395 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp753259 := BSN.arctan_dyadic_bound_f 1000 1645966 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp753260 := hp753259 1 20385 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1645966) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1645966) 0 0 rfl)

noncomputable def hp753261 := hp753256 (hp753258 (hp753260 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp753262 := @hp753235 31611403320063 67108864000 2468949 536870912000 hp753236 28717854339473229135953 18014398509481984000 124598560618031419409 hp738659 (@hp753238 1 hp753239 37203475804494254489681 18014398509481984000 10387302736428779 4356000000000000000000 (@hp753242 4356000000000000000000 hp753254 hp753261 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 822983 2000) rfl rfl)

noncomputable def hp753263 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 822983 2000) (Real.log Real.pi) 822983 2000 0 1 38410761 33554432

noncomputable def hp753264 := hp753262 (@hp753263 3 268435456 31611403320063 67108864000 2468949 536870912000 (Enclosure.Real.IsNear.const Bool.false 822983 2000) hd4909 rfl) rfl

noncomputable def hp753265 := @hp753225 hp738659 26745582643 16777216 235 33554432 (@hp753229 hp753223 hp753224 124598560618031419409 hp738659 (hp753231 rfl rfl rfl rfl rfl) (hp753234 (hp753264 rfl) (Enclosure.Real.IsNear.const Bool.true hp753227 hp753228) rfl rfl)) rfl

noncomputable def hp753266 := nat_lit 3320864527044206737227776

noncomputable def hp753267 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 26745582643) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp753266) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp753268 := BSN.sin_reduce_arg_pos_rat_q2 26745582643 16777216 226375608064910080 72057594037927936 253 hp753266 hp619230 rfl rfl rfl rfl

noncomputable def hp753269 := nat_lit 3233322943106388997001554631314921519559306233066203113936553433509324041488768755989111415467540402317864774522242827006601350020846144000000

noncomputable def hp753270 := nat_lit 2047275075136098454371575651798041654404773195528080483650113287284775052937825189843513790947757390707596657963436704485441000000000000

noncomputable def hp753271 := nat_lit 19587840402614261383001682263405114773028035416131142666545169052021365614351332862175417668686089935103051559830931898904532864149056473600000

noncomputable def hp753272 := BSN.cos_dyadic_bound_f 188769293290 137438953472 4 3 67108864 21801270 hp753269 hp740177 hp753270 hp753271 hp740180

noncomputable def hp753273 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 188769293290) (BSN.cosEvenQ 137438953472) 0 3 hp753269 hp740177 hp753270 rfl rfl rfl

noncomputable def hp753274 := hp753272 hp753270 13156089 rfl rfl rfl rfl rfl rfl rfl rfl (hp753273 rfl)

noncomputable def hp753275 := @BSN.binarySplit_of_base3 (BSN.cosOddP 188769293290) (BSN.cosOddQ 137438953472) 0 3 hp753271 hp740180 hp753270 rfl rfl rfl

noncomputable def hp753276 := @BSN.cos_arg_round Bool.false 13156089 67108864 hp753266 hp619230 188769293290 137438953472 21801270 21780000 (hp753274 (hp753275 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753277 := hp753267 13156089 67108864 253 1000000000000000 21780000 10890000 hp753268 BSN.pi_near_15 hp753276 rfl rfl

noncomputable def hp753278 := @hp753222 235 33554432 Bool.true 13156089 67108864 1 10890000 hp753265 (Enclosure.sfrac_false_div 26745582643 16777216) (hp753277 rfl rfl) rfl

noncomputable def hp753279 := @hp753219 13156089 67108864 162044027 22837985280000 105248712 536870912 3810 536870912 (@hp753220 Bool.true 13156089 67108864 162044027 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000)) (@hp753221 2592704432 365407764480000 13156089 67108864 162044027 22837985280000 (hp753278 rfl) rfl))

noncomputable def hp753280 := @hp753225 hp738659 855858644583 536870912 3750 536870912 (@hp753229 hp753223 hp753224 124598560618031419409 hp738659 (hp753231 rfl rfl rfl rfl rfl) (hp753234 (hp753264 rfl) (Enclosure.Real.IsNear.const Bool.true hp753227 hp753228) rfl rfl)) rfl

noncomputable def hp753281 := hp753218 (BSN.cos_quad_nat3 439 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 229711678 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl rfl (hp753279 rfl) hp753280

noncomputable def hp753282 := nat_lit 33356210890213565883399561673140680569503888927680632009162642469884439425

noncomputable def hp753283 := nat_lit 17610519141269508579132581010833768709822227345949539207511285996366721

noncomputable def hp753284 := nat_lit 87332992443378236204537399250874718246979996918698689341470950100941319041

noncomputable def hp753285 := BSN.sin_dyadic_bound_f 603561487 536870912 3 2 536870912 268435456 hp753282 hp708845 hp753283 hp753284 hp708848

noncomputable def hp753286 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 603561487) (BSN.sinEvenQ 536870912) 0 2 hp753282 hp708845 hp753283 rfl rfl rfl

noncomputable def hp753287 := hp753285 hp753283 484220722 rfl rfl rfl rfl rfl rfl rfl rfl (hp753286 rfl)

noncomputable def hp753288 := @BSN.binarySplit_of_base2 (BSN.sinOddP 603561487) (BSN.sinOddQ 536870912) 0 2 hp753284 hp708848 hp753283 rfl rfl rfl

noncomputable def hp753289 := nat_lit 797574194204145846394486675921393501703614916272925507213529999677196225

noncomputable def hp753290 := nat_lit 10078795736421285600747108486007277439690844005896389431044697360321

noncomputable def hp753291 := nat_lit 2088868476293951582285063893999434206965041471729271543785880688692168641

noncomputable def hp753292 := BSN.sin_dyadic_bound_f 237370137 536870912 3 2 536870912 268435456 hp753289 hp708845 hp753290 hp753291 hp708848

noncomputable def hp753293 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 237370137) (BSN.sinEvenQ 536870912) 0 2 hp753289 hp708845 hp753290 rfl rfl rfl

noncomputable def hp753294 := hp753292 hp753290 229711678 rfl rfl rfl rfl rfl rfl rfl rfl (hp753293 rfl)

noncomputable def hp753295 := @BSN.binarySplit_of_base2 (BSN.sinOddP 237370137) (BSN.sinOddQ 536870912) 0 2 hp753291 hp708848 hp753290 rfl rfl rfl

noncomputable def hp753296 := hp753281 hd4911 hd4913 hd4915 hd4917 hd4918 (hp753287 (hp753288 rfl) rfl rfl rfl rfl) (hp753294 (hp753295 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753297 := hp753214 (BSN.cos_quad_nat3 171 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 455994448 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl rfl (hp753296 rfl rfl rfl rfl rfl) hp753280

noncomputable def hp753298 := nat_lit 6797238418602663996060399946690904747558603880637655295848924747818663936

noncomputable def hp753299 := nat_lit 2370197411544740379240905107726429078089907593299875174621213328736256

noncomputable def hp753300 := nat_lit 20386974860984902507422718029857261384519631826726366137197531816798519296

noncomputable def hp753301 := BSN.cos_dyadic_bound_f 469729748 536870912 3 2 536870912 268435456 hp753298 hp708868 hp753299 hp753300 hp708870

noncomputable def hp753302 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 469729748) (BSN.cosEvenQ 536870912) 0 2 hp753298 hp708868 hp753299 rfl rfl rfl

noncomputable def hp753303 := hp753301 hp753299 344157358 rfl rfl rfl rfl rfl rfl rfl rfl (hp753302 rfl)

noncomputable def hp753304 := @BSN.binarySplit_of_base2 (BSN.cosOddP 469729748) (BSN.cosOddQ 536870912) 0 2 hp753300 hp708870 hp753299 rfl rfl rfl

noncomputable def hp753305 := nat_lit 22138731050287287232969488865720423181633850478101741087215820082030240000

noncomputable def hp753306 := nat_lit 7760297321621801766839255300353906480485496596254345797150848100000000

noncomputable def hp753307 := nat_lit 57969826555088840788249969187352916293786917591015386287607951222679200000

noncomputable def hp753308 := BSN.sin_dyadic_bound_f 544797110 536870912 3 2 536870912 268435456 hp753305 hp708845 hp753306 hp753307 hp708848

noncomputable def hp753309 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 544797110) (BSN.sinEvenQ 536870912) 0 2 hp753305 hp708845 hp753306 rfl rfl rfl

noncomputable def hp753310 := hp753308 hp753306 455994448 rfl rfl rfl rfl rfl rfl rfl rfl (hp753309 rfl)

noncomputable def hp753311 := @BSN.binarySplit_of_base2 (BSN.sinOddP 544797110) (BSN.sinOddQ 536870912) 0 2 hp753307 hp708848 hp753306 rfl rfl rfl

noncomputable def hp753312 := hp753297 hd4920 hd4922 hd4924 hd4926 hd4918 (hp753303 (hp753304 rfl) rfl rfl rfl rfl) (hp753310 (hp753311 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753313 := hp753209 (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 286989152 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl rfl (hp753312 rfl rfl rfl rfl rfl) hp753280

noncomputable def hp753314 := nat_lit 114933647328273448333820016432721

noncomputable def hp753315 := BSN.cos_dyadic_bound_f 103540867 536870912 2 1 536870912 268435456 hp753314 hp708767 hp753314 hp753314 hp708768

noncomputable def hp753316 := @BSN.binarySplit_of_base (BSN.cosEvenP 103540867) (BSN.cosEvenQ 536870912) 0 1 hp753314 hp708767 hp753314 rfl rfl rfl

noncomputable def hp753317 := hp753315 hp753314 526917380 rfl rfl rfl rfl rfl rfl rfl rfl (hp753316 rfl)

noncomputable def hp753318 := @BSN.binarySplit_of_base (BSN.cosOddP 103540867) (BSN.cosOddQ 536870912) 0 1 hp753314 hp708768 hp753314 rfl rfl rfl

noncomputable def hp753319 := nat_lit 11765781608944027106325022100874254349916901494230653362160092296422581465049395702053903291653827615787584000000

noncomputable def hp753320 := nat_lit 622030248929372227454289796793028774535207603752895568109938271831742006151568107399332868641000000000000

noncomputable def hp753321 := nat_lit 71349985151330273916786913956466267664226062429533662161837395746901817857703117473680956971105272073397209600000

noncomputable def hp753322 := BSN.cos_dyadic_bound_f 540527290 536870912 4 3 536870912 268435456 hp753319 hp716712 hp753320 hp753321 hp716714

noncomputable def hp753323 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 540527290) (BSN.cosEvenQ 536870912) 0 3 hp753319 hp716712 hp753320 rfl rfl rfl

noncomputable def hp753324 := hp753322 hp753320 286989152 rfl rfl rfl rfl rfl rfl rfl rfl (hp753323 rfl)

noncomputable def hp753325 := @BSN.binarySplit_of_base3 (BSN.cosOddP 540527290) (BSN.cosOddQ 536870912) 0 3 hp753321 hp716714 hp753320 rfl rfl rfl

noncomputable def hp753326 := hp753313 hd4928 hd4930 hd4932 hd4934 hd4918 (hp753317 (hp753318 rfl) rfl rfl rfl rfl) (hp753324 (hp753325 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753327 := hp753204 (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 473901183 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl rfl (hp753326 rfl rfl rfl rfl rfl) hp753280

noncomputable def hp753328 := nat_lit 9136593787753659314237820186840383299000361756252749991335939751137324913464932269152220427504328121297394047601

noncomputable def hp753329 := nat_lit 291393607972462010467023887789177112624062414203021767003087607223528084456387418107348269487778442091121

noncomputable def hp753330 := nat_lit 55411122982581358901541456911526990667325963537214432228921781468164667406518718919508044967212008596530637937265

noncomputable def hp753331 := BSN.cos_dyadic_bound_f 507426723 536870912 4 3 536870912 268435456 hp753328 hp716712 hp753329 hp753330 hp716714

noncomputable def hp753332 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 507426723) (BSN.cosEvenQ 536870912) 0 3 hp753328 hp716712 hp753329 rfl rfl rfl

noncomputable def hp753333 := hp753331 hp753329 314400462 rfl rfl rfl rfl rfl rfl rfl rfl (hp753332 rfl)

noncomputable def hp753334 := @BSN.binarySplit_of_base3 (BSN.cosOddP 507426723) (BSN.cosOddQ 536870912) 0 3 hp753330 hp716714 hp753329 rfl rfl rfl

noncomputable def hp753335 := nat_lit 664085278584364146651478972243936745774710983101359987909338195047708001

noncomputable def hp753336 := nat_lit 22638129416881308875211552898016573277963738455885175205800163898721

noncomputable def hp753337 := nat_lit 1992210559494258677336686493626014204177577021827168193377602984815326561

noncomputable def hp753338 := BSN.cos_dyadic_bound_f 262636491 536870912 3 2 536870912 268435456 hp753335 hp708868 hp753336 hp753337 hp708870

noncomputable def hp753339 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 262636491) (BSN.cosEvenQ 536870912) 0 2 hp753335 hp708868 hp753336 rfl rfl rfl

noncomputable def hp753340 := hp753338 hp753336 473901183 rfl rfl rfl rfl rfl rfl rfl rfl (hp753339 rfl)

noncomputable def hp753341 := @BSN.binarySplit_of_base2 (BSN.cosOddP 262636491) (BSN.cosOddQ 536870912) 0 2 hp753337 hp708870 hp753336 rfl rfl rfl

noncomputable def hp753342 := hp753327 hd4936 hd4938 hd4940 hd4942 hd4918 (hp753333 (hp753334 rfl) rfl rfl rfl rfl) (hp753340 (hp753341 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753343 := hp753199 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 347572951 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl rfl (hp753342 rfl rfl rfl rfl rfl) hp753280

noncomputable def hp753344 := nat_lit 8780134201570161257263588063159856288052162530962596009286985601001455105

noncomputable def hp753345 := nat_lit 1221121648051788386780417282165764493177306256370022347404848540679681

noncomputable def hp753346 := nat_lit 22993612521444052778302229013628498088100043370963152369093925866890329601

noncomputable def hp753347 := BSN.sin_dyadic_bound_f 432359361 536870912 3 2 536870912 268435456 hp753344 hp708845 hp753345 hp753346 hp708848

noncomputable def hp753348 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 432359361) (BSN.sinEvenQ 536870912) 0 2 hp753344 hp708845 hp753345 rfl rfl rfl

noncomputable def hp753349 := hp753347 hp753345 387116549 rfl rfl rfl rfl rfl rfl rfl rfl (hp753348 rfl)

noncomputable def hp753350 := @BSN.binarySplit_of_base2 (BSN.sinOddP 432359361) (BSN.sinOddQ 536870912) 0 2 hp753346 hp708848 hp753345 rfl rfl rfl

noncomputable def hp753351 := nat_lit 5132132122686236395810860086880317689249058243474688027781591548108472320

noncomputable def hp753352 := nat_lit 417255882093751901215765438557814686593584014511388906519048786804736

noncomputable def hp753353 := nat_lit 13440622859416753057378855654928881295683524834981640681198375594629267456

noncomputable def hp753354 := BSN.sin_dyadic_bound_f 378050928 536870912 3 2 536870912 268435456 hp753351 hp708845 hp753352 hp753353 hp708848

noncomputable def hp753355 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 378050928) (BSN.sinEvenQ 536870912) 0 2 hp753351 hp708845 hp753352 rfl rfl rfl

noncomputable def hp753356 := hp753354 hp753352 347572951 rfl rfl rfl rfl rfl rfl rfl rfl (hp753355 rfl)

noncomputable def hp753357 := @BSN.binarySplit_of_base2 (BSN.sinOddP 378050928) (BSN.sinOddQ 536870912) 0 2 hp753353 hp708848 hp753352 rfl rfl rfl

noncomputable def hp753358 := hp753343 hd4944 hd4946 hd4961 hd4963 hd4918 (hp753349 (hp753350 rfl) rfl rfl rfl rfl) (hp753356 (hp753357 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753359 := @hp753194 199707 268435456 (hp753358 rfl rfl rfl rfl rfl) (hp753358 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp753360 := @hp753192 Bool.false 283447773 67108864 199707 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 822983 1000)) (Enclosure.sfrac Bool.false 822983 1000) 11) hp753359

noncomputable def hp753361 := @Enclosure.Real.IsNear.mulLit_tf hp753183 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1))) 4959263 16777216 1

noncomputable def hp753362 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp753182 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753363 := @hp753362 1 1 0 1 4959263 16777216 1 33554432 4959263 16777216 1

noncomputable def hp753364 := @Enclosure.Real.IsNear.of_eq (hp753182 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753365 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 822983 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753366 := @hp753364 (@Inv.inv Real Real.instInv (Real.sqrt hp753184)) Bool.false 4959263 16777216 1 33554432 (hp753365 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 822983 1000) 822983 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000))))

noncomputable def hp753367 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp753184)) Bool.false 19837052 67108864 2 67108864 4959263 16777216

noncomputable def hp753368 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp753184) Bool.false 227029677 67108864 7 67108864 227029677 67108864 7 67108864

noncomputable def hp753369 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 822983 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753370 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 822983 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753371 := @hp753370 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 822983 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8790040288981

noncomputable def hp753372 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 822983 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 822983 1000 0

noncomputable def hp753373 := @hp753372 1 10680707 67108864 1 67108864 8790040288981 67108864000 822983 67108864000 (Enclosure.Real.IsNear.const Bool.false 822983 1000) hd4949

noncomputable def hp753374 := @hp753371 67108864000 822983 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 822983 1000) 822983 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000))) (hp753373 rfl)

noncomputable def hp753375 := @hp753369 8790040288981 67108864000 822983 67108864000 384021341 384021378 33554432 hp753374 rfl rfl rfl

noncomputable def hp753376 := @Enclosure.Real.IsNear.recentre' hp753184 Bool.false 768042719 67108864 37 67108864 768042719 67108864 37 67108864 (hp753375 rfl rfl rfl)

noncomputable def hp753377 := @Enclosure.Real.IsNear.sqrt_image hp753184 768042719 67108864 37 67108864 113514835 113514842 33554432 (hp753376 rfl) rfl rfl

noncomputable def hp753378 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp753184) 227029677 67108864 7 67108864 9918525 9918527 33554432 (hp753368 (hp753377 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp753379 := @hp753363 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp753366 (@hp753367 1 33554432 (hp753378 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp753380 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753381 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp753382 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1))) (hp753380 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753381 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp753383 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 822983 1000) 822983 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl

noncomputable def hp753384 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753385 := @hp753384 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753381 (Enclosure.sfrac Bool.false 1 16)))) 71369537

noncomputable def hp753386 := @hp753385 67108864 271 67108864 1530419 4194304 37958663 5709496320000 109225295446003 281474976710656 545612024387159 63859635341230080000

noncomputable def hp753387 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753388 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753389 := @hp753387 (@Neg.neg Real Real.instNeg hp753388) Bool.true 71369537 67108864 271 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753390 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753391 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp753392 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp753393 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 23440377) (@Nat.cast Real Real.instNatCast 8388608)) Bool.false

noncomputable def hp753394 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1))) Bool.false 26391518333800684739325

noncomputable def hp753395 := nat_lit 998484790390998126575429059

noncomputable def hp753396 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp753397 := @Enclosure.Real.IsNear.subLit_ff_p hp753184 (Enclosure.sfrac Bool.false 11 1) 768042719 67108864 37 67108864 11 1 0

noncomputable def hp753398 := @hp753396 500000000000000 29845215 67108864 37 67108864 26391518333800684739325 9444732965739290427392 hp753395 hp738031 hd4948 (@hp753397 1 29845215 29845215 67108864 37 67108864 (hp753376 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753399 := @hp753393 23440377 8388608 233 67108864 Bool.true 63102548 67108864 1 10890000 (@hp753394 9444732965739290427392 hp753395 hp738031 23440377 8388608 233 67108864 (hp753398 rfl) rfl) (Enclosure.sfrac_false_div 23440377 8388608)

noncomputable def hp753400 := nat_lit 1479138103105797020975104

noncomputable def hp753401 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 23440377) (@Nat.cast Real Real.instNatCast 8388608)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp753400) (@Nat.cast Real Real.instNatCast hp630689)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp753402 := BSN.sin_reduce_arg_pos_rat_q1 23440377 8388608 226375608064910080 72057594037927936 0 hp753400 hp630689 rfl rfl rfl rfl

noncomputable def hp753403 := nat_lit 863412854087663276222206158245746040410535685965027147626016350461554811247414743162605730625

noncomputable def hp753404 := nat_lit 639368579416843634618501584238669126561856508378795598806452259444309083658716900937890625

noncomputable def hp753405 := nat_lit 2260284211577205119459252840459615117727445695561505431860546661836400386179210214252925090625

noncomputable def hp753406 := BSN.sin_dyadic_bound_f 168158533495 137438953472 3 2 67108864 21801270 hp753403 hp738039 hp753404 hp753405 hp738042

noncomputable def hp753407 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 168158533495) (BSN.sinEvenQ 137438953472) 0 2 hp753403 hp738039 hp753404 rfl rfl rfl

noncomputable def hp753408 := hp753406 hp753404 63102548 rfl rfl rfl rfl rfl rfl rfl rfl (hp753407 rfl)

noncomputable def hp753409 := @BSN.binarySplit_of_base2 (BSN.sinOddP 168158533495) (BSN.sinOddQ 137438953472) 0 2 hp753405 hp738042 hp753404 rfl rfl rfl

noncomputable def hp753410 := @BSN.sin_arg_round Bool.false 63102548 67108864 hp753400 hp630689 168158533495 137438953472 21801270 21780000 (hp753408 (hp753409 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753411 := hp753401 63102548 67108864 0 1000000000000000 21780000 10890000 hp753402 BSN.pi_near_15 hp753410 rfl rfl

noncomputable def hp753412 := @hp753391 15775637 16777216 162779929 45675970560000 (@hp753392 63102548 67108864 2604478864 730815528960000 15775637 16777216 162779929 45675970560000 (hp753399 (hp753411 rfl rfl) rfl rfl) rfl)

noncomputable def hp753413 := @hp753390 15775637 16777216 162779929 45675970560000 35684633 35684904 33554432 hp753412 rfl rfl rfl

noncomputable def hp753414 := @Enclosure.Real.IsNear.recentre' hp753388 Bool.false 71369537 67108864 271 67108864 71369537 67108864 271 67108864 (hp753413 rfl rfl rfl)

noncomputable def hp753415 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753381 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp753416 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753381 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65239901)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp753417 := nat_lit 1232346889080044627613733679005

noncomputable def hp753418 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753381 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp753417

noncomputable def hp753419 := nat_lit 126607203414717518968693112594866921

noncomputable def hp753420 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753381 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp753421 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp753422 := @hp753421 (Enclosure.sfrac Bool.false 1 16) 1112141616089535 4503599627370496 4691575247 4503599627370496 1 16 0

noncomputable def hp753423 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)) 890736858396225

noncomputable def hp753424 := @hp753423 4503599627370496 2208547279 4503599627370496 29845215 67108864 37 67108864 74634560462892816138240 1112141616089535 4503599627370496 4691575247

noncomputable def hp753425 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)) 29845215 67108864 37

noncomputable def hp753426 := @hp753425 67108864 29845215 67108864 37 67108864 890736858396225 4503599627370496 2208547279 4503599627370496 (@hp753397 1 29845215 29845215 67108864 37 67108864 (hp753376 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753427 := hp753426 (@hp753397 1 29845215 29845215 67108864 37 67108864 (hp753376 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753428 := @hp753424 4503599627370496 (hp753427 rfl) (@hp753397 1 29845215 29845215 67108864 37 67108864 (hp753376 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753429 := @hp753420 500000000000000 1393616592800191 4503599627370496 4691575247 4503599627370496 hp753417 hp627574 hp753419 hp738055 hd4948 (@hp753422 1 22297865484803056 1393616592800191 4503599627370496 4691575247 4503599627370496 (hp753428 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp753430 := @hp753416 65239901 33554432 55 8388608 Bool.true 12243352 33554432 1 10890000 (@hp753418 hp627574 hp753419 hp738055 65239901 33554432 55 8388608 (hp753429 rfl) rfl) (Enclosure.sfrac_true_div 65239901 33554432)

noncomputable def hp753431 := nat_lit 585950704936024449908525278175403217979086334943999315116741445238147187303888030458479428065300081

noncomputable def hp753432 := nat_lit 5945104872597238011619904682511654242860774352744833545163150706436440804228788322054495538801

noncomputable def hp753433 := nat_lit 3534748940976629743012563097494453385680043640388181283654794337813421765657778736766641231666089585

noncomputable def hp753434 := BSN.cos_dyadic_bound_t 65239901 33554432 4 3 33554432 10890000 hp753431 hp681868 hp753432 hp753433 hp681871

noncomputable def hp753435 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 65239901) (BSN.cosEvenQ 33554432) 0 3 hp753431 hp681868 hp753432 rfl rfl rfl

noncomputable def hp753436 := hp753434 hp753432 12243352 rfl rfl rfl rfl rfl rfl rfl rfl (hp753435 rfl)

noncomputable def hp753437 := @BSN.binarySplit_of_base3 (BSN.cosOddP 65239901) (BSN.cosOddQ 33554432) 0 3 hp753433 hp681871 hp753432 rfl rfl rfl

noncomputable def hp753438 := hp753430 (BSN.cos_neg_of_bound 65239901 33554432 Bool.true 12243352 33554432 1 10890000 (hp753436 (hp753437 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp753439 := hp753386 (hp753389 (@Enclosure.Real.IsNear.neg hp753388 Bool.false 71369537 67108864 271 67108864 (hp753414 rfl))) (@hp753415 12243352 33554432 607338608 91351941120000 1530419 4194304 37958663 5709496320000 (hp753438 rfl) rfl)

noncomputable def hp753440 := @hp753361 33554432 109225295446003 281474976710656 545612024387159 63859635341230080000 541676966369431175789 4722366482869645213696 2718224042156503462709 hp750331 (hp753379 rfl) (@hp753382 Bool.false 109225295446003 281474976710656 545612024387159 63859635341230080000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753184 (Enclosure.sfrac Bool.false 11 1)) (hp753383 rfl (hp753187 rfl rfl))) (hp753439 rfl))

noncomputable def hp753441 := @hp753181 799794236235346227622709 hp750331 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 822983 1000))) (@hp753186 799794236235346227622709 hp750331 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 822983 1000) 11 (hp753187 rfl rfl)) (@hp753190 799794236235346227622709 hp750331 hp753360 (hp753440 rfl) rfl rfl))

theorem hd5023 : hp753180 hp750331 := hp753441

noncomputable def hp753442 := nat_lit 3206762699486611114408661

noncomputable def hp753443 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 824997 1000)) Bool.true 29507171841410328193615 9444732965739290427392 hp753442

noncomputable def hp753444 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 824997 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 824997 1000)) Bool.true 29507171841410328193615 9444732965739290427392

noncomputable def hp753445 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 824997 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753446 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp753445 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753447 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 824997 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753448 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp753446 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp753449 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 824997 1000)) hp753448 Bool.true 29507171841410328193615 9444732965739290427392

noncomputable def hp753450 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 824997 1000) 824997 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl

noncomputable def hp753451 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp753446 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp753452 := nat_lit 7920771128519341131762698813440

noncomputable def hp753453 := @hp753451 869227745 268435456 100097 134217728 1076060568606050850225 9444732965739290427392 10683740111057455528661 hp744350 hp753452 29507171841410328193615 9444732965739290427392

noncomputable def hp753454 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) 11)

noncomputable def hp753455 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) 11) hp753454

noncomputable def hp753456 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) 11)

noncomputable def hp753457 := @hp753456 869227745 536870912 200194 536870912 869227745 536870912 200194 536870912 933326184387706880 869227745 268435456

noncomputable def hp753458 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp753459 := hp753458 BSN.quadSignNeg 9 10 11 824997 1000 191 241 536870912 268435456 9007199254740992

noncomputable def hp753460 := hp753459 Bool.false 858494903795 3759 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp753461 := hp753460 Bool.true 860929610 171861 Bool.true 285788734 Bool.true 334535199 28296951008113761 1 Bool.false 272481463

noncomputable def hp753462 := hp753461 Bool.false Bool.false 313302792 Bool.true Bool.true 869227745 200194 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 272481463 536870912) BSN.abs_quadSignNeg

noncomputable def hp753463 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp753464 := hp753463 BSN.quadSignPos 7 8 9 824997 1000 74 136 536870912 268435456 9007199254740992

noncomputable def hp753465 := hp753464 Bool.false 858494903795 3759 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp753466 := hp753465 Bool.true 854761596 140359 Bool.true 119580346 Bool.true 2143938 28296951008113761 1 Bool.false 523608469

noncomputable def hp753467 := hp753466 Bool.true Bool.false 536866631 Bool.false Bool.true 860929610 171861 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 74 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 523608469 536870912) BSN.abs_quadSignPos

noncomputable def hp753468 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp753469 := hp753468 BSN.quadSignPos 5 6 7 824997 1000 76 4 536870912 268435456 9007199254740992

noncomputable def hp753470 := hp753469 Bool.false 858494903795 3759 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp753471 := hp753470 Bool.true 1074324098 104304 Bool.false 802445804 Bool.true 8298996 28296951008113761 1 Bool.false 40829591

noncomputable def hp753472 := hp753471 Bool.false Bool.false 536806769 Bool.false Bool.true 854761596 140359 BSN.abs_quadSignPos (BSN.cos_quad_nat0 76 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 40829591 536870912) BSN.abs_quadSignPos

noncomputable def hp753473 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp753474 := hp753473 BSN.quadSignPos 3 4 5 824997 1000 289 172 536870912 268435456 9007199254740992

noncomputable def hp753475 := hp753474 Bool.false 858494903795 3759 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp753476 := hp753475 Bool.true 914953674 61651 Bool.false 763732240 Bool.false 597523852 28296951008113761 1 Bool.false 530983273

noncomputable def hp753477 := hp753476 Bool.true Bool.false 237294223 Bool.false Bool.true 1074324098 104304 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 289 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530983273 536870912) BSN.abs_quadSignPos

noncomputable def hp753478 := hp753473 BSN.quadSignPos 1 2 3 824997 1000 653 440 536870912 268435456 9007199254740992

noncomputable def hp753479 := hp753478 Bool.false 858494903795 3759 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp753480 := hp753479 Bool.true 536870776 3818 Bool.false 803720070 Bool.false 842431159 28296951008113761 1 Bool.false 535411495

noncomputable def hp753481 := hp753480 Bool.true Bool.false 883697 Bool.false Bool.true 914953674 61651 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 653 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 535411495 536870912) BSN.abs_quadSignPos

noncomputable def hp753482 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) 1) Bool.true

noncomputable def hp753483 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)))

noncomputable def hp753484 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000))) Bool.true 67108847 67108864

noncomputable def hp753485 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 53655931487) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 53655931487 33554432

noncomputable def hp753486 := nat_lit 9082435186743588999572150214864992619390806108586152173067

noncomputable def hp753487 := nat_lit 5679818529303109284668433434497928165146739485966336000

noncomputable def hp753488 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) Bool.false hp753486 hp753487 11354770476291686921

noncomputable def hp753489 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 824997 4000) (Real.log (Enclosure.sfrac Bool.false 2722481200036 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1649994))))))

noncomputable def hp753490 := nat_lit 183443990007817853616752171883360000

noncomputable def hp753491 := nat_lit 908044604197186507868194043710754099520

noncomputable def hp753492 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp753489 (Enclosure.sfrac Bool.false 824997 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 824997 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp753490 hp753491)) Bool.false

noncomputable def hp753493 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 824997 1000) 824997 1000 2722481200036 16000000 1649994

noncomputable def hp753494 := hp753493 4000 2000 hp753490 hp753491 (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl rfl rfl rfl

noncomputable def hp753495 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp753489 (Enclosure.sfrac Bool.false 824997 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 824997 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp753490 hp753491) 28806312511025571074723 18014398509481984000

noncomputable def hp753496 := nat_lit 26157413337821536318767792618811178743845521592728118258432960

noncomputable def hp753497 := @hp753495 11354770476291686921 hp743892 hp753490 hp753491 0 1 hp753496 hp753486 hp753487 11354770476291686921 hp743892

noncomputable def hp753498 := @Enclosure.Real.IsNear.subLit_ff_p (hp753489 (Enclosure.sfrac Bool.false 824997 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 824997 2000) (Real.log Real.pi)) 1492507997907092049947 720575940379279360 946588888519451 396000000000000000000

noncomputable def hp753499 := nat_lit 77326356345756541991036785786880

noncomputable def hp753500 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 824997 4000) (Real.log (Enclosure.sfrac Bool.false 2722481200036 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1649994))))))

noncomputable def hp753501 := @hp753500 (Enclosure.sfrac Bool.false 824997 2000) 44743612311240855425699 18014398509481984000 946588888519451 396000000000000000000 824997 2000 0

noncomputable def hp753502 := nat_lit 74625399895354602497350000

noncomputable def hp753503 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 824997 4000) (Real.log (Enclosure.sfrac Bool.false 2722481200036 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1649994))))) 44750683819541167257699

noncomputable def hp753504 := nat_lit 100753657866057126894602217293036388352

noncomputable def hp753505 := @hp753503 18014398509481984000 3437492591056487 1452000000000000000000 883938537538979 2251799813685248 200000001089 8712000000000000000 hp753504 44743612311240855425699 18014398509481984000 946588888519451

noncomputable def hp753506 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 824997 4000) (Real.log (Enclosure.sfrac Bool.false 2722481200036 16000000)) 824997 4000 0 1 54243450363505767 4503599627370496

noncomputable def hp753507 := nat_lit 116486922666728290586198016

noncomputable def hp753508 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2722481200036) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp753507 hp617687

noncomputable def hp753509 := BSN.log_rat_reduce_isNear 2722481200036 16000000 17 5444962400072 4194304000000 70051839 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp753510 := nat_lit 275133648524241993985314132377853034637902474140130872767993138205015331522954555692597825732028094545920

noncomputable def hp753511 := nat_lit 1559657932292317514996223922684235796294680248915988507104820691696787472379182515535990973606161547264

noncomputable def hp753512 := nat_lit 2455042241239240918532452606744357305955769881886038831165019747781988523625831076162955228282880

noncomputable def hp753513 := BSN.log_dyadic_bound 625329200036 4819633200036 5 4 hp753510 268435456 87120000 hp753511 hp753512 70051839 5444962400072

noncomputable def hp753514 := hp753513 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp753515 := @BSN.binarySplit_of_base4 (BSN.artanhP 625329200036) (BSN.artanhQ 4819633200036) 0 4 hp753511 hp753510 hp753512 rfl rfl rfl

noncomputable def hp753516 := hp753509 rfl rfl rfl rfl (hp753514 (hp753515 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp753517 := @hp753506 12500018513 1089000000000000000 44750683819541167257699 18014398509481984000 3437492591056487 1452000000000000000000 (Enclosure.Real.IsNear.const Bool.false 824997 4000) (BSN.isNear_log_sfrac 2722481200036 16000000 54243450363505767 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp753508 1000001481040000 87120000000000000000000 54243450363505767 4503599627370496 12500018513 1089000000000000000 (hp753516 rfl rfl rfl) rfl)) rfl

noncomputable def hp753518 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1649994)))) 1 4

noncomputable def hp753519 := @hp753518 0 1 883938537538979 562949953421312 200000001089 2178000000000000000 883938537538979 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp753520 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1649994))) 884279719003555 562949953421312 1

noncomputable def hp753521 := @hp753520 2000000000000000 20336 33554432 1 10890000 29660055550031118204928 883938537538979 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp753522 := BSN.arctan_dyadic_bound_f 1000 1649994 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp753523 := hp753522 1 20336 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1649994) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1649994) 0 0 rfl)

noncomputable def hp753524 := hp753519 (hp753521 (hp753523 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp753525 := @hp753498 31688762592717 67108864000 2474991 536870912000 hp753499 28806312511025571074723 18014398509481984000 11354770476291686921 hp743892 (@hp753501 1 hp753502 1492507997907092049947 720575940379279360 946588888519451 396000000000000000000 (@hp753505 396000000000000000000 hp753517 hp753524 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 824997 2000) rfl rfl)

noncomputable def hp753526 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 824997 2000) (Real.log Real.pi) 824997 2000 0 1 38410761 33554432

noncomputable def hp753527 := hp753525 (@hp753526 3 268435456 31688762592717 67108864000 2474991 536870912000 (Enclosure.Real.IsNear.const Bool.false 824997 2000) hd4909 rfl) rfl

noncomputable def hp753528 := @hp753488 hp743892 53655931487 33554432 471 67108864 (@hp753492 hp753486 hp753487 11354770476291686921 hp743892 (hp753494 rfl rfl rfl rfl rfl) (hp753497 (hp753527 rfl) (Enclosure.Real.IsNear.const Bool.true hp753490 hp753491) rfl rfl)) rfl

noncomputable def hp753529 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 53655931487) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 3421310656977865539584) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp753530 := BSN.sin_reduce_arg_pos_rat_q2 53655931487 33554432 226375608064910080 72057594037927936 254 3421310656977865539584 hp619237 rfl rfl rfl rfl

noncomputable def hp753531 := BSN.cos_dyadic_bound_f 97239497 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp753532 := hp753531 1 67108847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 97239497) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp753533 := hp753532 (@BSN.binarySplit_of_le (BSN.cosOddP 97239497) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp753534 := @BSN.cos_arg_round Bool.false 67108847 67108864 3421310656977865539584 hp619237 97239497 137438953472 21801270 21780000 hp753533 rfl

noncomputable def hp753535 := hp753529 67108847 67108864 254 1000000000000000 21780000 10890000 hp753530 BSN.pi_near_15 hp753534 rfl rfl

noncomputable def hp753536 := @hp753485 471 67108864 Bool.true 67108847 67108864 1 10890000 hp753528 (Enclosure.sfrac_false_div 53655931487 33554432) (hp753535 rfl rfl) rfl

noncomputable def hp753537 := @hp753482 67108847 67108864 324768679 45675970560000 536870776 536870912 3818 536870912 (@hp753483 Bool.true 67108847 67108864 324768679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000)) (@hp753484 5196298864 730815528960000 67108847 67108864 324768679 45675970560000 (hp753536 rfl) rfl))

noncomputable def hp753538 := @hp753488 hp743892 858494903795 536870912 3759 536870912 (@hp753492 hp753486 hp753487 11354770476291686921 hp743892 (hp753494 rfl rfl rfl rfl rfl) (hp753497 (hp753527 rfl) (Enclosure.Real.IsNear.const Bool.true hp753490 hp753491) rfl rfl)) rfl

noncomputable def hp753539 := hp753481 (BSN.cos_quad_nat0 440 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 883697 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl rfl (hp753537 rfl) hp753538

noncomputable def hp753540 := nat_lit 149691890802408309169446143231960056368189919065441852344498912517500625926724528564744363173150360883466406400000

noncomputable def hp753541 := nat_lit 72653704090486440465953498071555263382052567134900368315387272464191821052510184594676358039201000000000000

noncomputable def hp753542 := nat_lit 747691940563561638605772890966427935604132983286212824577532272840612819600807139159099647674892680823188032000000

noncomputable def hp753543 := BSN.sin_dyadic_bound_f 803720070 536870912 4 3 536870912 268435456 hp753540 hp642702 hp753541 hp753542 hp642705

noncomputable def hp753544 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 803720070) (BSN.sinEvenQ 536870912) 0 3 hp753540 hp642702 hp753541 rfl rfl rfl

noncomputable def hp753545 := hp753543 hp753541 535411495 rfl rfl rfl rfl rfl rfl rfl rfl (hp753544 rfl)

noncomputable def hp753546 := @BSN.binarySplit_of_base3 (BSN.sinOddP 803720070) (BSN.sinOddQ 536870912) 0 3 hp753542 hp642705 hp753541 rfl rfl rfl

noncomputable def hp753547 := nat_lit 69628591644514633607215230613200080607004799204579188883101110752661653533973115884288136747549556506817470267361

noncomputable def hp753548 := nat_lit 127765341670024301981660219867737245309634724113703214758794769090140522230837537234513619899180320112115681

noncomputable def hp753549 := nat_lit 421400226672628509533951395911419492265919301234520567851703126312135301579137172182964193305812882837150296047585

noncomputable def hp753550 := BSN.cos_dyadic_bound_f 842431159 536870912 4 3 536870912 268435456 hp753547 hp716712 hp753548 hp753549 hp716714

noncomputable def hp753551 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 842431159) (BSN.cosEvenQ 536870912) 0 3 hp753547 hp716712 hp753548 rfl rfl rfl

noncomputable def hp753552 := hp753550 hp753548 883697 rfl rfl rfl rfl rfl rfl rfl rfl (hp753551 rfl)

noncomputable def hp753553 := @BSN.binarySplit_of_base3 (BSN.cosOddP 842431159) (BSN.cosOddQ 536870912) 0 3 hp753549 hp716714 hp753548 rfl rfl rfl

noncomputable def hp753554 := hp753539 hd4911 hd4913 hd4915 hd4917 hd4918 (hp753545 (hp753546 rfl) rfl rfl rfl rfl) (hp753552 (hp753553 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753555 := hp753477 (BSN.cos_quad_nat0 172 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 237294223 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl rfl (hp753554 rfl rfl rfl rfl rfl) hp753538

noncomputable def hp753556 := nat_lit 122014221315044044632367101807942910420122233398630107869861667315271968952516772806879402639021540645430886400000

noncomputable def hp753557 := nat_lit 39381612107675299222028303022732568934639356135712244758549525685374190925957580586713324978176000000000000

noncomputable def hp753558 := nat_lit 609560899924881017036108065186985645082159282862814652527324739215985759041035681150596270260234649371410432000000

noncomputable def hp753559 := BSN.sin_dyadic_bound_f 763732240 536870912 4 3 536870912 268435456 hp753556 hp642702 hp753557 hp753558 hp642705

noncomputable def hp753560 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 763732240) (BSN.sinEvenQ 536870912) 0 3 hp753556 hp642702 hp753557 rfl rfl rfl

noncomputable def hp753561 := hp753559 hp753557 530983273 rfl rfl rfl rfl rfl rfl rfl rfl (hp753560 rfl)

noncomputable def hp753562 := @BSN.binarySplit_of_base3 (BSN.sinOddP 763732240) (BSN.sinOddQ 536870912) 0 3 hp753558 hp642705 hp753557 rfl rfl rfl

noncomputable def hp753563 := nat_lit 17575279061308897247909956900201301291358488931436234891131626902524126976246148372264222441125647852894133682176

noncomputable def hp753564 := nat_lit 2071395144879980546801965602155234934442209193215516092347658257831137753035851525305985859886816685981696

noncomputable def hp753565 := nat_lit 106558486180922429423588970880704298434094976198333374387690245696788591440334756898410045756299520846569972695040

noncomputable def hp753566 := BSN.cos_dyadic_bound_f 597523852 536870912 4 3 536870912 268435456 hp753563 hp716712 hp753564 hp753565 hp716714

noncomputable def hp753567 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 597523852) (BSN.cosEvenQ 536870912) 0 3 hp753563 hp716712 hp753564 rfl rfl rfl

noncomputable def hp753568 := hp753566 hp753564 237294223 rfl rfl rfl rfl rfl rfl rfl rfl (hp753567 rfl)

noncomputable def hp753569 := @BSN.binarySplit_of_base3 (BSN.cosOddP 597523852) (BSN.cosOddQ 536870912) 0 3 hp753565 hp716714 hp753564 rfl rfl rfl

noncomputable def hp753570 := hp753555 hd4920 hd4922 hd4924 hd4926 hd4918 (hp753561 (hp753562 rfl) rfl rfl rfl rfl) (hp753568 (hp753569 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753571 := hp753472 (BSN.cos_quad_nat0 4 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536806769 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl rfl (hp753570 rfl rfl rfl rfl rfl) hp753538

noncomputable def hp753572 := nat_lit 57284402815782895326724783717909809994347057311443658490935969639565090483345526589069854651066412845189348458496

noncomputable def hp753573 := nat_lit 71283419614650699934394949071901249027370640202606297840247894471974152216911044008705382753041528563695616

noncomputable def hp753574 := nat_lit 346838768855141662652466026728558342271330944171776912532902623613986141841347549553720609149464892268716574638080

noncomputable def hp753575 := BSN.cos_dyadic_bound_f 802445804 536870912 4 3 536870912 268435456 hp753572 hp716712 hp753573 hp753574 hp716714

noncomputable def hp753576 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 802445804) (BSN.cosEvenQ 536870912) 0 3 hp753572 hp716712 hp753573 rfl rfl rfl

noncomputable def hp753577 := hp753575 hp753573 40829591 rfl rfl rfl rfl rfl rfl rfl rfl (hp753576 rfl)

noncomputable def hp753578 := @BSN.binarySplit_of_base3 (BSN.cosOddP 802445804) (BSN.cosOddQ 536870912) 0 3 hp753574 hp716714 hp753573 rfl rfl rfl

noncomputable def hp753579 := nat_lit 4743536220027734460371456256

noncomputable def hp753580 := BSN.cos_dyadic_bound_f 8298996 536870912 2 1 536870912 268435456 hp753579 hp708767 hp753579 hp753579 hp708768

noncomputable def hp753581 := @BSN.binarySplit_of_base (BSN.cosEvenP 8298996) (BSN.cosEvenQ 536870912) 0 1 hp753579 hp708767 hp753579 rfl rfl rfl

noncomputable def hp753582 := hp753580 hp753579 536806769 rfl rfl rfl rfl rfl rfl rfl rfl (hp753581 rfl)

noncomputable def hp753583 := @BSN.binarySplit_of_base (BSN.cosOddP 8298996) (BSN.cosOddQ 536870912) 0 1 hp753579 hp708768 hp753579 rfl rfl rfl

noncomputable def hp753584 := hp753571 hd4928 hd4930 hd4932 hd4934 hd4918 (hp753577 (hp753578 rfl) rfl rfl rfl rfl) (hp753582 (hp753583 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753585 := hp753467 (BSN.cos_quad_nat0 136 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536866631 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl rfl (hp753584 rfl rfl rfl rfl rfl) hp753538

noncomputable def hp753586 := nat_lit 204474531967639162891473495440656

noncomputable def hp753587 := BSN.cos_dyadic_bound_f 119580346 536870912 2 1 536870912 268435456 hp753586 hp708767 hp753586 hp753586 hp708768

noncomputable def hp753588 := @BSN.binarySplit_of_base (BSN.cosEvenP 119580346) (BSN.cosEvenQ 536870912) 0 1 hp753586 hp708767 hp753586 rfl rfl rfl

noncomputable def hp753589 := hp753587 hp753586 523608469 rfl rfl rfl rfl rfl rfl rfl rfl (hp753588 rfl)

noncomputable def hp753590 := @BSN.binarySplit_of_base (BSN.cosOddP 119580346) (BSN.cosOddQ 536870912) 0 1 hp753586 hp708768 hp753586 rfl rfl rfl

noncomputable def hp753591 := BSN.cos_dyadic_bound_f 2143938 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp753592 := hp753591 1 536866631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 2143938) (BSN.cosEvenQ 536870912) 0 0 rfl)

noncomputable def hp753593 := hp753592 (@BSN.binarySplit_of_le (BSN.cosOddP 2143938) (BSN.cosOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp753594 := hp753585 hd4936 hd4938 hd4940 hd4942 hd4918 (hp753589 (hp753590 rfl) rfl rfl rfl rfl) hp753593 rfl

noncomputable def hp753595 := hp753462 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 313302792 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl rfl (hp753594 rfl rfl rfl rfl rfl) hp753538

noncomputable def hp753596 := nat_lit 1675919808072839833178750959859204452291919207329768294148512878682374400

noncomputable def hp753597 := nat_lit 44500084607551695411053857177074805341697569550850159207714587607296

noncomputable def hp753598 := nat_lit 4389241735291882574627967950529153539651139937417739393940721239597711616

noncomputable def hp753599 := BSN.sin_dyadic_bound_f 285788734 536870912 3 2 536870912 268435456 hp753596 hp708845 hp753597 hp753598 hp708848

noncomputable def hp753600 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 285788734) (BSN.sinEvenQ 536870912) 0 2 hp753596 hp708845 hp753597 rfl rfl rfl

noncomputable def hp753601 := hp753599 hp753597 272481463 rfl rfl rfl rfl rfl rfl rfl rfl (hp753600 rfl)

noncomputable def hp753602 := @BSN.binarySplit_of_base2 (BSN.sinOddP 285788734) (BSN.sinOddQ 536870912) 0 2 hp753598 hp708848 hp753597 rfl rfl rfl

noncomputable def hp753603 := nat_lit 3146662863673203986384103274174505757917010289029732647739228373836472065

noncomputable def hp753604 := nat_lit 156868072250924925717750206517465881067555938340151567634754768838401

noncomputable def hp753605 := nat_lit 8241005904169985133507203646313153468832346142606272879636094233279307521

noncomputable def hp753606 := BSN.sin_dyadic_bound_f 334535199 536870912 3 2 536870912 268435456 hp753603 hp708845 hp753604 hp753605 hp708848

noncomputable def hp753607 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 334535199) (BSN.sinEvenQ 536870912) 0 2 hp753603 hp708845 hp753604 rfl rfl rfl

noncomputable def hp753608 := hp753606 hp753604 313302792 rfl rfl rfl rfl rfl rfl rfl rfl (hp753607 rfl)

noncomputable def hp753609 := @BSN.binarySplit_of_base2 (BSN.sinOddP 334535199) (BSN.sinOddQ 536870912) 0 2 hp753605 hp708848 hp753604 rfl rfl rfl

noncomputable def hp753610 := hp753595 hd4944 hd4946 hd4961 hd4963 hd4918 (hp753601 (hp753602 rfl) rfl rfl rfl rfl) (hp753608 (hp753609 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753611 := @hp753457 100097 134217728 (hp753610 rfl rfl rfl rfl rfl) (hp753610 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp753612 := @hp753455 Bool.true 869227745 268435456 100097 134217728 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 824997 1000)) (Enclosure.sfrac Bool.false 824997 1000) 11) hp753611

noncomputable def hp753613 := @Enclosure.Real.IsNear.mulLit_tf hp753446 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1))) 19824935 67108864 1

noncomputable def hp753614 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp753445 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753615 := @hp753614 1 1 0 1 19824935 67108864 1 67108864 19824935 67108864 1

noncomputable def hp753616 := @Enclosure.Real.IsNear.of_eq (hp753445 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753617 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 824997 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753618 := @hp753616 (@Inv.inv Real Real.instInv (Real.sqrt hp753447)) Bool.false 19824935 67108864 1 67108864 (hp753617 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 824997 1000) 824997 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000))))

noncomputable def hp753619 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp753447)) Bool.false 19824935 67108864 1 67108864 19824935 67108864

noncomputable def hp753620 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp753447) Bool.false 227168447 67108864 7 67108864 227168447 67108864 7 67108864

noncomputable def hp753621 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 824997 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753622 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 824997 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753623 := @hp753622 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 824997 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8811551232879

noncomputable def hp753624 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 824997 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 824997 1000 0

noncomputable def hp753625 := @hp753624 1 10680707 67108864 1 67108864 8811551232879 67108864000 824997 67108864000 (Enclosure.Real.IsNear.const Bool.false 824997 1000) hd4949

noncomputable def hp753626 := @hp753623 67108864000 824997 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 824997 1000) 824997 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000))) (hp753625 rfl)

noncomputable def hp753627 := @hp753621 8811551232879 67108864000 824997 67108864000 384490942 384490979 33554432 hp753626 rfl rfl rfl

noncomputable def hp753628 := @Enclosure.Real.IsNear.recentre' hp753447 Bool.false 768981921 67108864 37 67108864 768981921 67108864 37 67108864 (hp753627 rfl rfl rfl)

noncomputable def hp753629 := @Enclosure.Real.IsNear.sqrt_image hp753447 768981921 67108864 37 67108864 113584220 113584227 33554432 (hp753628 rfl) rfl rfl

noncomputable def hp753630 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp753447) 227168447 67108864 7 67108864 9912467 9912468 33554432 (hp753620 (hp753629 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp753631 := @hp753615 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp753618 (@hp753619 1 67108864 (hp753630 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp753632 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753633 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp753634 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1))) (hp753632 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753633 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp753635 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 824997 1000) 824997 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl

noncomputable def hp753636 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753637 := @hp753636 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753633 (Enclosure.sfrac Bool.false 1 16)))) 17357701

noncomputable def hp753638 := @hp753637 16777216 129 33554432 3127035 8388608 308433679 45675970560000 54278138546535 140737488355328 12903883963943549 1532631248189521920000

noncomputable def hp753639 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753640 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753641 := @hp753639 (@Neg.neg Real Real.instNeg hp753640) Bool.true 17357701 16777216 129 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753642 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753643 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp753644 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp753645 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 48356049) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false

noncomputable def hp753646 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1))) Bool.false 27222035614448261602435

noncomputable def hp753647 := nat_lit 998484790399065810324104643

noncomputable def hp753648 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp753649 := @Enclosure.Real.IsNear.subLit_ff_p hp753447 (Enclosure.sfrac Bool.false 11 1) 768981921 67108864 37 67108864 11 1 0

noncomputable def hp753650 := @hp753648 500000000000000 30784417 67108864 37 67108864 27222035614448261602435 9444732965739290427392 hp753647 hp738031 hd4948 (@hp753649 1 30784417 30784417 67108864 37 67108864 (hp753628 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753651 := @hp753645 48356049 16777216 117 33554432 Bool.true 64864576 67108864 1 10890000 (@hp753646 9444732965739290427392 hp753647 hp738031 48356049 16777216 117 33554432 (hp753650 rfl) rfl) (Enclosure.sfrac_false_div 48356049 16777216)

noncomputable def hp753652 := nat_lit 3170888622603963830632448

noncomputable def hp753653 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 48356049) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp753652) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp753654 := BSN.sin_reduce_arg_pos_rat_q1 48356049 16777216 226375608064910080 72057594037927936 0 hp753652 hp619230 rfl rfl rfl rfl

noncomputable def hp753655 := nat_lit 1139962261643706567375139942580301137739201793911192022362405146556863901581242156465287330625

noncomputable def hp753656 := nat_lit 1114010868583817695072727058340006979187789825095050340302861595219307743007988068937890625

noncomputable def hp753657 := nat_lit 2983811810517714828761915434377762016112557800526777596112475512685240863033621286249853090625

noncomputable def hp753658 := BSN.sin_dyadic_bound_f 180244150135 137438953472 3 2 67108864 21801270 hp753655 hp738039 hp753656 hp753657 hp738042

noncomputable def hp753659 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 180244150135) (BSN.sinEvenQ 137438953472) 0 2 hp753655 hp738039 hp753656 rfl rfl rfl

noncomputable def hp753660 := hp753658 hp753656 64864576 rfl rfl rfl rfl rfl rfl rfl rfl (hp753659 rfl)

noncomputable def hp753661 := @BSN.binarySplit_of_base2 (BSN.sinOddP 180244150135) (BSN.sinOddQ 137438953472) 0 2 hp753657 hp738042 hp753656 rfl rfl rfl

noncomputable def hp753662 := @BSN.sin_arg_round Bool.false 64864576 67108864 hp753652 hp619230 180244150135 137438953472 21801270 21780000 (hp753660 (hp753661 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753663 := hp753653 64864576 67108864 0 1000000000000000 21780000 10890000 hp753654 BSN.pi_near_15 hp753662 rfl rfl

noncomputable def hp753664 := @hp753643 1013509 1048576 81730277 22837985280000 (@hp753644 64864576 67108864 1307684432 365407764480000 1013509 1048576 81730277 22837985280000 (hp753651 (hp753663 rfl rfl) rfl rfl) rfl)

noncomputable def hp753665 := @hp753642 1013509 1048576 81730277 22837985280000 34715273 34715531 33554432 hp753664 rfl rfl rfl

noncomputable def hp753666 := @Enclosure.Real.IsNear.recentre' hp753640 Bool.false 69430804 67108864 258 67108864 17357701 16777216 129 33554432 (hp753665 rfl rfl rfl)

noncomputable def hp753667 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753633 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp753668 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753633 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 131049549)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp753669 := nat_lit 1237728003221369388347655610525

noncomputable def hp753670 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753633 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp753669

noncomputable def hp753671 := nat_lit 1027862089907982722370341968824153

noncomputable def hp753672 := nat_lit 154742504910672534362390528000000000000

noncomputable def hp753673 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753633 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp753674 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp753675 := @hp753674 (Enclosure.sfrac Bool.false 1 16) 1118226923742399 4503599627370496 4761076195 4503599627370496 1 16 0

noncomputable def hp753676 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)) 947680330029889

noncomputable def hp753677 := @hp753676 4503599627370496 2278048227 4503599627370496 30784417 67108864 37 67108864 75042938546567025524736 1118226923742399 4503599627370496 4761076195

noncomputable def hp753678 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)) 30784417 67108864 37

noncomputable def hp753679 := @hp753678 67108864 30784417 67108864 37 67108864 947680330029889 4503599627370496 2278048227 4503599627370496 (@hp753649 1 30784417 30784417 67108864 37 67108864 (hp753628 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753680 := hp753679 (@hp753649 1 30784417 30784417 67108864 37 67108864 (hp753628 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753681 := @hp753677 4503599627370496 (hp753680 rfl) (@hp753649 1 30784417 30784417 67108864 37 67108864 (hp753628 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753682 := @hp753673 500000000000000 1399701900453055 4503599627370496 4761076195 4503599627370496 hp753669 hp627574 hp753671 hp753672 hd4948 (@hp753675 1 22395230407248880 1399701900453055 4503599627370496 4761076195 4503599627370496 (hp753681 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp753683 := @hp753668 131049549 67108864 447 67108864 Bool.true 12508140 33554432 1 10890000 (@hp753670 hp627574 hp753671 hp753672 131049549 67108864 447 67108864 (hp753682 rfl) rfl) (Enclosure.sfrac_true_div 131049549 67108864)

noncomputable def hp753684 := nat_lit 2442612344285560546550300068847676165252332537338505065849734786557743328638561068478533560721256648881

noncomputable def hp753685 := nat_lit 25658210762422468779879877727150547236983999802434743638259990861378943934345501573680842212020401

noncomputable def hp753686 := nat_lit 14733607679123402892529406645321035812596156461998990016089806490501533472917662505058573259448576544945

noncomputable def hp753687 := BSN.cos_dyadic_bound_t 131049549 67108864 4 3 33554432 10890000 hp753684 hp745658 hp753685 hp753686 hp745661

noncomputable def hp753688 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 131049549) (BSN.cosEvenQ 67108864) 0 3 hp753684 hp745658 hp753685 rfl rfl rfl

noncomputable def hp753689 := hp753687 hp753685 12508140 rfl rfl rfl rfl rfl rfl rfl rfl (hp753688 rfl)

noncomputable def hp753690 := @BSN.binarySplit_of_base3 (BSN.cosOddP 131049549) (BSN.cosOddQ 67108864) 0 3 hp753686 hp745661 hp753685 rfl rfl rfl

noncomputable def hp753691 := hp753683 (BSN.cos_neg_of_bound 131049549 67108864 Bool.true 12508140 33554432 1 10890000 (hp753689 (hp753690 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp753692 := hp753638 (hp753641 (@Enclosure.Real.IsNear.neg hp753640 Bool.false 17357701 16777216 129 33554432 (hp753666 rfl))) (@hp753667 12508140 33554432 4934938864 730815528960000 3127035 8388608 308433679 45675970560000 (hp753691 rfl) rfl)

noncomputable def hp753693 := @hp753613 67108864 54278138546535 140737488355328 12903883963943549 1532631248189521920000 1076060568606050850225 9444732965739290427392 10683740111057455528661 hp744350 (hp753631 rfl) (@hp753634 Bool.false 54278138546535 140737488355328 12903883963943549 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753447 (Enclosure.sfrac Bool.false 11 1)) (hp753635 rfl (hp753450 rfl rfl))) (hp753692 rfl))

noncomputable def hp753694 := @hp753444 hp753442 hp744350 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 824997 1000))) (@hp753449 hp753442 hp744350 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 824997 1000) 11 (hp753450 rfl rfl)) (@hp753453 hp753442 hp744350 hp753612 (hp753693 rfl) rfl rfl))

theorem hd5024 : hp753443 hp744350 := hp753694

noncomputable def hp753695 := nat_lit 12846455946521565135431573

noncomputable def hp753696 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 826285 1000)) Bool.false 30453645506694091203077 37778931862957161709568 hp753695

noncomputable def hp753697 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 826285 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 826285 1000)) Bool.false 30453645506694091203077 37778931862957161709568

noncomputable def hp753698 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 826285 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753699 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp753698 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753700 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 826285 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753701 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp753699 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp753702 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 826285 1000)) hp753701 Bool.false 30453645506694091203077 37778931862957161709568

noncomputable def hp753703 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 826285 1000) 826285 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl

noncomputable def hp753704 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp753699 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp753705 := nat_lit 2043709554612944856150890774528

noncomputable def hp753706 := @hp753704 46476541 67108864 200501 268435456 4289678915560393761285 37778931862957161709568 42535200969592865351573 hp741590 hp753705 30453645506694091203077 37778931862957161709568

noncomputable def hp753707 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) 11)

noncomputable def hp753708 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) 11) hp753707

noncomputable def hp753709 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) 11)

noncomputable def hp753710 := @hp753709 185906164 536870912 200501 536870912 185906164 536870912 200501 536870912 199615223626203136 46476541 67108864

noncomputable def hp753711 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp753712 := hp753711 BSN.quadSignNeg 9 10 11 826285 1000 191 241 536870912 268435456 9007199254740992

noncomputable def hp753713 := hp753712 Bool.false 860181544832 3765 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp753714 := hp753713 Bool.false 214016643 172124 Bool.true 191361648 Bool.true 306014126 28296951008113761 1 Bool.false 187335270

noncomputable def hp753715 := hp753714 Bool.false Bool.false 289710818 Bool.true Bool.false 185906164 200501 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 187335270 536870912) BSN.abs_quadSignNeg

noncomputable def hp753716 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp753717 := hp753716 BSN.quadSignPos 7 8 9 826285 1000 73 135 536870912 268435456 9007199254740992

noncomputable def hp753718 := hp753717 Bool.false 860181544832 3765 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp753719 := hp753718 Bool.false 227806072 140573 Bool.true 714166644 Bool.true 678175979 28296951008113761 1 Bool.false 521411904

noncomputable def hp753720 := hp753719 Bool.true Bool.false 511672576 Bool.false Bool.false 214016643 172124 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 521411904 536870912) BSN.abs_quadSignPos

noncomputable def hp753721 := hp753716 BSN.quadSignPos 5 6 7 826285 1000 77 3 536870912 268435456 9007199254740992

noncomputable def hp753722 := hp753721 Bool.false 860181544832 3765 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp753723 := hp753722 Bool.false 213264727 104462 Bool.false 406788714 Bool.true 510549688 28296951008113761 1 Bool.false 368967056

noncomputable def hp753724 := hp753723 Bool.true Bool.false 437002742 Bool.false Bool.false 227806072 140573 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 77 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 368967056 536870912) BSN.abs_quadSignPos

noncomputable def hp753725 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp753726 := hp753725 BSN.quadSignNeg 3 4 5 826285 1000 290 173 536870912 268435456 9007199254740992

noncomputable def hp753727 := hp753726 Bool.false 860181544832 3765 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp753728 := hp753727 Bool.false 446279515 61742 Bool.false 648450118 Bool.false 327940258 28296951008113761 1 Bool.false 190614164

noncomputable def hp753729 := hp753728 Bool.true Bool.false 307923791 Bool.true Bool.false 213264727 104462 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 290 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 190614164 536870912) BSN.abs_quadSignNeg

noncomputable def hp753730 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp753731 := hp753730 BSN.quadSignNeg 1 2 3 826285 1000 655 442 536870912 268435456 9007199254740992

noncomputable def hp753732 := hp753731 Bool.false 860181544832 3765 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp753733 := hp753732 Bool.false 536870768 3818 Bool.false 324427254 Bool.false 82763370 28296951008113761 1 Bool.false 305039477

noncomputable def hp753734 := hp753733 Bool.false Bool.false 530504185 Bool.true Bool.false 446279515 61742 BSN.abs_quadSignPos (BSN.cos_quad_nat3 655 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 305039477 536870912) BSN.abs_quadSignNeg

noncomputable def hp753735 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) 1) Bool.false

noncomputable def hp753736 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)))

noncomputable def hp753737 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000))) Bool.false 67108846 67108864

noncomputable def hp753738 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 6720168319) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false 6720168319 4194304

noncomputable def hp753739 := nat_lit 1058210779982105453988006802207573303505617644819050039

noncomputable def hp753740 := nat_lit 660468234816848699011036568729691320589482773708800

noncomputable def hp753741 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) Bool.false hp753739 hp753740 8339789048786566837

noncomputable def hp753742 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 826285 4000) (Real.log (Enclosure.sfrac Bool.false 2730988604900 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1652570))))))

noncomputable def hp753743 := nat_lit 184880447834665233823111085500000000

noncomputable def hp753744 := nat_lit 916583801658999856880378443904205000000

noncomputable def hp753745 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp753742 (Enclosure.sfrac Bool.false 826285 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 826285 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp753743 hp753744)) Bool.false

noncomputable def hp753746 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 826285 1000) 826285 1000 2730988604900 16000000 1652570

noncomputable def hp753747 := hp753746 4000 2000 hp753743 hp753744 (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl rfl rfl rfl

noncomputable def hp753748 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp753742 (Enclosure.sfrac Bool.false 826285 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 826285 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp753743 hp753744) 5772581357466527779679 3602879701896396800

noncomputable def hp753749 := nat_lit 5291053899910527269940034011037866517528088224095250195000000

noncomputable def hp753750 := @hp753748 8339789048786566837 1189478400000000000000000 hp753743 hp753744 0 1 hp753749 hp753739 hp753740 8339789048786566837 1189478400000000000000000

noncomputable def hp753751 := @Enclosure.Real.IsNear.subLit_ff_p (hp753742 (Enclosure.sfrac Bool.false 826285 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 826285 2000) (Real.log Real.pi)) 7476514909490056317791 3602879701896396800 695238519837247 290400000000000000000

noncomputable def hp753752 := nat_lit 77478275449431319463739994931200

noncomputable def hp753753 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 826285 4000) (Real.log (Enclosure.sfrac Bool.false 2730988604900 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1652570))))))

noncomputable def hp753754 := @hp753753 (Enclosure.sfrac Bool.false 826285 2000) 1793003527346157686547 720575940379279360 695238519837247 290400000000000000000 826285 2000 0

noncomputable def hp753755 := nat_lit 2990605963796022527116400

noncomputable def hp753756 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 826285 4000) (Real.log (Enclosure.sfrac Bool.false 2730988604900 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1652570))))) 1793286387849968851667

noncomputable def hp753757 := nat_lit 4037485008815070345941947078101958656

noncomputable def hp753758 := @hp753756 720575940379279360 2065715559402841 871200000000000000000 883939074409891 2251799813685248 200000001089 8712000000000000000 hp753757 1793003527346157686547 720575940379279360 695238519837247

noncomputable def hp753759 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 826285 4000) (Real.log (Enclosure.sfrac Bool.false 2730988604900 16000000)) 826285 4000 0 1 54257501583895655 4503599627370496

noncomputable def hp753760 := nat_lit 116517097432750019250749440

noncomputable def hp753761 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2730988604900) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp753760 hp617687

noncomputable def hp753762 := BSN.log_rat_reduce_isNear 2730988604900 16000000 17 5461977209800 4194304000000 70889357 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp753763 := nat_lit 279042967253034742568453519977202746510169587380387528085845271384102943370334133949129450000000000000000

noncomputable def hp753764 := nat_lit 1619824256663213577278120496810530935123059561131012976211604763695387953695937519111440000000000000000

noncomputable def hp753765 := nat_lit 2735318056257424105544091188841048062862470755793373073044581452762894211263681050000000000000000

noncomputable def hp753766 := BSN.log_dyadic_bound 633836604900 4828140604900 5 4 hp753763 268435456 87120000 hp753764 hp753765 70889357 5461977209800

noncomputable def hp753767 := hp753766 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp753768 := @BSN.binarySplit_of_base4 (BSN.artanhP 633836604900) (BSN.artanhQ 4828140604900) 0 4 hp753764 hp753763 hp753765 rfl rfl rfl

noncomputable def hp753769 := hp753762 rfl rfl rfl rfl (hp753767 (hp753768 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp753770 := @hp753759 12500018513 1089000000000000000 1793286387849968851667 720575940379279360 2065715559402841 871200000000000000000 (Enclosure.Real.IsNear.const Bool.false 826285 4000) (BSN.isNear_log_sfrac 2730988604900 16000000 54257501583895655 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp753761 1000001481040000 87120000000000000000000 54257501583895655 4503599627370496 12500018513 1089000000000000000 (hp753769 rfl rfl rfl) rfl)) rfl

noncomputable def hp753771 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1652570)))) 1 4

noncomputable def hp753772 := @hp753771 0 1 883939074409891 562949953421312 200000001089 2178000000000000000 883939074409891 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp753773 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1652570))) 884279719003555 562949953421312 1

noncomputable def hp753774 := @hp753773 2000000000000000 20304 33554432 1 10890000 29660073564429627686912 883939074409891 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp753775 := BSN.arctan_dyadic_bound_f 1000 1652570 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp753776 := hp753775 1 20304 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1652570) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1652570) 0 0 rfl)

noncomputable def hp753777 := hp753772 (hp753774 (hp753776 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp753778 := @hp753751 6347647130577 13421772800 495771 107374182400 hp753752 5772581357466527779679 3602879701896396800 8339789048786566837 1189478400000000000000000 (@hp753754 1 hp753755 7476514909490056317791 3602879701896396800 695238519837247 290400000000000000000 (@hp753758 290400000000000000000 hp753770 hp753777 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 826285 2000) rfl rfl)

noncomputable def hp753779 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 826285 2000) (Real.log Real.pi) 826285 2000 0 1 38410761 33554432

noncomputable def hp753780 := hp753778 (@hp753779 3 268435456 6347647130577 13421772800 495771 107374182400 (Enclosure.Real.IsNear.const Bool.false 826285 2000) hd4909 rfl) rfl

noncomputable def hp753781 := @hp753741 1189478400000000000000000 6720168319 4194304 471 67108864 (@hp753745 hp753739 hp753740 8339789048786566837 1189478400000000000000000 (hp753747 rfl rfl rfl rfl rfl) (hp753750 (hp753780 rfl) (Enclosure.Real.IsNear.const Bool.true hp753743 hp753744) rfl rfl)) rfl

noncomputable def hp753782 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 6720168319) (@Nat.cast Real Real.instNatCast 4194304)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 440416826899476512768) (@Nat.cast Real Real.instNatCast 604462909807314587353088)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp753783 := BSN.sin_reduce_arg_pos_rat_q0 6720168319 4194304 226375608064910080 72057594037927936 255 440416826899476512768 604462909807314587353088 rfl rfl rfl rfl

noncomputable def hp753784 := BSN.cos_dyadic_bound_f 100139192 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp753785 := hp753784 1 67108846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 100139192) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp753786 := hp753785 (@BSN.binarySplit_of_le (BSN.cosOddP 100139192) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp753787 := @BSN.cos_arg_round Bool.false 67108846 67108864 440416826899476512768 604462909807314587353088 100139192 137438953472 21801270 21780000 hp753786 rfl

noncomputable def hp753788 := hp753782 67108846 67108864 255 1000000000000000 21780000 10890000 hp753783 BSN.pi_near_15 hp753787 rfl rfl

noncomputable def hp753789 := @hp753738 471 67108864 Bool.false 67108846 67108864 1 10890000 hp753781 (Enclosure.sfrac_false_div 6720168319 4194304) (hp753788 rfl rfl) rfl

noncomputable def hp753790 := @hp753735 33554423 33554432 324768679 45675970560000 536870768 536870912 3818 536870912 (@hp753736 Bool.false 33554423 33554432 324768679 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000)) (@hp753737 5196298864 730815528960000 33554423 33554432 324768679 45675970560000 (hp753789 rfl) rfl))

noncomputable def hp753791 := @hp753741 1189478400000000000000000 860181544832 536870912 3765 536870912 (@hp753745 hp753739 hp753740 8339789048786566837 1189478400000000000000000 (hp753747 rfl rfl rfl rfl rfl) (hp753750 (hp753780 rfl) (Enclosure.Real.IsNear.const Bool.true hp753743 hp753744) rfl rfl)) rfl

noncomputable def hp753792 := hp753734 (BSN.cos_quad_nat2 442 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 530504185 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl rfl (hp753790 rfl) hp753791

noncomputable def hp753793 := nat_lit 2783234229986241663642039459683433695570148285792752600585837946473406720

noncomputable def hp753794 := nat_lit 122726583698978063267908005496329978093511655502399985524115236577536

noncomputable def hp753795 := nat_lit 7289224283114167916483860067161998954147760777253062449176822244666368256

noncomputable def hp753796 := BSN.sin_dyadic_bound_f 324427254 536870912 3 2 536870912 268435456 hp753793 hp708845 hp753794 hp753795 hp708848

noncomputable def hp753797 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 324427254) (BSN.sinEvenQ 536870912) 0 2 hp753793 hp708845 hp753794 rfl rfl rfl

noncomputable def hp753798 := hp753796 hp753794 305039477 rfl rfl rfl rfl rfl rfl rfl rfl (hp753797 rfl)

noncomputable def hp753799 := @BSN.binarySplit_of_base2 (BSN.sinOddP 324427254) (BSN.sinOddQ 536870912) 0 2 hp753795 hp708848 hp753794 rfl rfl rfl

noncomputable def hp753800 := nat_lit 46919423218908510589772297610000

noncomputable def hp753801 := BSN.cos_dyadic_bound_f 82763370 536870912 2 1 536870912 268435456 hp753800 hp708767 hp753800 hp753800 hp708768

noncomputable def hp753802 := @BSN.binarySplit_of_base (BSN.cosEvenP 82763370) (BSN.cosEvenQ 536870912) 0 1 hp753800 hp708767 hp753800 rfl rfl rfl

noncomputable def hp753803 := hp753801 hp753800 530504185 rfl rfl rfl rfl rfl rfl rfl rfl (hp753802 rfl)

noncomputable def hp753804 := @BSN.binarySplit_of_base (BSN.cosOddP 82763370) (BSN.cosOddQ 536870912) 0 1 hp753800 hp708768 hp753800 rfl rfl rfl

noncomputable def hp753805 := hp753792 hd4911 hd4913 hd4915 hd4917 hd4918 (hp753798 (hp753799 rfl) rfl rfl rfl rfl) (hp753803 (hp753804 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753806 := hp753729 (BSN.cos_quad_nat1 173 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 307923791 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl rfl (hp753805 rfl rfl rfl rfl rfl) hp753791

noncomputable def hp753807 := nat_lit 24386020658063062298207404430602229138031452002996075353597877502144993034269231288475443915260751139185579462656

noncomputable def hp753808 := nat_lit 5527374408316687849020414404942654256210801819882580807343563104301491342357284465298805022982774853144576

noncomputable def hp753809 := nat_lit 147817044211882456794967091544342715196546502963836511268632230138100982007751575945870120378635306013446690508800

noncomputable def hp753810 := BSN.cos_dyadic_bound_f 648450118 536870912 4 3 536870912 268435456 hp753807 hp716712 hp753808 hp753809 hp716714

noncomputable def hp753811 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 648450118) (BSN.cosEvenQ 536870912) 0 3 hp753807 hp716712 hp753808 rfl rfl rfl

noncomputable def hp753812 := hp753810 hp753808 190614164 rfl rfl rfl rfl rfl rfl rfl rfl (hp753811 rfl)

noncomputable def hp753813 := @BSN.binarySplit_of_base3 (BSN.cosOddP 648450118) (BSN.cosOddQ 536870912) 0 3 hp753809 hp716714 hp753808 rfl rfl rfl

noncomputable def hp753814 := nat_lit 2905763160949837411019865595110965007192118551119635452476517523503612160

noncomputable def hp753815 := nat_lit 133769736634582028972648185031992547568730528927501100169519918121216

noncomputable def hp753816 := nat_lit 7610115508628356277005120842514856554711865879695067373752509529308692736

noncomputable def hp753817 := BSN.sin_dyadic_bound_f 327940258 536870912 3 2 536870912 268435456 hp753814 hp708845 hp753815 hp753816 hp708848

noncomputable def hp753818 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 327940258) (BSN.sinEvenQ 536870912) 0 2 hp753814 hp708845 hp753815 rfl rfl rfl

noncomputable def hp753819 := hp753817 hp753815 307923791 rfl rfl rfl rfl rfl rfl rfl rfl (hp753818 rfl)

noncomputable def hp753820 := @BSN.binarySplit_of_base2 (BSN.sinOddP 327940258) (BSN.sinOddQ 536870912) 0 2 hp753816 hp708848 hp753815 rfl rfl rfl

noncomputable def hp753821 := hp753806 hd4920 hd4922 hd4924 hd4926 hd4918 (hp753812 (hp753813 rfl) rfl rfl rfl rfl) (hp753819 (hp753820 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753822 := hp753724 (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 437002742 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl rfl (hp753821 rfl rfl rfl rfl rfl) hp753791

noncomputable def hp753823 := nat_lit 6879932846702692233747499021534661991562730587790054823690709190580199680

noncomputable def hp753824 := nat_lit 749809886342470271706773578146512886302080761855444657759923556147456

noncomputable def hp753825 := nat_lit 18017657763452972803184495994416639433229329122978568104029769908619141376

noncomputable def hp753826 := BSN.sin_dyadic_bound_f 406788714 536870912 3 2 536870912 268435456 hp753823 hp708845 hp753824 hp753825 hp708848

noncomputable def hp753827 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 406788714) (BSN.sinEvenQ 536870912) 0 2 hp753823 hp708845 hp753824 rfl rfl rfl

noncomputable def hp753828 := hp753826 hp753824 368967056 rfl rfl rfl rfl rfl rfl rfl rfl (hp753827 rfl)

noncomputable def hp753829 := @BSN.binarySplit_of_base2 (BSN.sinOddP 406788714) (BSN.sinOddQ 536870912) 0 2 hp753825 hp708848 hp753824 rfl rfl rfl

noncomputable def hp753830 := nat_lit 17073823375994212230078826799507729546040444956891884800134761332028211200

noncomputable def hp753831 := nat_lit 4616407320353374451044694258773862052705978485075098798897724334800896

noncomputable def hp753832 := nat_lit 44709682277656650377285712112767943510592022350502910030869016696865161216

noncomputable def hp753833 := BSN.sin_dyadic_bound_f 510549688 536870912 3 2 536870912 268435456 hp753830 hp708845 hp753831 hp753832 hp708848

noncomputable def hp753834 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 510549688) (BSN.sinEvenQ 536870912) 0 2 hp753830 hp708845 hp753831 rfl rfl rfl

noncomputable def hp753835 := hp753833 hp753831 437002742 rfl rfl rfl rfl rfl rfl rfl rfl (hp753834 rfl)

noncomputable def hp753836 := @BSN.binarySplit_of_base2 (BSN.sinOddP 510549688) (BSN.sinOddQ 536870912) 0 2 hp753832 hp708848 hp753831 rfl rfl rfl

noncomputable def hp753837 := hp753822 hd4928 hd4930 hd4932 hd4934 hd4918 (hp753828 (hp753829 rfl) rfl rfl rfl rfl) (hp753835 (hp753836 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753838 := hp753720 (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 511672576 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl rfl (hp753837 rfl rfl rfl rfl rfl) hp753791

noncomputable def hp753839 := nat_lit 93262243894655833397441776191882493634122185713533911716668410655638109703606828534373159815533846893061667291136

noncomputable def hp753840 := nat_lit 17603326537183689481062604811291312007877198318482546692318963623722459864337490293950115470587757682753536

noncomputable def hp753841 := nat_lit 466012968374250063743909946433994957253274993162010784912655473546299506584197842370231866204675938555727756394496

noncomputable def hp753842 := BSN.sin_dyadic_bound_f 714166644 536870912 4 3 536870912 268435456 hp753839 hp642702 hp753840 hp753841 hp642705

noncomputable def hp753843 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 714166644) (BSN.sinEvenQ 536870912) 0 3 hp753839 hp642702 hp753840 rfl rfl rfl

noncomputable def hp753844 := hp753842 hp753840 521411904 rfl rfl rfl rfl rfl rfl rfl rfl (hp753843 rfl)

noncomputable def hp753845 := @BSN.binarySplit_of_base3 (BSN.sinOddP 714166644) (BSN.sinOddQ 536870912) 0 3 hp753841 hp642705 hp753840 rfl rfl rfl

noncomputable def hp753846 := nat_lit 75821653210138753529706440630691467376587125885022001513769985138934644451171604535852400285918816519530415117841

noncomputable def hp753847 := nat_lit 9464743220306749498646783244200288308269950100472078503347217043225772808746892932934503898547123900634641

noncomputable def hp753848 := nat_lit 378911066635963933900184994824591760526272828712699007021301292256695206232880100654327278082065930739714777142801

noncomputable def hp753849 := BSN.sin_dyadic_bound_f 678175979 536870912 4 3 536870912 268435456 hp753846 hp642702 hp753847 hp753848 hp642705

noncomputable def hp753850 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 678175979) (BSN.sinEvenQ 536870912) 0 3 hp753846 hp642702 hp753847 rfl rfl rfl

noncomputable def hp753851 := hp753849 hp753847 511672576 rfl rfl rfl rfl rfl rfl rfl rfl (hp753850 rfl)

noncomputable def hp753852 := @BSN.binarySplit_of_base3 (BSN.sinOddP 678175979) (BSN.sinOddQ 536870912) 0 3 hp753848 hp642705 hp753847 rfl rfl rfl

noncomputable def hp753853 := hp753838 hd4936 hd4938 hd4940 hd4942 hd4918 (hp753844 (hp753845 rfl) rfl rfl rfl rfl) (hp753851 (hp753852 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753854 := hp753715 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 289710818 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl rfl (hp753853 rfl rfl rfl rfl rfl) hp753791

noncomputable def hp753855 := nat_lit 1340971691541138917462653723017216

noncomputable def hp753856 := BSN.sin_dyadic_bound_f 191361648 536870912 2 1 536870912 268435456 hp753855 hp708890 hp753855 hp753855 hp708891

noncomputable def hp753857 := @BSN.binarySplit_of_base (BSN.sinEvenP 191361648) (BSN.sinEvenQ 536870912) 0 1 hp753855 hp708890 hp753855 rfl rfl rfl

noncomputable def hp753858 := hp753856 hp753855 187335270 rfl rfl rfl rfl rfl rfl rfl rfl (hp753857 rfl)

noncomputable def hp753859 := @BSN.binarySplit_of_base (BSN.sinOddP 191361648) (BSN.sinOddQ 536870912) 0 1 hp753855 hp708891 hp753855 rfl rfl rfl

noncomputable def hp753860 := nat_lit 2203141246823621429685971086433746383592037459107063474149410034522538240

noncomputable def hp753861 := nat_lit 76900966168456231699448883425785547248410586285432844638906782597376

noncomputable def hp753862 := nat_lit 5770007330592831005754791832943789256616934013854989826738087098482442496

noncomputable def hp753863 := BSN.sin_dyadic_bound_f 306014126 536870912 3 2 536870912 268435456 hp753860 hp708845 hp753861 hp753862 hp708848

noncomputable def hp753864 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 306014126) (BSN.sinEvenQ 536870912) 0 2 hp753860 hp708845 hp753861 rfl rfl rfl

noncomputable def hp753865 := hp753863 hp753861 289710818 rfl rfl rfl rfl rfl rfl rfl rfl (hp753864 rfl)

noncomputable def hp753866 := @BSN.binarySplit_of_base2 (BSN.sinOddP 306014126) (BSN.sinOddQ 536870912) 0 2 hp753862 hp708848 hp753861 rfl rfl rfl

noncomputable def hp753867 := hp753854 hd4944 hd4946 hd4961 hd4963 hd4918 (hp753858 (hp753859 rfl) rfl rfl rfl rfl) (hp753865 (hp753866 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753868 := @hp753710 200501 268435456 (hp753867 rfl rfl rfl rfl rfl) (hp753867 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp753869 := @hp753708 Bool.false 46476541 67108864 200501 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 826285 1000)) (Enclosure.sfrac Bool.false 826285 1000) 11) hp753868

noncomputable def hp753870 := @Enclosure.Real.IsNear.mulLit_tf hp753699 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1))) 4954301 16777216 1

noncomputable def hp753871 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp753698 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753872 := @hp753871 1 1 0 1 4954301 16777216 1 33554432 4954301 16777216 1

noncomputable def hp753873 := @Enclosure.Real.IsNear.of_eq (hp753698 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753874 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 826285 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753875 := @hp753873 (@Inv.inv Real Real.instInv (Real.sqrt hp753700)) Bool.false 4954301 16777216 1 33554432 (hp753874 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 826285 1000) 826285 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000))))

noncomputable def hp753876 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp753700)) Bool.false 19817204 67108864 2 67108864 4954301 16777216

noncomputable def hp753877 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp753700) Bool.false 227257060 67108864 6 67108864 56814265 16777216 3 33554432

noncomputable def hp753878 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 826285 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753879 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 826285 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753880 := @hp753879 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 826285 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 1765061596699

noncomputable def hp753881 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 826285 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 826285 1000 0

noncomputable def hp753882 := @hp753881 1 10680707 67108864 1 67108864 1765061596699 13421772800 165257 13421772800 (Enclosure.Real.IsNear.const Bool.false 826285 1000) hd4949

noncomputable def hp753883 := @hp753880 13421772800 165257 13421772800 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 826285 1000) 826285 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000))) (hp753882 rfl)

noncomputable def hp753884 := @hp753878 1765061596699 13421772800 165257 13421772800 384790962 384790999 33554432 hp753883 rfl rfl rfl

noncomputable def hp753885 := @Enclosure.Real.IsNear.recentre' hp753700 Bool.false 769581961 67108864 37 67108864 769581961 67108864 37 67108864 (hp753884 rfl rfl rfl)

noncomputable def hp753886 := @Enclosure.Real.IsNear.sqrt_image hp753700 769581961 67108864 37 67108864 113628527 113628533 33554432 (hp753885 rfl) rfl rfl

noncomputable def hp753887 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp753700) 56814265 16777216 3 33554432 9908601 9908603 33554432 (hp753877 (hp753886 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp753888 := @hp753872 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp753875 (@hp753876 1 33554432 (hp753887 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp753889 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753890 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp753891 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1))) (hp753889 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753890 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp753892 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 826285 1000) 826285 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl

noncomputable def hp753893 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753894 := @hp753893 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753890 (Enclosure.sfrac Bool.false 1 16)))) 68518123

noncomputable def hp753895 := @hp753894 67108864 251 67108864 12636795 33554432 311156179 45675970560000 865849474135785 2251799813685248 2136464715063683 255438541364920320000

noncomputable def hp753896 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753897 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753898 := @hp753896 (@Neg.neg Real Real.instNeg hp753897) Bool.true 68518123 67108864 251 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753899 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp753900 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp753901 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp753902 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 197194359) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp753903 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1))) Bool.false 27752638817039154744635

noncomputable def hp753904 := nat_lit 998484790404220114676688323

noncomputable def hp753905 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp753906 := @Enclosure.Real.IsNear.subLit_ff_p hp753700 (Enclosure.sfrac Bool.false 11 1) 769581961 67108864 37 67108864 11 1 0

noncomputable def hp753907 := @hp753905 500000000000000 31384457 67108864 37 67108864 27752638817039154744635 9444732965739290427392 hp753904 hp738031 hd4948 (@hp753906 1 31384457 31384457 67108864 37 67108864 (hp753885 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753908 := @hp753902 197194359 67108864 233 67108864 Bool.true 65728590 67108864 1 10890000 (@hp753903 9444732965739290427392 hp753904 hp738031 197194359 67108864 233 67108864 (hp753907 rfl) rfl) (Enclosure.sfrac_false_div 197194359 67108864)

noncomputable def hp753909 := nat_lit 13226892240237488324476928

noncomputable def hp753910 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 197194359) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp753909) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp753911 := BSN.sin_reduce_arg_pos_rat_q1 197194359 67108864 226375608064910080 72057594037927936 0 hp753909 hp617687 rfl rfl rfl rfl

noncomputable def hp753912 := nat_lit 1348451539811537598284149526594728804259719593676197940566493678615186754042780379654363626305

noncomputable def hp753913 := nat_lit 1558203295352167896207770767297857423165260833329297875016527721606769773307320628507917121

noncomputable def hp753914 := nat_lit 3529135989409171152245579036029617003899855180183699552543170970538125776193355808553368107841

noncomputable def hp753915 := BSN.sin_dyadic_bound_f 187965443959 137438953472 3 2 67108864 21801270 hp753912 hp738039 hp753913 hp753914 hp738042

noncomputable def hp753916 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 187965443959) (BSN.sinEvenQ 137438953472) 0 2 hp753912 hp738039 hp753913 rfl rfl rfl

noncomputable def hp753917 := hp753915 hp753913 65728590 rfl rfl rfl rfl rfl rfl rfl rfl (hp753916 rfl)

noncomputable def hp753918 := @BSN.binarySplit_of_base2 (BSN.sinOddP 187965443959) (BSN.sinOddQ 137438953472) 0 2 hp753914 hp738042 hp753913 rfl rfl rfl

noncomputable def hp753919 := @BSN.sin_arg_round Bool.false 65728590 67108864 hp753909 hp617687 187965443959 137438953472 21801270 21780000 (hp753917 (hp753918 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp753920 := hp753910 65728590 67108864 0 1000000000000000 21780000 10890000 hp753911 BSN.pi_near_15 hp753919 rfl rfl

noncomputable def hp753921 := @hp753900 32864295 33554432 162779929 45675970560000 (@hp753901 65728590 67108864 2604478864 730815528960000 32864295 33554432 162779929 45675970560000 (hp753908 (hp753920 rfl rfl) rfl rfl) rfl)

noncomputable def hp753922 := @hp753899 32864295 33554432 162779929 45675970560000 34258936 34259187 33554432 hp753921 rfl rfl rfl

noncomputable def hp753923 := @Enclosure.Real.IsNear.recentre' hp753897 Bool.false 68518123 67108864 251 67108864 68518123 67108864 251 67108864 (hp753922 rfl rfl rfl)

noncomputable def hp753924 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753890 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp753925 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753890 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 131327077)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp753926 := nat_lit 1240349177736136374561192188525

noncomputable def hp753927 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753890 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp753926

noncomputable def hp753928 := nat_lit 25936204573093613779367103078264929

noncomputable def hp753929 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp753890 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp753930 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp753931 := @hp753930 (Enclosure.sfrac Bool.false 1 16) 1121191115341999 4503599627370496 4805479155 4503599627370496 1 16 0

noncomputable def hp753932 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)) 984984141184849

noncomputable def hp753933 := @hp753932 4503599627370496 2322451187 4503599627370496 31384457 67108864 37 67108864 75241862077494524379136 1121191115341999 4503599627370496 4805479155

noncomputable def hp753934 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)) 31384457 67108864 37

noncomputable def hp753935 := @hp753934 67108864 31384457 67108864 37 67108864 984984141184849 4503599627370496 2322451187 4503599627370496 (@hp753906 1 31384457 31384457 67108864 37 67108864 (hp753885 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753936 := hp753935 (@hp753906 1 31384457 31384457 67108864 37 67108864 (hp753885 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753937 := @hp753933 4503599627370496 (hp753936 rfl) (@hp753906 1 31384457 31384457 67108864 37 67108864 (hp753885 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp753938 := @hp753929 500000000000000 1402666092052655 4503599627370496 4805479155 4503599627370496 hp753926 hp627574 hp753928 hp742826 hd4948 (@hp753931 1 22442657472842480 1402666092052655 4503599627370496 4805479155 4503599627370496 (hp753937 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp753939 := @hp753925 131327077 67108864 451 67108864 Bool.true 12636795 33554432 1 10890000 (@hp753927 hp627574 hp753928 hp742826 131327077 67108864 451 67108864 (hp753938 rfl) rfl) (Enclosure.sfrac_true_div 131327077 67108864)

noncomputable def hp753940 := nat_lit 2463549454082008860852472317013633512237450864540125027224233014699060857585986265817991042753687790801

noncomputable def hp753941 := nat_lit 26317906352475250574821504952150934744722258680648524082409656855103774894837240653762407619699921

noncomputable def hp753942 := nat_lit 14859175827558086664920276069329970012009881548522760935427882216599135073368075086960473505889300325585

noncomputable def hp753943 := BSN.cos_dyadic_bound_t 131327077 67108864 4 3 33554432 10890000 hp753940 hp745658 hp753941 hp753942 hp745661

noncomputable def hp753944 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 131327077) (BSN.cosEvenQ 67108864) 0 3 hp753940 hp745658 hp753941 rfl rfl rfl

noncomputable def hp753945 := hp753943 hp753941 12636795 rfl rfl rfl rfl rfl rfl rfl rfl (hp753944 rfl)

noncomputable def hp753946 := @BSN.binarySplit_of_base3 (BSN.cosOddP 131327077) (BSN.cosOddQ 67108864) 0 3 hp753942 hp745661 hp753941 rfl rfl rfl

noncomputable def hp753947 := hp753939 (BSN.cos_neg_of_bound 131327077 67108864 Bool.true 12636795 33554432 1 10890000 (hp753945 (hp753946 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp753948 := hp753895 (hp753898 (@Enclosure.Real.IsNear.neg hp753897 Bool.false 68518123 67108864 251 67108864 (hp753923 rfl))) (@hp753924 12636795 33554432 4978498864 730815528960000 12636795 33554432 311156179 45675970560000 (hp753947 rfl) rfl)

noncomputable def hp753949 := @hp753870 33554432 865849474135785 2251799813685248 2136464715063683 255438541364920320000 4289678915560393761285 37778931862957161709568 42535200969592865351573 hp741590 (hp753888 rfl) (@hp753891 Bool.false 865849474135785 2251799813685248 2136464715063683 255438541364920320000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753700 (Enclosure.sfrac Bool.false 11 1)) (hp753892 rfl (hp753703 rfl rfl))) (hp753948 rfl))

noncomputable def hp753950 := @hp753697 hp753695 hp741590 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 826285 1000))) (@hp753702 hp753695 hp741590 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 826285 1000) 11 (hp753703 rfl rfl)) (@hp753706 hp753695 hp741590 hp753869 (hp753949 rfl) rfl rfl))

theorem hd5025 : hp753696 hp741590 := hp753950

noncomputable def hp753951 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 827572 1000)) Bool.true 147008037433646261728903 75557863725914323419136 389890594628524038105653

noncomputable def hp753952 := nat_lit 519460313115660973506560000

noncomputable def hp753953 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 827572 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 827572 1000)) Bool.true 147008037433646261728903 75557863725914323419136

noncomputable def hp753954 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 827572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753955 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp753954 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp753956 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 827572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp753957 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp753955 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp753958 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 827572 1000)) hp753957 Bool.true 147008037433646261728903 75557863725914323419136

noncomputable def hp753959 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 827572 1000) 827572 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl

noncomputable def hp753960 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp753955 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp753961 := nat_lit 39462169564165904009893425184768

noncomputable def hp753962 := @hp753960 552676513 268435456 200817 268435456 8556571191555306293625 75557863725914323419136 1281491891560372185653 hp753952 hp753961 147008037433646261728903 75557863725914323419136

noncomputable def hp753963 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) 11)

noncomputable def hp753964 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) 11) hp753963

noncomputable def hp753965 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) 11)

noncomputable def hp753966 := @hp753965 552676513 536870912 200817 536870912 552676513 536870912 200817 536870912 593431887150579712 552676513 268435456

noncomputable def hp753967 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp753968 := hp753967 BSN.quadSignNeg 9 10 11 827572 1000 191 241 536870912 268435456 9007199254740992

noncomputable def hp753969 := hp753968 Bool.false 861867414770 3771 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp753970 := hp753969 Bool.true 503162920 172396 Bool.true 96469471 Bool.true 276976791 28296951008113761 1 Bool.false 95951175

noncomputable def hp753971 := hp753970 Bool.false Bool.false 264852463 Bool.true Bool.true 552676513 200817 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 95951175 536870912) BSN.abs_quadSignNeg

noncomputable def hp753972 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp753973 := hp753972 BSN.quadSignPos 7 8 9 827572 1000 73 135 536870912 268435456 9007199254740992

noncomputable def hp753974 := hp753973 Bool.false 861867414770 3771 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp753975 := hp753974 Bool.true 504192197 140795 Bool.true 465092793 Bool.true 510484636 28296951008113761 1 Bool.false 409063255

noncomputable def hp753976 := hp753975 Bool.true Bool.false 436964951 Bool.false Bool.true 503162920 172396 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 409063255 536870912) BSN.abs_quadSignPos

noncomputable def hp753977 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp753978 := hp753977 BSN.quadSignPos 5 6 7 827572 1000 78 3 536870912 268435456 9007199254740992

noncomputable def hp753979 := hp753978 Bool.false 861867414770 3771 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp753980 := hp753979 Bool.true 347966753 104627 Bool.false 11322468 Bool.true 169211920 28296951008113761 1 Bool.false 536751522

noncomputable def hp753981 := hp753980 Bool.true Bool.false 166424229 Bool.false Bool.true 504192197 140795 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536751522 536870912) BSN.abs_quadSignPos

noncomputable def hp753982 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) Real.sin Real.cos BSN.quadSignPos

noncomputable def hp753983 := hp753982 BSN.quadSignNeg 3 4 5 827572 1000 291 174 536870912 268435456 9007199254740992

noncomputable def hp753984 := hp753983 Bool.false 861867414770 3771 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp753985 := hp753984 Bool.true 334159886 61840 Bool.false 533141159 Bool.false 58449625 28296951008113761 1 Bool.false 449735215

noncomputable def hp753986 := hp753985 Bool.false Bool.false 533692321 Bool.true Bool.true 347966753 104627 BSN.abs_quadSignPos (BSN.cos_quad_nat3 291 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 449735215 536870912) BSN.abs_quadSignNeg

noncomputable def hp753987 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp753988 := hp753987 BSN.quadSignPos 1 2 3 827572 1000 656 443 536870912 268435456 9007199254740992

noncomputable def hp753989 := hp753988 Bool.false 861867414770 3771 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp753990 := hp753989 Bool.true 536870784 3826 Bool.false 688050325 Bool.false 166229151 28296951008113761 1 Bool.false 153109223

noncomputable def hp753991 := hp753990 Bool.false Bool.false 163585838 Bool.false Bool.true 334159886 61840 BSN.abs_quadSignPos (BSN.cos_quad_nat0 656 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 153109223 536870912) BSN.abs_quadSignPos

noncomputable def hp753992 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) 1) Bool.true

noncomputable def hp753993 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)))

noncomputable def hp753994 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000))) Bool.true 67108848 67108864

noncomputable def hp753995 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 53866713423) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 53866713423 33554432

noncomputable def hp753996 := nat_lit 637908136863464258151926299612294292632456130847786107

noncomputable def hp753997 := nat_lit 397363117970152743395463449027520793930201300992000

noncomputable def hp753998 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) Bool.false hp753996 hp753997 10440920443615407113

noncomputable def hp753999 := nat_lit 1486848000000000000000000

noncomputable def hp754000 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 827572 4000) (Real.log (Enclosure.sfrac Bool.false 2739502660736 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1655144))))))

noncomputable def hp754001 := nat_lit 186324764413306192374834168463360000

noncomputable def hp754002 := nat_lit 925183105212991925411539732076974571520

noncomputable def hp754003 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp754000 (Enclosure.sfrac Bool.false 827572 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 827572 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp754001 hp754002)) Bool.false

noncomputable def hp754004 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 827572 1000) 827572 1000 2739502660736 16000000 1655144

noncomputable def hp754005 := hp754004 4000 2000 hp754001 hp754002 (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl rfl rfl rfl

noncomputable def hp754006 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp754000 (Enclosure.sfrac Bool.false 827572 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 827572 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp754001 hp754002) 7229868797474068536491 4503599627370496000

noncomputable def hp754007 := nat_lit 6688951625197438979559142715422611001913703198598481649336320

noncomputable def hp754008 := @hp754006 10440920443615407113 hp753999 hp754001 hp754002 0 1 hp754007 hp753996 hp753997 10440920443615407113 hp753999

noncomputable def hp754009 := @Enclosure.Real.IsNear.subLit_ff_p (hp754000 (Enclosure.sfrac Bool.false 827572 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 827572 2000) (Real.log Real.pi)) 9363103240667421252779 4503599627370496000 435194388391039 181500000000000000000

noncomputable def hp754010 := nat_lit 121297070466882702235513389056000

noncomputable def hp754011 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 827572 4000) (Real.log (Enclosure.sfrac Bool.false 2739502660736 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1655144))))))

noncomputable def hp754012 := @hp754011 (Enclosure.sfrac Bool.false 827572 2000) 2245325943215709862127 900719925474099200 435194388391039 181500000000000000000 827572 2000 0

noncomputable def hp754013 := nat_lit 3745241296266968501111600

noncomputable def hp754014 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 827572 4000) (Real.log (Enclosure.sfrac Bool.false 2739502660736 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1655144))))) 2245679519060222183327

noncomputable def hp754015 := nat_lit 5056024540595789198136513133853802496

noncomputable def hp754016 := @hp754014 900719925474099200 2586166330210109 1089000000000000000000 883939611280803 2251799813685248 200000001089 8712000000000000000 hp754015 2245325943215709862127 900719925474099200 435194388391039

noncomputable def hp754017 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 827572 4000) (Real.log (Enclosure.sfrac Bool.false 2739502660736 16000000)) 827572 4000 0 1 54271520038382695 4503599627370496

noncomputable def hp754018 := nat_lit 116547201834531169878671360

noncomputable def hp754019 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2739502660736) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp754018 hp617687

noncomputable def hp754020 := BSN.log_rat_reduce_isNear 2739502660736 16000000 17 5479005321472 4194304000000 71724922 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp754021 := nat_lit 283003916604339834576306794534164328498362607464396055432522844229262099118275415938603310184832874577920

noncomputable def hp754022 := nat_lit 1681726687635400671982768318514440845660798395529311920830409392154693229693359906594985200375943921664

noncomputable def hp754023 := nat_lit 3043453709172044387794354812404580704545012574049651491444255796887888809158694328193185092730880

noncomputable def hp754024 := BSN.log_dyadic_bound 642350660736 4836654660736 5 4 hp754021 268435456 87120000 hp754022 hp754023 71724922 5479005321472

noncomputable def hp754025 := hp754024 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp754026 := @BSN.binarySplit_of_base4 (BSN.artanhP 642350660736) (BSN.artanhQ 4836654660736) 0 4 hp754022 hp754021 hp754023 rfl rfl rfl

noncomputable def hp754027 := hp754020 rfl rfl rfl rfl (hp754025 (hp754026 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp754028 := @hp754017 12500018513 1089000000000000000 2245679519060222183327 900719925474099200 2586166330210109 1089000000000000000000 (Enclosure.Real.IsNear.const Bool.false 827572 4000) (BSN.isNear_log_sfrac 2739502660736 16000000 54271520038382695 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp754019 1000001481040000 87120000000000000000000 54271520038382695 4503599627370496 12500018513 1089000000000000000 (hp754027 rfl rfl rfl) rfl)) rfl

noncomputable def hp754029 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1655144)))) 1 4

noncomputable def hp754030 := @hp754029 0 1 883939611280803 562949953421312 200000001089 2178000000000000000 883939611280803 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp754031 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1655144))) 884279719003555 562949953421312 1

noncomputable def hp754032 := @hp754031 2000000000000000 20272 33554432 1 10890000 29660091578828137168896 883939611280803 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp754033 := BSN.arctan_dyadic_bound_f 1000 1655144 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp754034 := hp754033 1 20272 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1655144) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1655144) 0 0 rfl)

noncomputable def hp754035 := hp754030 (hp754032 (hp754034 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp754036 := @hp754009 7946917575573 16777216000 620679 134217728000 hp754010 7229868797474068536491 4503599627370496000 10440920443615407113 hp753999 (@hp754012 1 hp754013 9363103240667421252779 4503599627370496000 435194388391039 181500000000000000000 (@hp754016 181500000000000000000 hp754028 hp754035 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 827572 2000) rfl rfl)

noncomputable def hp754037 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 827572 2000) (Real.log Real.pi) 827572 2000 0 1 38410761 33554432

noncomputable def hp754038 := hp754036 (@hp754037 3 268435456 7946917575573 16777216000 620679 134217728000 (Enclosure.Real.IsNear.const Bool.false 827572 2000) hd4909 rfl) rfl

noncomputable def hp754039 := @hp753998 hp753999 53866713423 33554432 59 8388608 (@hp754003 hp753996 hp753997 10440920443615407113 hp753999 (hp754005 rfl rfl rfl rfl rfl) (hp754008 (hp754038 rfl) (Enclosure.Real.IsNear.const Bool.true hp754001 hp754002) rfl rfl)) rfl

noncomputable def hp754040 := nat_lit 7592584818471962826244096

noncomputable def hp754041 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 53866713423) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp754040) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp754042 := BSN.sin_reduce_arg_pos_rat_q1 53866713423 33554432 226375608064910080 72057594037927936 255 hp754040 hp619237 rfl rfl rfl rfl

noncomputable def hp754043 := nat_lit 14355205850239584607208172947969362049918554306223137342537293094642634083885428958550806463069388249880815721801858231767383615442599066730496

noncomputable def hp754044 := nat_lit 10197134978777918833797538069377679938649860819631467760411529143453087624793215381151664383024559320130469680337018250512961002742480896

noncomputable def hp754045 := nat_lit 71686994273110460705324802472281685689602232164578195079472424613258548936229720870869328031332019098169965498511222119175181244240662632595456

noncomputable def hp754046 := BSN.sin_dyadic_bound_f 215794239536 137438953472 4 3 67108864 21801270 hp754043 hp737934 hp754044 hp754045 hp737937

noncomputable def hp754047 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215794239536) (BSN.sinEvenQ 137438953472) 0 3 hp754043 hp737934 hp754044 rfl rfl rfl

noncomputable def hp754048 := hp754046 hp754044 67108848 rfl rfl rfl rfl rfl rfl rfl rfl (hp754047 rfl)

noncomputable def hp754049 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215794239536) (BSN.sinOddQ 137438953472) 0 3 hp754045 hp737937 hp754044 rfl rfl rfl

noncomputable def hp754050 := @BSN.sin_arg_round Bool.false 67108848 67108864 hp754040 hp619237 215794239536 137438953472 21801270 21780000 (hp754048 (hp754049 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754051 := hp754041 67108848 67108864 255 1000000000000000 21780000 10890000 hp754042 BSN.pi_near_15 hp754050 rfl rfl

noncomputable def hp754052 := @hp753995 59 8388608 Bool.true 67108848 67108864 1 10890000 hp754039 (Enclosure.sfrac_false_div 53866713423 33554432) (hp754051 rfl rfl) rfl

noncomputable def hp754053 := @hp753992 4194303 4194304 40681163 5709496320000 536870784 536870912 3826 536870912 (@hp753993 Bool.true 4194303 4194304 40681163 5709496320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000)) (@hp753994 650898608 91351941120000 4194303 4194304 40681163 5709496320000 (hp754052 rfl) rfl))

noncomputable def hp754054 := @hp753998 hp753999 861867414770 536870912 3771 536870912 (@hp754003 hp753996 hp753997 10440920443615407113 hp753999 (hp754005 rfl rfl rfl rfl rfl) (hp754008 (hp754038 rfl) (Enclosure.Real.IsNear.const Bool.true hp754001 hp754002) rfl rfl)) rfl

noncomputable def hp754055 := hp753991 (BSN.cos_quad_nat3 443 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 163585838 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl rfl (hp754053 rfl) hp754054

noncomputable def hp754056 := nat_lit 30921640274354541399489606779342939510941738973776220655549652137134187865501281243023308552974481621449619140625

noncomputable def hp754057 := nat_lit 11257512864287746390525362809745596545050667893041335501626045442364504027971972154193549215793609619140625

noncomputable def hp754058 := nat_lit 187390726337579730060724707217509068961298500500748078814547265587401788824498282010946940038229748482505619140625

noncomputable def hp754059 := BSN.cos_dyadic_bound_f 688050325 536870912 4 3 536870912 268435456 hp754056 hp716712 hp754057 hp754058 hp716714

noncomputable def hp754060 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 688050325) (BSN.cosEvenQ 536870912) 0 3 hp754056 hp716712 hp754057 rfl rfl rfl

noncomputable def hp754061 := hp754059 hp754057 153109223 rfl rfl rfl rfl rfl rfl rfl rfl (hp754060 rfl)

noncomputable def hp754062 := @BSN.binarySplit_of_base3 (BSN.cosOddP 688050325) (BSN.cosOddQ 536870912) 0 3 hp754058 hp716714 hp754057 rfl rfl rfl

noncomputable def hp754063 := nat_lit 763534643826547165868441173001601

noncomputable def hp754064 := BSN.sin_dyadic_bound_f 166229151 536870912 2 1 536870912 268435456 hp754063 hp708890 hp754063 hp754063 hp708891

noncomputable def hp754065 := @BSN.binarySplit_of_base (BSN.sinEvenP 166229151) (BSN.sinEvenQ 536870912) 0 1 hp754063 hp708890 hp754063 rfl rfl rfl

noncomputable def hp754066 := hp754064 hp754063 163585838 rfl rfl rfl rfl rfl rfl rfl rfl (hp754065 rfl)

noncomputable def hp754067 := @BSN.binarySplit_of_base (BSN.sinOddP 166229151) (BSN.sinOddQ 536870912) 0 1 hp754063 hp708891 hp754063 rfl rfl rfl

noncomputable def hp754068 := hp754055 hd4911 hd4913 hd4915 hd4917 hd4918 (hp754061 (hp754062 rfl) rfl rfl rfl rfl) (hp754066 (hp754067 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754069 := hp753986 (BSN.cos_quad_nat2 174 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 533692321 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl rfl (hp754068 rfl rfl rfl rfl rfl) hp754054

noncomputable def hp754070 := nat_lit 20303446938658693408834406415913589802040666556907238599439210303763941825

noncomputable def hp754071 := nat_lit 6527361928812750355726972378897108233146405729681656578221998122371521

noncomputable def hp754072 := nat_lit 53165126253364214474942744562588806544395699182623283173595096131945531841

noncomputable def hp754073 := BSN.sin_dyadic_bound_f 533141159 536870912 3 2 536870912 268435456 hp754070 hp708845 hp754071 hp754072 hp708848

noncomputable def hp754074 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 533141159) (BSN.sinEvenQ 536870912) 0 2 hp754070 hp708845 hp754071 rfl rfl rfl

noncomputable def hp754075 := hp754073 hp754071 449735215 rfl rfl rfl rfl rfl rfl rfl rfl (hp754074 rfl)

noncomputable def hp754076 := @BSN.binarySplit_of_base2 (BSN.sinOddP 533141159) (BSN.sinOddQ 536870912) 0 2 hp754072 hp708848 hp754071 rfl rfl rfl

noncomputable def hp754077 := nat_lit 11671506511799639780097900390625

noncomputable def hp754078 := BSN.cos_dyadic_bound_f 58449625 536870912 2 1 536870912 268435456 hp754077 hp708767 hp754077 hp754077 hp708768

noncomputable def hp754079 := @BSN.binarySplit_of_base (BSN.cosEvenP 58449625) (BSN.cosEvenQ 536870912) 0 1 hp754077 hp708767 hp754077 rfl rfl rfl

noncomputable def hp754080 := hp754078 hp754077 533692321 rfl rfl rfl rfl rfl rfl rfl rfl (hp754079 rfl)

noncomputable def hp754081 := @BSN.binarySplit_of_base (BSN.cosOddP 58449625) (BSN.cosOddQ 536870912) 0 1 hp754077 hp708768 hp754077 rfl rfl rfl

noncomputable def hp754082 := hp754069 hd4920 hd4922 hd4924 hd4926 hd4918 (hp754075 (hp754076 rfl) rfl rfl rfl rfl) (hp754080 (hp754081 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754083 := hp753981 (BSN.cos_quad_nat3 3 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 166424229 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl rfl (hp754082 rfl rfl rfl rfl rfl) hp754054

noncomputable def hp754084 := nat_lit 16434799408019414272838328576

noncomputable def hp754085 := BSN.cos_dyadic_bound_f 11322468 536870912 2 1 536870912 268435456 hp754084 hp708767 hp754084 hp754084 hp708768

noncomputable def hp754086 := @BSN.binarySplit_of_base (BSN.cosEvenP 11322468) (BSN.cosEvenQ 536870912) 0 1 hp754084 hp708767 hp754084 rfl rfl rfl

noncomputable def hp754087 := hp754085 hp754084 536751522 rfl rfl rfl rfl rfl rfl rfl rfl (hp754086 rfl)

noncomputable def hp754088 := @BSN.binarySplit_of_base (BSN.cosOddP 11322468) (BSN.cosOddQ 536870912) 0 1 hp754084 hp708768 hp754084 rfl rfl rfl

noncomputable def hp754089 := nat_lit 819830012950728502944743464960000

noncomputable def hp754090 := BSN.sin_dyadic_bound_f 169211920 536870912 2 1 536870912 268435456 hp754089 hp708890 hp754089 hp754089 hp708891

noncomputable def hp754091 := @BSN.binarySplit_of_base (BSN.sinEvenP 169211920) (BSN.sinEvenQ 536870912) 0 1 hp754089 hp708890 hp754089 rfl rfl rfl

noncomputable def hp754092 := hp754090 hp754089 166424229 rfl rfl rfl rfl rfl rfl rfl rfl (hp754091 rfl)

noncomputable def hp754093 := @BSN.binarySplit_of_base (BSN.sinOddP 169211920) (BSN.sinOddQ 536870912) 0 1 hp754089 hp708891 hp754089 rfl rfl rfl

noncomputable def hp754094 := hp754083 hd4928 hd4930 hd4932 hd4934 hd4918 (hp754087 (hp754088 rfl) rfl rfl rfl rfl) (hp754092 (hp754093 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754095 := hp753976 (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 436964951 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl rfl (hp754094 rfl rfl rfl rfl rfl) hp754054

noncomputable def hp754096 := nat_lit 11757110583996076176240305191354482177095098235164563031880738821345897665

noncomputable def hp754097 := nat_lit 2189358484066681342325702992390341415431360065469362876947778459921601

noncomputable def hp754098 := nat_lit 30788887806253615358456081505845488006290749366277381353124971938399382721

noncomputable def hp754099 := BSN.sin_dyadic_bound_f 465092793 536870912 3 2 536870912 268435456 hp754096 hp708845 hp754097 hp754098 hp708848

noncomputable def hp754100 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 465092793) (BSN.sinEvenQ 536870912) 0 2 hp754096 hp708845 hp754097 rfl rfl rfl

noncomputable def hp754101 := hp754099 hp754097 409063255 rfl rfl rfl rfl rfl rfl rfl rfl (hp754100 rfl)

noncomputable def hp754102 := @BSN.binarySplit_of_base2 (BSN.sinOddP 465092793) (BSN.sinOddQ 536870912) 0 2 hp754098 hp708848 hp754097 rfl rfl rfl

noncomputable def hp754103 := nat_lit 17065120801335049168244458642427712959245576046839367804439224527349678080

noncomputable def hp754104 := nat_lit 4611703799468452369360328955084546237415813772230914558342157534560256

noncomputable def hp754105 := nat_lit 44686897435440275089185094007097682770782597376567113245198748364193202176

noncomputable def hp754106 := BSN.sin_dyadic_bound_f 510484636 536870912 3 2 536870912 268435456 hp754103 hp708845 hp754104 hp754105 hp708848

noncomputable def hp754107 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 510484636) (BSN.sinEvenQ 536870912) 0 2 hp754103 hp708845 hp754104 rfl rfl rfl

noncomputable def hp754108 := hp754106 hp754104 436964951 rfl rfl rfl rfl rfl rfl rfl rfl (hp754107 rfl)

noncomputable def hp754109 := @BSN.binarySplit_of_base2 (BSN.sinOddP 510484636) (BSN.sinOddQ 536870912) 0 2 hp754105 hp708848 hp754104 rfl rfl rfl

noncomputable def hp754110 := hp754095 hd4936 hd4938 hd4940 hd4942 hd4918 (hp754101 (hp754102 rfl) rfl rfl rfl rfl) (hp754108 (hp754109 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754111 := hp753971 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 264852463 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl rfl (hp754110 rfl rfl rfl rfl rfl) hp754054

noncomputable def hp754112 := nat_lit 86608314766151852156290863665281

noncomputable def hp754113 := BSN.sin_dyadic_bound_f 96469471 536870912 2 1 536870912 268435456 hp754112 hp708890 hp754112 hp754112 hp708891

noncomputable def hp754114 := @BSN.binarySplit_of_base (BSN.sinEvenP 96469471) (BSN.sinEvenQ 536870912) 0 1 hp754112 hp708890 hp754112 rfl rfl rfl

noncomputable def hp754115 := hp754113 hp754112 95951175 rfl rfl rfl rfl rfl rfl rfl rfl (hp754114 rfl)

noncomputable def hp754116 := @BSN.binarySplit_of_base (BSN.sinOddP 96469471) (BSN.sinOddQ 536870912) 0 1 hp754112 hp708891 hp754112 rfl rfl rfl

noncomputable def hp754117 := nat_lit 1478580502684238430093898662382248097476354995681878320894864356874242625

noncomputable def hp754118 := nat_lit 34637539531984592406152618056929056392412995173908163909185557613121

noncomputable def hp754119 := nat_lit 3872416665299477437096315106762367132061056320031780703411648919958309441

noncomputable def hp754120 := BSN.sin_dyadic_bound_f 276976791 536870912 3 2 536870912 268435456 hp754117 hp708845 hp754118 hp754119 hp708848

noncomputable def hp754121 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 276976791) (BSN.sinEvenQ 536870912) 0 2 hp754117 hp708845 hp754118 rfl rfl rfl

noncomputable def hp754122 := hp754120 hp754118 264852463 rfl rfl rfl rfl rfl rfl rfl rfl (hp754121 rfl)

noncomputable def hp754123 := @BSN.binarySplit_of_base2 (BSN.sinOddP 276976791) (BSN.sinOddQ 536870912) 0 2 hp754119 hp708848 hp754118 rfl rfl rfl

noncomputable def hp754124 := hp754111 hd4944 hd4946 hd4961 hd4963 hd4918 (hp754115 (hp754116 rfl) rfl rfl rfl rfl) (hp754122 (hp754123 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754125 := @hp753966 200817 268435456 (hp754124 rfl rfl rfl rfl rfl) (hp754124 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp754126 := @hp753964 Bool.true 552676513 268435456 200817 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 827572 1000)) (Enclosure.sfrac Bool.false 827572 1000) 11) hp754125

noncomputable def hp754127 := @Enclosure.Real.IsNear.mulLit_tf hp753955 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1))) 19809495 67108864 1

noncomputable def hp754128 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp753954 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754129 := @hp754128 1 1 0 1 19809495 67108864 1 67108864 19809495 67108864 1

noncomputable def hp754130 := @Enclosure.Real.IsNear.of_eq (hp753954 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754131 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 827572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754132 := @hp754130 (@Inv.inv Real Real.instInv (Real.sqrt hp753956)) Bool.false 19809495 67108864 1 67108864 (hp754131 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 827572 1000) 827572 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000))))

noncomputable def hp754133 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp753956)) Bool.false 19809495 67108864 1 67108864 19809495 67108864

noncomputable def hp754134 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp753956) Bool.false 227345500 67108864 6 67108864 56836375 16777216 3 33554432

noncomputable def hp754135 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 827572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754136 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 827572 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754137 := @hp754136 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 827572 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2209763513351

noncomputable def hp754138 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 827572 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 827572 1000 0

noncomputable def hp754139 := @hp754138 1 10680707 67108864 1 67108864 2209763513351 16777216000 206893 16777216000 (Enclosure.Real.IsNear.const Bool.false 827572 1000) hd4949

noncomputable def hp754140 := @hp754137 16777216000 206893 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 827572 1000) 827572 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000))) (hp754139 rfl)

noncomputable def hp754141 := @hp754135 2209763513351 16777216000 206893 16777216000 385090515 385090552 33554432 hp754140 rfl rfl rfl

noncomputable def hp754142 := @Enclosure.Real.IsNear.recentre' hp753956 Bool.false 770181067 67108864 37 67108864 770181067 67108864 37 67108864 (hp754141 rfl rfl rfl)

noncomputable def hp754143 := @Enclosure.Real.IsNear.sqrt_image hp753956 770181067 67108864 37 67108864 113672747 113672753 33554432 (hp754142 rfl) rfl rfl

noncomputable def hp754144 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp753956) 56836375 16777216 3 33554432 9904747 9904748 33554432 (hp754134 (hp754143 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp754145 := @hp754129 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp754132 (@hp754133 1 67108864 (hp754144 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp754146 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754147 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp754148 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1))) (hp754146 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754147 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp754149 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 827572 1000) 827572 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl

noncomputable def hp754150 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754151 := @hp754150 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754147 (Enclosure.sfrac Bool.false 1 16)))) 33920643

noncomputable def hp754152 := @hp754151 33554432 123 33554432 12733925 33554432 313878679 45675970560000 431942923913775 1125899906842624 1008451234037 120946279055360000

noncomputable def hp754153 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754154 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754155 := @hp754153 (@Neg.neg Real Real.instNeg hp754154) Bool.true 33920643 33554432 123 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754156 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754157 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp754158 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp754159 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 200958653) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp754160 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1))) Bool.false 28282416102372498566465

noncomputable def hp754161 := nat_lit 39939391616374655841214523

noncomputable def hp754162 := nat_lit 11529215046068469760000000000000

noncomputable def hp754163 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp754164 := @Enclosure.Real.IsNear.subLit_ff_p hp753956 (Enclosure.sfrac Bool.false 11 1) 770181067 67108864 37 67108864 11 1 0

noncomputable def hp754165 := @hp754163 500000000000000 31983563 67108864 37 67108864 28282416102372498566465 9444732965739290427392 hp754161 hp754162 hd4948 (@hp754164 1 31983563 31983563 67108864 37 67108864 (hp754142 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754166 := @hp754159 200958653 67108864 233 67108864 Bool.true 66384349 67108864 1 10890000 (@hp754160 9444732965739290427392 hp754161 hp754162 200958653 67108864 233 67108864 (hp754165 rfl) rfl) (Enclosure.sfrac_false_div 200958653 67108864)

noncomputable def hp754167 := nat_lit 13769384178020304128311296

noncomputable def hp754168 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 200958653) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp754167) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp754169 := BSN.sin_reduce_arg_pos_rat_q1 200958653 67108864 226375608064910080 72057594037927936 0 hp754167 hp617687 rfl rfl rfl rfl

noncomputable def hp754170 := nat_lit 9698542259068809094464971768755133369662528930976968666069281344992575286264445815040668742422842036429065339042696346623158336955104115478241

noncomputable def hp754171 := nat_lit 3150769270283680920884447360284599638023564015316483153788261606845723352203968987371725743582891379329065535355378048556174888418070241

noncomputable def hp754172 := nat_lit 48452024343544983976007789098835473746221055798869352114416511646804412306384792731738390613329195587289009813084256854040016066733584285093601

noncomputable def hp754173 := BSN.sin_dyadic_bound_f 195674718071 137438953472 4 3 67108864 21801270 hp754170 hp737934 hp754171 hp754172 hp737937

noncomputable def hp754174 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 195674718071) (BSN.sinEvenQ 137438953472) 0 3 hp754170 hp737934 hp754171 rfl rfl rfl

noncomputable def hp754175 := hp754173 hp754171 66384349 rfl rfl rfl rfl rfl rfl rfl rfl (hp754174 rfl)

noncomputable def hp754176 := @BSN.binarySplit_of_base3 (BSN.sinOddP 195674718071) (BSN.sinOddQ 137438953472) 0 3 hp754172 hp737937 hp754171 rfl rfl rfl

noncomputable def hp754177 := @BSN.sin_arg_round Bool.false 66384349 67108864 hp754167 hp617687 195674718071 137438953472 21801270 21780000 (hp754175 (hp754176 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754178 := hp754168 66384349 67108864 0 1000000000000000 21780000 10890000 hp754169 BSN.pi_near_15 hp754177 rfl rfl

noncomputable def hp754179 := @hp754157 66384349 67108864 162779929 45675970560000 (@hp754158 66384349 67108864 2604478864 730815528960000 66384349 67108864 162779929 45675970560000 (hp754166 (hp754178 rfl rfl) rfl rfl) rfl)

noncomputable def hp754180 := @hp754156 66384349 67108864 162779929 45675970560000 33920520 33920766 33554432 hp754179 rfl rfl rfl

noncomputable def hp754181 := @Enclosure.Real.IsNear.recentre' hp754154 Bool.false 67841286 67108864 246 67108864 33920643 33554432 123 33554432 (hp754180 rfl rfl rfl)

noncomputable def hp754182 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754147 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp754183 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754147 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 65768455)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp754184 := nat_lit 1242330991915311901797022013045

noncomputable def hp754185 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754147 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp754184

noncomputable def hp754186 := nat_lit 130877419322844115232898091441914481

noncomputable def hp754187 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754147 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp754188 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp754189 := @hp754188 (Enclosure.sfrac Bool.false 1 16) 1123432277427463 4503599627370496 4849812999 4503599627370496 1 16 0

noncomputable def hp754190 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)) 1022948302174969

noncomputable def hp754191 := @hp754190 4503599627370496 2366785031 4503599627370496 31983563 67108864 37 67108864 75392263919089884332032 1123432277427463 4503599627370496 4849812999

noncomputable def hp754192 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)) 31983563 67108864 37

noncomputable def hp754193 := @hp754192 67108864 31983563 67108864 37 67108864 1022948302174969 4503599627370496 2366785031 4503599627370496 (@hp754164 1 31983563 31983563 67108864 37 67108864 (hp754142 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754194 := hp754193 (@hp754164 1 31983563 31983563 67108864 37 67108864 (hp754142 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754195 := @hp754191 4503599627370496 (hp754194 rfl) (@hp754164 1 31983563 31983563 67108864 37 67108864 (hp754142 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754196 := @hp754187 500000000000000 1404907254138119 4503599627370496 4849812999 4503599627370496 hp754184 hp627574 hp754186 hp738055 hd4948 (@hp754189 1 22478516066209904 1404907254138119 4503599627370496 4849812999 4503599627370496 (hp754195 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp754197 := @hp754183 65768455 33554432 455 67108864 Bool.true 12733925 33554432 1 10890000 (@hp754185 hp627574 hp754186 hp738055 65768455 33554432 455 67108864 (hp754196 rfl) rfl) (Enclosure.sfrac_true_div 65768455 33554432)

noncomputable def hp754198 := nat_lit 605339345307993560926888392841760072937282507643979608166771785517257781198250507866708261889390625

noncomputable def hp754199 := nat_lit 6549553242920856472903429812101680565927286285655457393775887291327638412030269100801025390625

noncomputable def hp754200 := nat_lit 3651037429982615903404655868315868326400166223807055855010516753809397773812848591573491373466990625

noncomputable def hp754201 := BSN.cos_dyadic_bound_t 65768455 33554432 4 3 33554432 10890000 hp754198 hp681868 hp754199 hp754200 hp681871

noncomputable def hp754202 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 65768455) (BSN.cosEvenQ 33554432) 0 3 hp754198 hp681868 hp754199 rfl rfl rfl

noncomputable def hp754203 := hp754201 hp754199 12733925 rfl rfl rfl rfl rfl rfl rfl rfl (hp754202 rfl)

noncomputable def hp754204 := @BSN.binarySplit_of_base3 (BSN.cosOddP 65768455) (BSN.cosOddQ 33554432) 0 3 hp754200 hp681871 hp754199 rfl rfl rfl

noncomputable def hp754205 := hp754197 (BSN.cos_neg_of_bound 65768455 33554432 Bool.true 12733925 33554432 1 10890000 (hp754203 (hp754204 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp754206 := hp754152 (hp754155 (@Enclosure.Real.IsNear.neg hp754154 Bool.false 33920643 33554432 123 33554432 (hp754181 rfl))) (@hp754182 12733925 33554432 5022058864 730815528960000 12733925 33554432 313878679 45675970560000 (hp754205 rfl) rfl)

noncomputable def hp754207 := @hp754127 67108864 431942923913775 1125899906842624 1008451234037 120946279055360000 8556571191555306293625 75557863725914323419136 1281491891560372185653 hp753952 (hp754145 rfl) (@hp754148 Bool.false 431942923913775 1125899906842624 1008451234037 120946279055360000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp753956 (Enclosure.sfrac Bool.false 11 1)) (hp754149 rfl (hp753959 rfl rfl))) (hp754206 rfl))

noncomputable def hp754208 := @hp753953 389890594628524038105653 hp753952 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 827572 1000))) (@hp753958 389890594628524038105653 hp753952 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 827572 1000) 11 (hp753959 rfl rfl)) (@hp753962 389890594628524038105653 hp753952 hp754126 (hp754207 rfl) rfl rfl))

theorem hd5026 : hp753951 hp753952 := hp754208

noncomputable def hp754209 := nat_lit 38659642500792401703972671

noncomputable def hp754210 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 828859 1000)) Bool.false 97118063959614914181383 75557863725914323419136 hp754209

noncomputable def hp754211 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 828859 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 828859 1000)) Bool.false 97118063959614914181383 75557863725914323419136

noncomputable def hp754212 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 828859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754213 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp754212 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754214 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 828859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754215 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp754213 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp754216 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 828859 1000)) hp754215 Bool.false 97118063959614914181383 75557863725914323419136

noncomputable def hp754217 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 828859 1000) 828859 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl

noncomputable def hp754218 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp754213 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp754219 := nat_lit 26069931784836395072680412315648

noncomputable def hp754220 := @hp754218 314692307 268435456 201131 268435456 8540054175767306057991 75557863725914323419136 127185553341560042532671 hp738860 hp754219 97118063959614914181383 75557863725914323419136

noncomputable def hp754221 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) 11)

noncomputable def hp754222 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) 11) hp754221

noncomputable def hp754223 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) 11)

noncomputable def hp754224 := @hp754223 314692307 536870912 201131 536870912 314692307 536870912 201131 536870912 337898291716947968 314692307 268435456

noncomputable def hp754225 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp754226 := hp754225 BSN.quadSignNeg 9 10 11 828859 1000 191 241 536870912 268435456 9007199254740992

noncomputable def hp754227 := hp754226 Bool.false 863553822155 3777 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp754228 := hp754227 Bool.false 386345768 172665 Bool.true 1039846 Bool.true 247402009 28296951008113761 1 Bool.false 1039845

noncomputable def hp754229 := hp754228 Bool.false Bool.false 238738252 Bool.true Bool.false 314692307 201131 BSN.abs_quadSignPos (BSN.cos_quad_nat3 191 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 1039845 536870912) BSN.abs_quadSignNeg

noncomputable def hp754230 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp754231 := hp754230 BSN.quadSignPos 7 8 9 828859 1000 73 135 536870912 268435456 9007199254740992

noncomputable def hp754232 := hp754231 Bool.false 863553822155 3777 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp754233 := hp754232 Bool.false 353987650 141015 Bool.true 215481495 Bool.true 342255846 28296951008113761 1 Bool.false 209742442

noncomputable def hp754234 := hp754233 Bool.true Bool.false 319539819 Bool.false Bool.false 386345768 172665 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 73 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 209742442 536870912) BSN.abs_quadSignPos

noncomputable def hp754235 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp754236 := hp754235 BSN.quadSignNeg 5 6 7 828859 1000 78 2 536870912 268435456 9007199254740992

noncomputable def hp754237 := hp754236 Bool.false 863553822155 3777 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp754238 := hp754237 Bool.false 561745997 104791 Bool.false 459708526 Bool.true 670651562 28296951008113761 1 Bool.false 351788295

noncomputable def hp754239 := hp754238 Bool.true Bool.false 169702128 Bool.true Bool.false 353987650 141015 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 351788295 536870912) BSN.abs_quadSignNeg

noncomputable def hp754240 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp754241 := hp754240 BSN.quadSignNeg 3 4 5 828859 1000 292 174 536870912 268435456 9007199254740992

noncomputable def hp754242 := hp754241 Bool.false 863553822155 3777 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp754243 := hp754242 Bool.false 462521023 61938 Bool.false 418369647 Bool.false 632811296 28296951008113761 1 Bool.false 381942741

noncomputable def hp754244 := hp754243 Bool.false Bool.false 205151162 Bool.true Bool.false 561745997 104791 BSN.abs_quadSignPos (BSN.cos_quad_nat0 292 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 381942741 536870912) BSN.abs_quadSignNeg

noncomputable def hp754245 := hp754235 BSN.quadSignPos 1 2 3 828859 1000 658 444 536870912 268435456 9007199254740992

noncomputable def hp754246 := hp754245 Bool.false 863553822155 3777 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp754247 := hp754246 Bool.false 536870584 3834 Bool.false 208895987 Bool.false 250232380 28296951008113761 1 Bool.false 496740454

noncomputable def hp754248 := hp754247 Bool.true Bool.false 479603105 Bool.false Bool.false 462521023 61938 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 658 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 496740454 536870912) BSN.abs_quadSignPos

noncomputable def hp754249 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) 1) Bool.false

noncomputable def hp754250 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)))

noncomputable def hp754251 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000))) Bool.false 67108823 67108864

noncomputable def hp754252 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 107944227769) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 107944227769 67108864

noncomputable def hp754253 := nat_lit 84560244707057273742861461869614290018365286889135788785789

noncomputable def hp754254 := nat_lit 52571055248780895738678310072141459559384407024336896000

noncomputable def hp754255 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) Bool.false hp754253 hp754254 41828418304990422719

noncomputable def hp754256 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 828859 4000) (Real.log (Enclosure.sfrac Bool.false 2748029967524 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1657718))))))

noncomputable def hp754257 := nat_lit 187778093513941310562583939983520000

noncomputable def hp754258 := nat_lit 933849535456603798498745839966898422080

noncomputable def hp754259 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp754256 (Enclosure.sfrac Bool.false 828859 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 828859 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp754257 hp754258)) Bool.false

noncomputable def hp754260 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 828859 1000) 828859 1000 2748029967524 16000000 1657718

noncomputable def hp754261 := hp754260 4000 2000 hp754257 hp754258 (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl rfl rfl rfl

noncomputable def hp754262 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp754256 (Enclosure.sfrac Bool.false 828859 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 828859 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp754257 hp754258) 28976061626177450208381 18014398509481984000

noncomputable def hp754263 := nat_lit 27059278306258327597715667798276572805876891804523452411452480

noncomputable def hp754264 := @hp754262 41828418304990422719 hp737908 hp754257 hp754258 0 1 hp754263 hp754253 hp754254 41828418304990422719 hp737908

noncomputable def hp754265 := @Enclosure.Real.IsNear.subLit_ff_p (hp754256 (Enclosure.sfrac Bool.false 828859 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 828859 2000) (Real.log Real.pi)) 300178155292853033985 144115188075855872 3486917615070389 1452000000000000000000

noncomputable def hp754266 := nat_lit 15556404631414090767208097513472

noncomputable def hp754267 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 828859 4000) (Real.log (Enclosure.sfrac Bool.false 2748029967524 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1657718))))))

noncomputable def hp754268 := @hp754267 (Enclosure.sfrac Bool.false 828859 2000) 44987967578691993136253 18014398509481984000 3486917615070389 1452000000000000000000 828859 2000 0

noncomputable def hp754269 := nat_lit 75044538823213258496250000

noncomputable def hp754270 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 828859 4000) (Real.log (Enclosure.sfrac Bool.false 2748029967524 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1657718))))) 44995039099742989128253

noncomputable def hp754271 := nat_lit 101303897011776607736175319833320095744

noncomputable def hp754272 := @hp754270 18014398509481984000 10360752844666667 4356000000000000000000 883940131374499 2251799813685248 200000001089 8712000000000000000 hp754271 44987967578691993136253 18014398509481984000 3486917615070389

noncomputable def hp754273 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 828859 4000) (Real.log (Enclosure.sfrac Bool.false 2748029967524 16000000)) 828859 4000 0 1 54285516716043367 4503599627370496

noncomputable def hp754274 := nat_lit 116577259470933789891362816

noncomputable def hp754275 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2748029967524) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp754274 hp617687

noncomputable def hp754276 := BSN.log_rat_reduce_isNear 2748029967524 16000000 17 5496059935048 4194304000000 72559189 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp754277 := nat_lit 287020255235012980939135520855253324335316690381204772275069973694884967451075905421872177486566375096320

noncomputable def hp754278 := nat_lit 1745452842677023181229994948560265294474706609329897977920122254970136757057552601790287617412255186944

noncomputable def hp754279 := nat_lit 3382095488322449810425226888903115466354520120375506071637916300288243128032142931772812512788480

noncomputable def hp754280 := BSN.log_dyadic_bound 650877967524 4845181967524 5 4 hp754277 268435456 87120000 hp754278 hp754279 72559189 5496059935048

noncomputable def hp754281 := hp754280 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp754282 := @BSN.binarySplit_of_base4 (BSN.artanhP 650877967524) (BSN.artanhQ 4845181967524) 0 4 hp754278 hp754277 hp754279 rfl rfl rfl

noncomputable def hp754283 := hp754276 rfl rfl rfl rfl (hp754281 (hp754282 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp754284 := @hp754273 12500018513 1089000000000000000 44995039099742989128253 18014398509481984000 10360752844666667 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 828859 4000) (BSN.isNear_log_sfrac 2748029967524 16000000 54285516716043367 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp754275 1000001481040000 87120000000000000000000 54285516716043367 4503599627370496 12500018513 1089000000000000000 (hp754283 rfl rfl rfl) rfl)) rfl

noncomputable def hp754285 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1657718)))) 1 4

noncomputable def hp754286 := @hp754285 0 1 883940131374499 562949953421312 200000001089 2178000000000000000 883940131374499 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp754287 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1657718))) 884279719003555 562949953421312 1

noncomputable def hp754288 := @hp754287 2000000000000000 20241 33554432 1 10890000 29660109030276693229568 883940131374499 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp754289 := BSN.arctan_dyadic_bound_f 1000 1657718 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp754290 := hp754289 1 20241 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1657718) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1657718) 0 0 rfl)

noncomputable def hp754291 := hp754286 (hp754288 (hp754290 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp754292 := @hp754265 31837104951699 67108864000 2486577 536870912000 hp754266 28976061626177450208381 18014398509481984000 41828418304990422719 hp737908 (@hp754268 1 hp754269 300178155292853033985 144115188075855872 3486917615070389 1452000000000000000000 (@hp754272 1452000000000000000000 hp754284 hp754291 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 828859 2000) rfl rfl)

noncomputable def hp754293 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 828859 2000) (Real.log Real.pi) 828859 2000 0 1 38410761 33554432

noncomputable def hp754294 := hp754292 (@hp754293 3 268435456 31837104951699 67108864000 2486577 536870912000 (Enclosure.Real.IsNear.const Bool.false 828859 2000) hd4909 rfl) rfl

noncomputable def hp754295 := @hp754255 hp737908 107944227769 67108864 473 67108864 (@hp754259 hp754253 hp754254 41828418304990422719 hp737908 (hp754261 rfl rfl rfl rfl rfl) (hp754264 (hp754294 rfl) (Enclosure.Real.IsNear.const Bool.true hp754257 hp754258) rfl rfl)) rfl

noncomputable def hp754296 := nat_lit 15181164512562230023159808

noncomputable def hp754297 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 107944227769) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp754296) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp754298 := BSN.sin_reduce_arg_pos_rat_q3 107944227769 67108864 226375608064910080 72057594037927936 255 hp754296 hp617687 rfl rfl rfl rfl

noncomputable def hp754299 := nat_lit 14340036609448543645913991162158355512835394865550667148671883541699504898435270346163557333599719227332273579566489642265121508649563493290625

noncomputable def hp754300 := nat_lit 10164907534268476385167876566172287500482901441446422773763982940574252916456321408281335238668492537089534510373747650481868574462890625

noncomputable def hp754301 := nat_lit 71611335804234622786401867370212965391992836541217819930556768596274153639763060740300013948475362038723819433820503118014754903283535614890625

noncomputable def hp754302 := BSN.sin_dyadic_bound_f 215737323295 137438953472 4 3 67108864 21801270 hp754299 hp737934 hp754300 hp754301 hp737937

noncomputable def hp754303 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215737323295) (BSN.sinEvenQ 137438953472) 0 3 hp754299 hp737934 hp754300 rfl rfl rfl

noncomputable def hp754304 := hp754302 hp754300 67108823 rfl rfl rfl rfl rfl rfl rfl rfl (hp754303 rfl)

noncomputable def hp754305 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215737323295) (BSN.sinOddQ 137438953472) 0 3 hp754301 hp737937 hp754300 rfl rfl rfl

noncomputable def hp754306 := @BSN.sin_arg_round Bool.false 67108823 67108864 hp754296 hp617687 215737323295 137438953472 21801270 21780000 (hp754304 (hp754305 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754307 := hp754297 67108823 67108864 255 1000000000000000 21780000 10890000 hp754298 BSN.pi_near_15 hp754306 rfl rfl

noncomputable def hp754308 := @hp754252 473 67108864 Bool.false 67108823 67108864 1 10890000 hp754295 (Enclosure.sfrac_false_div 107944227769 67108864) (hp754307 rfl rfl) rfl

noncomputable def hp754309 := @hp754249 67108823 67108864 326129929 45675970560000 536870584 536870912 3834 536870912 (@hp754250 Bool.false 67108823 67108864 326129929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000)) (@hp754251 5218078864 730815528960000 67108823 67108864 326129929 45675970560000 (hp754308 rfl) rfl))

noncomputable def hp754310 := @hp754255 hp737908 863553822155 536870912 3777 536870912 (@hp754259 hp754253 hp754254 41828418304990422719 hp737908 (hp754261 rfl rfl rfl rfl rfl) (hp754264 (hp754294 rfl) (Enclosure.Real.IsNear.const Bool.true hp754257 hp754258) rfl rfl)) rfl

noncomputable def hp754311 := hp754248 (BSN.cos_quad_nat0 444 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 479603105 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl rfl (hp754309 rfl) hp754310

noncomputable def hp754312 := nat_lit 265775590805789090175350491378461283012127355523901353624317067357524001

noncomputable def hp754313 := nat_lit 3626108345089474826038590755022443776439406903726488290907189874721

noncomputable def hp754314 := nat_lit 797319520200677091576399396953873804148829187757896607896369387692822561

noncomputable def hp754315 := BSN.cos_dyadic_bound_f 208895987 536870912 3 2 536870912 268435456 hp754312 hp708868 hp754313 hp754314 hp708870

noncomputable def hp754316 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 208895987) (BSN.cosEvenQ 536870912) 0 2 hp754312 hp708868 hp754313 rfl rfl rfl

noncomputable def hp754317 := hp754315 hp754313 496740454 rfl rfl rfl rfl rfl rfl rfl rfl (hp754316 rfl)

noncomputable def hp754318 := @BSN.binarySplit_of_base2 (BSN.cosOddP 208895987) (BSN.cosOddQ 536870912) 0 2 hp754314 hp708870 hp754313 rfl rfl rfl

noncomputable def hp754319 := nat_lit 547236435204881799538852084458710943629552864745858447646557974732800000

noncomputable def hp754320 := nat_lit 15372625690225649268594500520800686728231545786944794169369600000000

noncomputable def hp754321 := nat_lit 1641678560363264947318019064375091229515202131146001453351335184998400000

noncomputable def hp754322 := BSN.cos_dyadic_bound_f 250232380 536870912 3 2 536870912 268435456 hp754319 hp708868 hp754320 hp754321 hp708870

noncomputable def hp754323 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 250232380) (BSN.cosEvenQ 536870912) 0 2 hp754319 hp708868 hp754320 rfl rfl rfl

noncomputable def hp754324 := hp754322 hp754320 479603105 rfl rfl rfl rfl rfl rfl rfl rfl (hp754323 rfl)

noncomputable def hp754325 := @BSN.binarySplit_of_base2 (BSN.cosOddP 250232380) (BSN.cosOddQ 536870912) 0 2 hp754321 hp708870 hp754320 rfl rfl rfl

noncomputable def hp754326 := hp754311 hd4911 hd4913 hd4915 hd4917 hd4918 (hp754317 (hp754318 rfl) rfl rfl rfl rfl) (hp754324 (hp754325 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754327 := hp754244 (BSN.cos_quad_nat2 174 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 205151162 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl rfl (hp754326 rfl rfl rfl rfl rfl) hp754310

noncomputable def hp754328 := nat_lit 4276857441051308626233331728607069597517918168902505787783350832584743041

noncomputable def hp754329 := nat_lit 938601727411806374402907843532720468863239631468643154497656177580161

noncomputable def hp754330 := nat_lit 12828695119699102265951189370134143351616028027444580077041057185399068801

noncomputable def hp754331 := BSN.cos_dyadic_bound_f 418369647 536870912 3 2 536870912 268435456 hp754328 hp708868 hp754329 hp754330 hp708870

noncomputable def hp754332 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 418369647) (BSN.cosEvenQ 536870912) 0 2 hp754328 hp708868 hp754329 rfl rfl rfl

noncomputable def hp754333 := hp754331 hp754329 381942741 rfl rfl rfl rfl rfl rfl rfl rfl (hp754332 rfl)

noncomputable def hp754334 := @BSN.binarySplit_of_base2 (BSN.cosOddP 418369647) (BSN.cosOddQ 536870912) 0 2 hp754330 hp708870 hp754329 rfl rfl rfl

noncomputable def hp754335 := nat_lit 22114666447926577804914966439759368523455469285721460335148420729491794217356888565880822085820557835064831901696

noncomputable def hp754336 := nat_lit 4123734301021736804708278193387219821242027626046297290727543239247478597913226714608218388277596117794816

noncomputable def hp754337 := nat_lit 134059641338777143571333398156001485647757524891898369073945017198868330149480791284456262265574519344860737044480

noncomputable def hp754338 := BSN.cos_dyadic_bound_f 632811296 536870912 4 3 536870912 268435456 hp754335 hp716712 hp754336 hp754337 hp716714

noncomputable def hp754339 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 632811296) (BSN.cosEvenQ 536870912) 0 3 hp754335 hp716712 hp754336 rfl rfl rfl

noncomputable def hp754340 := hp754338 hp754336 205151162 rfl rfl rfl rfl rfl rfl rfl rfl (hp754339 rfl)

noncomputable def hp754341 := @BSN.binarySplit_of_base3 (BSN.cosOddP 632811296) (BSN.cosOddQ 536870912) 0 3 hp754337 hp716714 hp754336 rfl rfl rfl

noncomputable def hp754342 := hp754327 hd4920 hd4922 hd4924 hd4926 hd4918 (hp754333 (hp754334 rfl) rfl rfl rfl rfl) (hp754340 (hp754341 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754343 := hp754239 (BSN.cos_quad_nat2 2 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 169702128 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl rfl (hp754342 rfl rfl rfl rfl rfl) hp754310

noncomputable def hp754344 := nat_lit 6235308734367008434679807319245887842469407158595023265713314634699981056

noncomputable def hp754345 := nat_lit 1994621370833591419440821502983443432004861340401536897541373224632576

noncomputable def hp754346 := nat_lit 18701936960359358121200540314731696640544211753104266723344861157650678016

noncomputable def hp754347 := BSN.cos_dyadic_bound_f 459708526 536870912 3 2 536870912 268435456 hp754344 hp708868 hp754345 hp754346 hp708870

noncomputable def hp754348 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 459708526) (BSN.cosEvenQ 536870912) 0 2 hp754344 hp708868 hp754345 rfl rfl rfl

noncomputable def hp754349 := hp754347 hp754345 351788295 rfl rfl rfl rfl rfl rfl rfl rfl (hp754348 rfl)

noncomputable def hp754350 := @BSN.binarySplit_of_base2 (BSN.cosOddP 459708526) (BSN.cosOddQ 536870912) 0 2 hp754346 hp708870 hp754345 rfl rfl rfl

noncomputable def hp754351 := nat_lit 27906259806807284133424306765745633478410918002708570436311730065160532937322539181815782400672858825305283956736

noncomputable def hp754352 := nat_lit 8278721732494658624660447377604832309625582235901056467446919059722302298071586657062736077572449500205056

noncomputable def hp754353 := nat_lit 169134580004406536795885439764458368417245249272072385008369570835007623540302237874369381075505618927432869416960

noncomputable def hp754354 := BSN.cos_dyadic_bound_f 670651562 536870912 4 3 536870912 268435456 hp754351 hp716712 hp754352 hp754353 hp716714

noncomputable def hp754355 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 670651562) (BSN.cosEvenQ 536870912) 0 3 hp754351 hp716712 hp754352 rfl rfl rfl

noncomputable def hp754356 := hp754354 hp754352 169702128 rfl rfl rfl rfl rfl rfl rfl rfl (hp754355 rfl)

noncomputable def hp754357 := @BSN.binarySplit_of_base3 (BSN.cosOddP 670651562) (BSN.cosOddQ 536870912) 0 3 hp754353 hp716714 hp754352 rfl rfl rfl

noncomputable def hp754358 := hp754343 hd4928 hd4930 hd4932 hd4934 hd4918 (hp754349 (hp754350 rfl) rfl rfl rfl rfl) (hp754356 (hp754357 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754359 := hp754234 (BSN.cos_quad_nat3 135 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 319539819 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl rfl (hp754358 rfl rfl rfl rfl rfl) hp754310

noncomputable def hp754360 := nat_lit 2155956132649419348560613596750625

noncomputable def hp754361 := BSN.sin_dyadic_bound_f 215481495 536870912 2 1 536870912 268435456 hp754360 hp708890 hp754360 hp754360 hp708891

noncomputable def hp754362 := @BSN.binarySplit_of_base (BSN.sinEvenP 215481495) (BSN.sinEvenQ 536870912) 0 1 hp754360 hp708890 hp754360 rfl rfl rfl

noncomputable def hp754363 := hp754361 hp754360 209742442 rfl rfl rfl rfl rfl rfl rfl rfl (hp754362 rfl)

noncomputable def hp754364 := @BSN.binarySplit_of_base (BSN.sinOddP 215481495) (BSN.sinOddQ 536870912) 0 1 hp754360 hp708891 hp754360 rfl rfl rfl

noncomputable def hp754365 := nat_lit 3447374808326797157506278639428936629004837143747361473140295522966053120

noncomputable def hp754366 := nat_lit 188281218251664947509596037132842395716287482702238520026382867374336

noncomputable def hp754367 := nat_lit 9028533947454918431172857090634714188276747101509190710144540797411533056

noncomputable def hp754368 := BSN.sin_dyadic_bound_f 342255846 536870912 3 2 536870912 268435456 hp754365 hp708845 hp754366 hp754367 hp708848

noncomputable def hp754369 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 342255846) (BSN.sinEvenQ 536870912) 0 2 hp754365 hp708845 hp754366 rfl rfl rfl

noncomputable def hp754370 := hp754368 hp754366 319539819 rfl rfl rfl rfl rfl rfl rfl rfl (hp754369 rfl)

noncomputable def hp754371 := @BSN.binarySplit_of_base2 (BSN.sinOddP 342255846) (BSN.sinOddQ 536870912) 0 2 hp754367 hp708848 hp754366 rfl rfl rfl

noncomputable def hp754372 := hp754359 hd4936 hd4938 hd4940 hd4942 hd4918 (hp754363 (hp754364 rfl) rfl rfl rfl rfl) (hp754370 (hp754371 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754373 := hp754229 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 238738252 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl rfl (hp754372 rfl rfl rfl rfl rfl) hp754310

noncomputable def hp754374 := BSN.sin_dyadic_bound_f 1039846 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp754375 := hp754374 1 1039845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1039846) (BSN.sinEvenQ 536870912) 0 0 rfl)

noncomputable def hp754376 := hp754375 (@BSN.binarySplit_of_le (BSN.sinOddP 1039846) (BSN.sinOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp754377 := nat_lit 941197246625565648109093040223656898056120499648574309749762079732031425

noncomputable def hp754378 := nat_lit 14035431713672362072059293155615061982264607928302756872063007350721

noncomputable def hp754379 := nat_lit 2465017683796564085032841295063516118141868118285810702023964963952943041

noncomputable def hp754380 := BSN.sin_dyadic_bound_f 247402009 536870912 3 2 536870912 268435456 hp754377 hp708845 hp754378 hp754379 hp708848

noncomputable def hp754381 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 247402009) (BSN.sinEvenQ 536870912) 0 2 hp754377 hp708845 hp754378 rfl rfl rfl

noncomputable def hp754382 := hp754380 hp754378 238738252 rfl rfl rfl rfl rfl rfl rfl rfl (hp754381 rfl)

noncomputable def hp754383 := @BSN.binarySplit_of_base2 (BSN.sinOddP 247402009) (BSN.sinOddQ 536870912) 0 2 hp754379 hp708848 hp754378 rfl rfl rfl

noncomputable def hp754384 := hp754373 hd4944 hd4946 hd4961 hd4963 hd4918 hp754376 (hp754382 (hp754383 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp754385 := @hp754222 Bool.false 314692307 268435456 201131 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 828859 1000)) (Enclosure.sfrac Bool.false 828859 1000) 11) (@hp754224 201131 268435456 (hp754384 rfl rfl rfl rfl) (hp754384 rfl rfl rfl rfl) rfl rfl)

noncomputable def hp754386 := @Enclosure.Real.IsNear.mulLit_tf hp754213 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1))) 19801801 67108864 1

noncomputable def hp754387 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp754212 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754388 := @hp754387 1 1 0 1 19801801 67108864 1 67108864 19801801 67108864 1

noncomputable def hp754389 := @Enclosure.Real.IsNear.of_eq (hp754212 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp754390 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 828859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754391 := @hp754389 (@Inv.inv Real Real.instInv (Real.sqrt hp754214)) Bool.false 19801801 67108864 1 67108864 (hp754390 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 828859 1000) 828859 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000))))

noncomputable def hp754392 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp754214)) Bool.false 19801801 67108864 1 67108864 19801801 67108864

noncomputable def hp754393 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp754214) Bool.false 227433838 67108864 6 67108864 113716919 33554432 3 33554432

noncomputable def hp754394 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 828859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754395 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 828859 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp754396 := @hp754395 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 828859 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8852800123313

noncomputable def hp754397 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 828859 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 828859 1000 0

noncomputable def hp754398 := @hp754397 1 10680707 67108864 1 67108864 8852800123313 67108864000 828859 67108864000 (Enclosure.Real.IsNear.const Bool.false 828859 1000) hd4949

noncomputable def hp754399 := @hp754396 67108864000 828859 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 828859 1000) 828859 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000))) (hp754398 rfl)

noncomputable def hp754400 := @hp754394 8852800123313 67108864000 828859 67108864000 385389836 385389873 33554432 hp754399 rfl rfl rfl

noncomputable def hp754401 := @Enclosure.Real.IsNear.recentre' hp754214 Bool.false 770779709 67108864 37 67108864 770779709 67108864 37 67108864 (hp754400 rfl rfl rfl)

noncomputable def hp754402 := @Enclosure.Real.IsNear.sqrt_image hp754214 770779709 67108864 37 67108864 113716916 113716922 33554432 (hp754401 rfl) rfl rfl

noncomputable def hp754403 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp754214) 113716919 33554432 3 33554432 9900900 9900901 33554432 (hp754393 (hp754402 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp754404 := @hp754388 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp754391 (@hp754392 1 67108864 (hp754403 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp754405 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754406 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp754407 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1))) (hp754405 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754406 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp754408 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 828859 1000) 828859 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl

noncomputable def hp754409 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754410 := @hp754409 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754406 (Enclosure.sfrac Bool.false 1 16)))) 33693927

noncomputable def hp754411 := @hp754410 33554432 61 16777216 12799833 33554432 79320451 11418992640000 431276638714191 1125899906842624 400506528646153 47894726505922560000

noncomputable def hp754412 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754413 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754414 := @hp754412 (@Neg.neg Real Real.instNeg hp754413) Bool.true 33693927 33554432 61 16777216 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754415 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp754416 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp754417 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp754418 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 204720031) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false

noncomputable def hp754419 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1))) Bool.false 28811783081916224738775

noncomputable def hp754420 := nat_lit 998484790414508691654387139

noncomputable def hp754421 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp754422 := @Enclosure.Real.IsNear.subLit_ff_p hp754214 (Enclosure.sfrac Bool.false 11 1) 770779709 67108864 37 67108864 11 1 0

noncomputable def hp754423 := @hp754421 500000000000000 32582205 67108864 37 67108864 28811783081916224738775 9444732965739290427392 hp754420 hp738031 hd4948 (@hp754422 1 32582205 32582205 67108864 37 67108864 (hp754401 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754424 := @hp754418 204720031 67108864 117 33554432 Bool.true 66831029 67108864 1 10890000 (@hp754419 9444732965739290427392 hp754420 hp738031 204720031 67108864 117 33554432 (hp754423 rfl) rfl) (Enclosure.sfrac_false_div 204720031 67108864)

noncomputable def hp754425 := nat_lit 14311455875914690736422912

noncomputable def hp754426 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 204720031) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp754425) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp754427 := BSN.sin_reduce_arg_pos_rat_q1 204720031 67108864 226375608064910080 72057594037927936 0 hp754425 hp617687 rfl rfl rfl rfl

noncomputable def hp754428 := nat_lit 11320930245874146688806785175775935044182095382360844004690548854364325875649669399872254260839259730492739786902261132700148775066536106790625

noncomputable def hp754429 := nat_lit 5007813937172754933339588730645355220639423250980229347000846291156952090005073672986047241110335832689274742213888436593484472900390625

noncomputable def hp754430 := nat_lit 56549235633062629701714252506330862572203491280075740147227861412809436729641202513513306793512991109910781732816670538419814301040484932390625

noncomputable def hp754431 := BSN.sin_dyadic_bound_f 203378020215 137438953472 4 3 67108864 21801270 hp754428 hp737934 hp754429 hp754430 hp737937

noncomputable def hp754432 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 203378020215) (BSN.sinEvenQ 137438953472) 0 3 hp754428 hp737934 hp754429 rfl rfl rfl

noncomputable def hp754433 := hp754431 hp754429 66831029 rfl rfl rfl rfl rfl rfl rfl rfl (hp754432 rfl)

noncomputable def hp754434 := @BSN.binarySplit_of_base3 (BSN.sinOddP 203378020215) (BSN.sinOddQ 137438953472) 0 3 hp754430 hp737937 hp754429 rfl rfl rfl

noncomputable def hp754435 := @BSN.sin_arg_round Bool.false 66831029 67108864 hp754425 hp617687 203378020215 137438953472 21801270 21780000 (hp754433 (hp754434 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp754436 := hp754426 66831029 67108864 0 1000000000000000 21780000 10890000 hp754427 BSN.pi_near_15 hp754435 rfl rfl

noncomputable def hp754437 := @hp754416 66831029 67108864 81730277 22837985280000 (@hp754417 66831029 67108864 1307684432 365407764480000 66831029 67108864 81730277 22837985280000 (hp754424 (hp754436 rfl rfl) rfl rfl) rfl)

noncomputable def hp754438 := @hp754415 66831029 67108864 81730277 22837985280000 33693805 33694049 33554432 hp754437 rfl rfl rfl

noncomputable def hp754439 := @Enclosure.Real.IsNear.recentre' hp754413 Bool.false 67387854 67108864 244 67108864 33693927 33554432 61 16777216 (hp754438 rfl rfl rfl)

noncomputable def hp754440 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754406 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp754441 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754406 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 131679447)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp754442 := nat_lit 1243677222963521633650918884805

noncomputable def hp754443 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754406 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp754442

noncomputable def hp754444 := nat_lit 132072889186328742548323985837944861

noncomputable def hp754445 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp754406 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp754446 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp754447 := @hp754446 (Enclosure.sfrac Bool.false 1 16) 1124954681503095 4503599627370496 4894112507 4503599627370496 1 16 0

noncomputable def hp754448 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)) 1061600082662025

noncomputable def hp754449 := @hp754448 4503599627370496 2411084539 4503599627370496 32582205 67108864 37 67108864 75494430727154517934080 1124954681503095 4503599627370496 4894112507

noncomputable def hp754450 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)) 32582205 67108864 37

noncomputable def hp754451 := @hp754450 67108864 32582205 67108864 37 67108864 1061600082662025 4503599627370496 2411084539 4503599627370496 (@hp754422 1 32582205 32582205 67108864 37 67108864 (hp754401 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754452 := hp754451 (@hp754422 1 32582205 32582205 67108864 37 67108864 (hp754401 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754453 := @hp754449 4503599627370496 (hp754452 rfl) (@hp754422 1 32582205 32582205 67108864 37 67108864 (hp754401 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp754454 := @hp754445 500000000000000 1406429658213751 4503599627370496 4894112507 4503599627370496 hp754442 hp627574 hp754444 hp738055 hd4948 (@hp754447 1 22502874531420016 1406429658213751 4503599627370496 4894112507 4503599627370496 (hp754453 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp754455 := @hp754441 131679447 67108864 115 16777216 Bool.true 12799833 33554432 1 10890000 (@hp754443 hp627574 hp754444 hp738055 131679447 67108864 115 16777216 (hp754454 rfl) rfl) (Enclosure.sfrac_true_div 131679447 67108864)

noncomputable def hp754456 := nat_lit 2490329116105521330304048221230560042687964568555619726421027150262416425563023428721608146574888077921

noncomputable def hp754457 := nat_lit 27177901990524587556915769477442503695793504323752949066894307473903323829836573713447924748716641

noncomputable def hp754458 := nat_lit 15019766460497168392287743924784543200930673783538123744143177102864764296429150179493262681427768969825

noncomputable def hp754459 := BSN.cos_dyadic_bound_t 131679447 67108864 4 3 33554432 10890000 hp754456 hp745658 hp754457 hp754458 hp745661

noncomputable def hp754460 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 131679447) (BSN.cosEvenQ 67108864) 0 3 hp754456 hp745658 hp754457 rfl rfl rfl

noncomputable def hp754461 := hp754459 hp754457 12799833 rfl rfl rfl rfl rfl rfl rfl rfl (hp754460 rfl)

noncomputable def hp754462 := @BSN.binarySplit_of_base3 (BSN.cosOddP 131679447) (BSN.cosOddQ 67108864) 0 3 hp754458 hp745661 hp754457 rfl rfl rfl

noncomputable def hp754463 := hp754455 (BSN.cos_neg_of_bound 131679447 67108864 Bool.true 12799833 33554432 1 10890000 (hp754461 (hp754462 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp754464 := hp754411 (hp754414 (@Enclosure.Real.IsNear.neg hp754413 Bool.false 33693927 33554432 61 16777216 (hp754439 rfl))) (@hp754440 12799833 33554432 1269127216 182703882240000 12799833 33554432 79320451 11418992640000 (hp754463 rfl) rfl)

noncomputable def hp754465 := @hp754386 67108864 431276638714191 1125899906842624 400506528646153 47894726505922560000 8540054175767306057991 75557863725914323419136 127185553341560042532671 hp738860 (hp754404 rfl) (@hp754407 Bool.false 431276638714191 1125899906842624 400506528646153 47894726505922560000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp754214 (Enclosure.sfrac Bool.false 11 1)) (hp754408 rfl (hp754217 rfl rfl))) (hp754464 rfl))

noncomputable def hp754466 := @hp754211 hp754209 hp738860 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 828859 1000))) (@hp754216 hp754209 hp738860 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 828859 1000) 11 (hp754217 rfl rfl)) (@hp754220 hp754209 hp738860 hp754385 (hp754465 rfl) rfl rfl))

theorem hd5027 : hp754210 hp738860 := hp754466

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

noncomputable def hp790762 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) Bool.false 556919581 10737418240 1213 10737418240

noncomputable def hp791997 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) 814678 1000 815969 1000

noncomputable def hp791998 := hp791997 (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl rfl rfl

noncomputable def hp791999 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998))

noncomputable def hp792000 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 814678 1000) 814678 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl rfl

noncomputable def hp792001 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998))

noncomputable def hp792002 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998)) 13016006086865015373005

noncomputable def hp792003 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 814678 1000))

noncomputable def hp792004 := @hp792002 18889465931478580854784 432132676092571296169351 hp751364 (@hp792003 Bool.true 13016006086865015373005 18889465931478580854784 432132676092571296169351 hp751364 (hd4340 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998) hd5016)

noncomputable def hp792005 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998)) 90151228217801955985693

noncomputable def hp792006 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 815969 1000))

noncomputable def hp792007 := @hp792005 18889465931478580854784 1190095007903759139496411 hp751616 (@hp792006 Bool.false 90151228217801955985693 18889465931478580854784 1190095007903759139496411 hp751616 (hd4359 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998) hd5017)

noncomputable def hp792008 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998) hp792000 (hp792001 (hp792004 rfl rfl rfl) (hp792007 rfl rfl rfl))

noncomputable def hp792009 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792010 := hp792009 (Enclosure.sfrac Bool.false 814678 1000) 749551 1000 814678 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792011 := hp792010 (@Eq.refl Real (Enclosure.sfrac Bool.false 814678 1000)) rfl rfl rfl rfl

noncomputable def hp792012 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792013 := @hp792012 Bool.true Bool.false 13016006086865015373005 18889465931478580854784 432132676092571296169351 hp751364 556919581 10737418240 1213 10737418240 (@hp792003 Bool.true 13016006086865015373005 18889465931478580854784 432132676092571296169351 hp751364 (hd4340 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998) hd5016)

noncomputable def hp792014 := hp792013 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792015 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792016 := hp792015 (Enclosure.sfrac Bool.false 815969 1000) 749551 1000 815969 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792017 := hp792016 (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl rfl rfl rfl

noncomputable def hp792018 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792019 := @hp792018 Bool.false Bool.false 90151228217801955985693 18889465931478580854784 1190095007903759139496411 hp751616 556919581 10737418240 1213 10737418240 (@hp792006 Bool.false 90151228217801955985693 18889465931478580854784 1190095007903759139496411 hp751616 (hd4359 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998) hd5017)

noncomputable def hp792020 := hp792019 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792022 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) 815969 1000 817260 1000

noncomputable def hp792023 := hp792022 (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl rfl rfl

noncomputable def hp792024 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023))

noncomputable def hp792025 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 815969 1000) 815969 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl rfl

noncomputable def hp792026 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023))

noncomputable def hp792027 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023)) 90151228217801955985693

noncomputable def hp792028 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 815969 1000))

noncomputable def hp792029 := @hp792027 18889465931478580854784 1190095007903759139496411 hp751616 (@hp792028 Bool.false 90151228217801955985693 18889465931478580854784 1190095007903759139496411 hp751616 (hd4340 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023) hd5017)

noncomputable def hp792030 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023)) 31922198073318024890163

noncomputable def hp792031 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 817260 1000))

noncomputable def hp792032 := @hp792030 9444732965739290427392 317819373059543018578751 hp751876 (@hp792031 Bool.true 31922198073318024890163 9444732965739290427392 317819373059543018578751 hp751876 (hd4359 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023) hd5018)

noncomputable def hp792033 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023) hp792025 (hp792026 (hp792029 rfl rfl rfl) (hp792032 rfl rfl rfl))

noncomputable def hp792034 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792035 := hp792034 (Enclosure.sfrac Bool.false 815969 1000) 749551 1000 815969 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792036 := hp792035 (@Eq.refl Real (Enclosure.sfrac Bool.false 815969 1000)) rfl rfl rfl rfl

noncomputable def hp792037 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792038 := @hp792037 Bool.false Bool.false 90151228217801955985693 18889465931478580854784 1190095007903759139496411 hp751616 556919581 10737418240 1213 10737418240 (@hp792028 Bool.false 90151228217801955985693 18889465931478580854784 1190095007903759139496411 hp751616 (hd4340 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023) hd5017)

noncomputable def hp792039 := hp792038 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792040 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792041 := hp792040 (Enclosure.sfrac Bool.false 817260 1000) 749551 1000 817260 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792042 := hp792041 (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl rfl rfl rfl

noncomputable def hp792043 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792044 := @hp792043 Bool.true Bool.false 31922198073318024890163 9444732965739290427392 317819373059543018578751 hp751876 556919581 10737418240 1213 10737418240 (@hp792031 Bool.true 31922198073318024890163 9444732965739290427392 317819373059543018578751 hp751876 (hd4359 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023) hd5018)

noncomputable def hp792045 := hp792044 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792047 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) 817260 1000 818551 1000

noncomputable def hp792048 := hp792047 (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl rfl rfl

noncomputable def hp792049 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048))

noncomputable def hp792050 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 817260 1000) 817260 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl rfl

noncomputable def hp792051 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048))

noncomputable def hp792052 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048)) 31922198073318024890163

noncomputable def hp792053 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 817260 1000))

noncomputable def hp792054 := @hp792052 9444732965739290427392 317819373059543018578751 hp751876 (@hp792053 Bool.true 31922198073318024890163 9444732965739290427392 317819373059543018578751 hp751876 (hd4340 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048) hd5018)

noncomputable def hp792055 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048)) 10339502890598671513357

noncomputable def hp792056 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 818551 1000))

noncomputable def hp792057 := @hp792055 18889465931478580854784 636496280585817785703743 hp752138 (@hp792056 Bool.false 10339502890598671513357 18889465931478580854784 636496280585817785703743 hp752138 (hd4359 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048) hd5019)

noncomputable def hp792058 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048) hp792050 (hp792051 (hp792054 rfl rfl rfl) (hp792057 rfl rfl rfl))

noncomputable def hp792059 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792060 := hp792059 (Enclosure.sfrac Bool.false 817260 1000) 749551 1000 817260 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792061 := hp792060 (@Eq.refl Real (Enclosure.sfrac Bool.false 817260 1000)) rfl rfl rfl rfl

noncomputable def hp792062 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792063 := @hp792062 Bool.true Bool.false 31922198073318024890163 9444732965739290427392 317819373059543018578751 hp751876 556919581 10737418240 1213 10737418240 (@hp792053 Bool.true 31922198073318024890163 9444732965739290427392 317819373059543018578751 hp751876 (hd4340 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048) hd5018)

noncomputable def hp792064 := hp792063 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792065 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792066 := hp792065 (Enclosure.sfrac Bool.false 818551 1000) 749551 1000 818551 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792067 := hp792066 (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl rfl rfl rfl

noncomputable def hp792068 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792069 := @hp792068 Bool.false Bool.false 10339502890598671513357 18889465931478580854784 636496280585817785703743 hp752138 556919581 10737418240 1213 10737418240 (@hp792056 Bool.false 10339502890598671513357 18889465931478580854784 636496280585817785703743 hp752138 (hd4359 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048) hd5019)

noncomputable def hp792070 := hp792069 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792072 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) 818551 1000 819841 1000

noncomputable def hp792073 := hp792072 (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl rfl rfl

noncomputable def hp792074 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073))

noncomputable def hp792075 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 818551 1000) 818551 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl rfl

noncomputable def hp792076 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073))

noncomputable def hp792077 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073)) 10339502890598671513357

noncomputable def hp792078 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 818551 1000))

noncomputable def hp792079 := @hp792077 18889465931478580854784 636496280585817785703743 hp752138 (@hp792078 Bool.false 10339502890598671513357 18889465931478580854784 636496280585817785703743 hp752138 (hd4340 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073) hd5019)

noncomputable def hp792080 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073)) 15780327723276270924517

noncomputable def hp792081 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 819841 1000))

noncomputable def hp792082 := @hp792080 9444732965739290427392 hp752396 hp752398 (@hp792081 Bool.true 15780327723276270924517 9444732965739290427392 hp752396 hp752398 (hd4359 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073) hd5020)

noncomputable def hp792083 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073) hp792075 (hp792076 (hp792079 rfl rfl rfl) (hp792082 rfl rfl rfl))

noncomputable def hp792084 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792085 := hp792084 (Enclosure.sfrac Bool.false 818551 1000) 749551 1000 818551 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792086 := hp792085 (@Eq.refl Real (Enclosure.sfrac Bool.false 818551 1000)) rfl rfl rfl rfl

noncomputable def hp792087 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792088 := @hp792087 Bool.false Bool.false 10339502890598671513357 18889465931478580854784 636496280585817785703743 hp752138 556919581 10737418240 1213 10737418240 (@hp792078 Bool.false 10339502890598671513357 18889465931478580854784 636496280585817785703743 hp752138 (hd4340 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073) hd5019)

noncomputable def hp792089 := hp792088 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792090 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792091 := hp792090 (Enclosure.sfrac Bool.false 819841 1000) 749551 1000 819841 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792092 := hp792091 (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl rfl rfl rfl

noncomputable def hp792093 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792094 := @hp792093 Bool.true Bool.false 15780327723276270924517 9444732965739290427392 hp752396 hp752398 556919581 10737418240 1213 10737418240 (@hp792081 Bool.true 15780327723276270924517 9444732965739290427392 hp752396 hp752398 (hd4359 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073) hd5020)

noncomputable def hp792095 := hp792094 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792097 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) 819841 1000 821372 1000

noncomputable def hp792098 := hp792097 (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl rfl rfl

noncomputable def hp792099 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098))

noncomputable def hp792100 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 819841 1000) 819841 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl rfl

noncomputable def hp792101 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098))

noncomputable def hp792102 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098)) 15780327723276270924517

noncomputable def hp792103 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 819841 1000))

noncomputable def hp792104 := @hp792102 9444732965739290427392 hp752396 hp752398 (@hp792103 Bool.true 15780327723276270924517 9444732965739290427392 hp752396 hp752398 (hd4340 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098) hd5020)

noncomputable def hp792105 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098)) 152880999490992134501

noncomputable def hp792106 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821372 1000))

noncomputable def hp792107 := @hp792105 295147905179352825856 hp752657 hp742094 (@hp792106 Bool.false 152880999490992134501 295147905179352825856 hp752657 hp742094 (hd4359 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098) hd5021)

noncomputable def hp792108 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098) hp792100 (hp792101 (hp792104 rfl rfl rfl) (hp792107 rfl rfl rfl))

noncomputable def hp792109 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792110 := hp792109 (Enclosure.sfrac Bool.false 819841 1000) 749551 1000 819841 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792111 := hp792110 (@Eq.refl Real (Enclosure.sfrac Bool.false 819841 1000)) rfl rfl rfl rfl

noncomputable def hp792112 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792113 := @hp792112 Bool.true Bool.false 15780327723276270924517 9444732965739290427392 hp752396 hp752398 556919581 10737418240 1213 10737418240 (@hp792103 Bool.true 15780327723276270924517 9444732965739290427392 hp752396 hp752398 (hd4340 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098) hd5020)

noncomputable def hp792114 := hp792113 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792115 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792116 := hp792115 (Enclosure.sfrac Bool.false 821372 1000) 749551 1000 821372 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792117 := hp792116 (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl rfl rfl rfl

noncomputable def hp792118 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792119 := @hp792118 Bool.false Bool.false 152880999490992134501 295147905179352825856 hp752657 hp742094 556919581 10737418240 1213 10737418240 (@hp792106 Bool.false 152880999490992134501 295147905179352825856 hp752657 hp742094 (hd4359 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098) hd5021)

noncomputable def hp792120 := hp792119 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792122 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) 821372 1000 821936 1000

noncomputable def hp792123 := hp792122 (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl rfl rfl

noncomputable def hp792124 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123))

noncomputable def hp792125 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 821372 1000) 821372 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl rfl

noncomputable def hp792126 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123))

noncomputable def hp792127 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123)) 152880999490992134501

noncomputable def hp792128 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821372 1000))

noncomputable def hp792129 := @hp792127 295147905179352825856 hp752657 hp742094 (@hp792128 Bool.false 152880999490992134501 295147905179352825856 hp752657 hp742094 (hd4340 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123) hd5021)

noncomputable def hp792130 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123)) 8332312934964312657227

noncomputable def hp792131 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821936 1000))

noncomputable def hp792132 := @hp792130 37778931862957161709568 85207062108651627797619 hp752921 (@hp792131 Bool.true 8332312934964312657227 37778931862957161709568 85207062108651627797619 hp752921 (hd4359 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123) hd5022)

noncomputable def hp792133 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123) hp792125 (hp792126 (hp792129 rfl rfl rfl) (hp792132 rfl rfl rfl))

noncomputable def hp792134 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792135 := hp792134 (Enclosure.sfrac Bool.false 821372 1000) 749551 1000 821372 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792136 := hp792135 (@Eq.refl Real (Enclosure.sfrac Bool.false 821372 1000)) rfl rfl rfl rfl

noncomputable def hp792137 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792138 := @hp792137 Bool.false Bool.false 152880999490992134501 295147905179352825856 hp752657 hp742094 556919581 10737418240 1213 10737418240 (@hp792128 Bool.false 152880999490992134501 295147905179352825856 hp752657 hp742094 (hd4340 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123) hd5021)

noncomputable def hp792139 := hp792138 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792140 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792141 := hp792140 (Enclosure.sfrac Bool.false 821936 1000) 749551 1000 821936 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792142 := hp792141 (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl rfl rfl rfl

noncomputable def hp792143 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792144 := @hp792143 Bool.true Bool.false 8332312934964312657227 37778931862957161709568 85207062108651627797619 hp752921 556919581 10737418240 1213 10737418240 (@hp792131 Bool.true 8332312934964312657227 37778931862957161709568 85207062108651627797619 hp752921 (hd4359 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123) hd5022)

noncomputable def hp792145 := hp792144 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792147 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) 821936 1000 822983 1000

noncomputable def hp792148 := hp792147 (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl rfl rfl

noncomputable def hp792149 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148))

noncomputable def hp792150 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 821936 1000) 821936 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl rfl

noncomputable def hp792151 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148))

noncomputable def hp792152 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148)) 8332312934964312657227

noncomputable def hp792153 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 821936 1000))

noncomputable def hp792154 := @hp792152 37778931862957161709568 85207062108651627797619 hp752921 (@hp792153 Bool.true 8332312934964312657227 37778931862957161709568 85207062108651627797619 hp752921 (hd4340 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148) hd5022)

noncomputable def hp792155 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148)) 20487540792335008318061

noncomputable def hp792156 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 822983 1000))

noncomputable def hp792157 := @hp792155 4722366482869645213696 799794236235346227622709 hp750331 (@hp792156 Bool.false 20487540792335008318061 4722366482869645213696 799794236235346227622709 hp750331 (hd4359 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148) hd5023)

noncomputable def hp792158 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148) hp792150 (hp792151 (hp792154 rfl rfl rfl) (hp792157 rfl rfl rfl))

noncomputable def hp792159 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792160 := hp792159 (Enclosure.sfrac Bool.false 821936 1000) 749551 1000 821936 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792161 := hp792160 (@Eq.refl Real (Enclosure.sfrac Bool.false 821936 1000)) rfl rfl rfl rfl

noncomputable def hp792162 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792163 := @hp792162 Bool.true Bool.false 8332312934964312657227 37778931862957161709568 85207062108651627797619 hp752921 556919581 10737418240 1213 10737418240 (@hp792153 Bool.true 8332312934964312657227 37778931862957161709568 85207062108651627797619 hp752921 (hd4340 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148) hd5022)

noncomputable def hp792164 := hp792163 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792165 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792166 := hp792165 (Enclosure.sfrac Bool.false 822983 1000) 749551 1000 822983 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792167 := hp792166 (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl rfl rfl rfl

noncomputable def hp792168 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792169 := @hp792168 Bool.false Bool.false 20487540792335008318061 4722366482869645213696 799794236235346227622709 hp750331 556919581 10737418240 1213 10737418240 (@hp792156 Bool.false 20487540792335008318061 4722366482869645213696 799794236235346227622709 hp750331 (hd4359 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148) hd5023)

noncomputable def hp792170 := hp792169 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792172 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) 822983 1000 824997 1000

noncomputable def hp792173 := hp792172 (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl rfl rfl

noncomputable def hp792174 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173))

noncomputable def hp792175 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 822983 1000) 822983 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl rfl

noncomputable def hp792176 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173))

noncomputable def hp792177 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173)) 20487540792335008318061

noncomputable def hp792178 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 822983 1000))

noncomputable def hp792179 := @hp792177 4722366482869645213696 799794236235346227622709 hp750331 (@hp792178 Bool.false 20487540792335008318061 4722366482869645213696 799794236235346227622709 hp750331 (hd4340 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173) hd5023)

noncomputable def hp792180 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173)) 29507171841410328193615

noncomputable def hp792181 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 824997 1000))

noncomputable def hp792182 := @hp792180 9444732965739290427392 hp753442 hp744350 (@hp792181 Bool.true 29507171841410328193615 9444732965739290427392 hp753442 hp744350 (hd4359 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173) hd5024)

noncomputable def hp792183 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173) hp792175 (hp792176 (hp792179 rfl rfl rfl) (hp792182 rfl rfl rfl))

noncomputable def hp792184 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792185 := hp792184 (Enclosure.sfrac Bool.false 822983 1000) 749551 1000 822983 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792186 := hp792185 (@Eq.refl Real (Enclosure.sfrac Bool.false 822983 1000)) rfl rfl rfl rfl

noncomputable def hp792187 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792188 := @hp792187 Bool.false Bool.false 20487540792335008318061 4722366482869645213696 799794236235346227622709 hp750331 556919581 10737418240 1213 10737418240 (@hp792178 Bool.false 20487540792335008318061 4722366482869645213696 799794236235346227622709 hp750331 (hd4340 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173) hd5023)

noncomputable def hp792189 := hp792188 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792190 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792191 := hp792190 (Enclosure.sfrac Bool.false 824997 1000) 749551 1000 824997 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792192 := hp792191 (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl rfl rfl rfl

noncomputable def hp792193 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792194 := @hp792193 Bool.true Bool.false 29507171841410328193615 9444732965739290427392 hp753442 hp744350 556919581 10737418240 1213 10737418240 (@hp792181 Bool.true 29507171841410328193615 9444732965739290427392 hp753442 hp744350 (hd4359 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173) hd5024)

noncomputable def hp792195 := hp792194 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792197 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) 824997 1000 826285 1000

noncomputable def hp792198 := hp792197 (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl rfl rfl

noncomputable def hp792199 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198))

noncomputable def hp792200 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 824997 1000) 824997 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl rfl

noncomputable def hp792201 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198))

noncomputable def hp792202 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198)) 29507171841410328193615

noncomputable def hp792203 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 824997 1000))

noncomputable def hp792204 := @hp792202 9444732965739290427392 hp753442 hp744350 (@hp792203 Bool.true 29507171841410328193615 9444732965739290427392 hp753442 hp744350 (hd4340 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198) hd5024)

noncomputable def hp792205 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198)) 30453645506694091203077

noncomputable def hp792206 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 826285 1000))

noncomputable def hp792207 := @hp792205 37778931862957161709568 hp753695 hp741590 (@hp792206 Bool.false 30453645506694091203077 37778931862957161709568 hp753695 hp741590 (hd4359 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198) hd5025)

noncomputable def hp792208 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198) hp792200 (hp792201 (hp792204 rfl rfl rfl) (hp792207 rfl rfl rfl))

noncomputable def hp792209 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792210 := hp792209 (Enclosure.sfrac Bool.false 824997 1000) 749551 1000 824997 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792211 := hp792210 (@Eq.refl Real (Enclosure.sfrac Bool.false 824997 1000)) rfl rfl rfl rfl

noncomputable def hp792212 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792213 := @hp792212 Bool.true Bool.false 29507171841410328193615 9444732965739290427392 hp753442 hp744350 556919581 10737418240 1213 10737418240 (@hp792203 Bool.true 29507171841410328193615 9444732965739290427392 hp753442 hp744350 (hd4340 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198) hd5024)

noncomputable def hp792214 := hp792213 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792215 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792216 := hp792215 (Enclosure.sfrac Bool.false 826285 1000) 749551 1000 826285 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792217 := hp792216 (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl rfl rfl rfl

noncomputable def hp792218 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792219 := @hp792218 Bool.false Bool.false 30453645506694091203077 37778931862957161709568 hp753695 hp741590 556919581 10737418240 1213 10737418240 (@hp792206 Bool.false 30453645506694091203077 37778931862957161709568 hp753695 hp741590 (hd4359 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198) hd5025)

noncomputable def hp792220 := hp792219 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792222 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) 826285 1000 827572 1000

noncomputable def hp792223 := hp792222 (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl rfl rfl

noncomputable def hp792224 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223))

noncomputable def hp792225 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 826285 1000) 826285 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl rfl

noncomputable def hp792226 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223))

noncomputable def hp792227 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223)) 30453645506694091203077

noncomputable def hp792228 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 826285 1000))

noncomputable def hp792229 := @hp792227 37778931862957161709568 hp753695 hp741590 (@hp792228 Bool.false 30453645506694091203077 37778931862957161709568 hp753695 hp741590 (hd4340 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223) hd5025)

noncomputable def hp792230 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223)) 147008037433646261728903

noncomputable def hp792231 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 827572 1000))

noncomputable def hp792232 := @hp792230 75557863725914323419136 389890594628524038105653 hp753952 (@hp792231 Bool.true 147008037433646261728903 75557863725914323419136 389890594628524038105653 hp753952 (hd4359 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223) hd5026)

noncomputable def hp792233 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223) hp792225 (hp792226 (hp792229 rfl rfl rfl) (hp792232 rfl rfl rfl))

noncomputable def hp792234 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792235 := hp792234 (Enclosure.sfrac Bool.false 826285 1000) 749551 1000 826285 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792236 := hp792235 (@Eq.refl Real (Enclosure.sfrac Bool.false 826285 1000)) rfl rfl rfl rfl

noncomputable def hp792237 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792238 := @hp792237 Bool.false Bool.false 30453645506694091203077 37778931862957161709568 hp753695 hp741590 556919581 10737418240 1213 10737418240 (@hp792228 Bool.false 30453645506694091203077 37778931862957161709568 hp753695 hp741590 (hd4340 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223) hd5025)

noncomputable def hp792239 := hp792238 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792240 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792241 := hp792240 (Enclosure.sfrac Bool.false 827572 1000) 749551 1000 827572 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792242 := hp792241 (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl rfl rfl rfl

noncomputable def hp792243 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792244 := @hp792243 Bool.true Bool.false 147008037433646261728903 75557863725914323419136 389890594628524038105653 hp753952 556919581 10737418240 1213 10737418240 (@hp792231 Bool.true 147008037433646261728903 75557863725914323419136 389890594628524038105653 hp753952 (hd4359 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223) hd5026)

noncomputable def hp792245 := hp792244 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792247 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) 827572 1000 828859 1000

noncomputable def hp792248 := hp792247 (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl rfl rfl

noncomputable def hp792249 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248))

noncomputable def hp792250 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 827572 1000) 827572 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl rfl

noncomputable def hp792251 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248))

noncomputable def hp792252 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248)) 147008037433646261728903

noncomputable def hp792253 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 827572 1000))

noncomputable def hp792254 := @hp792252 75557863725914323419136 389890594628524038105653 hp753952 (@hp792253 Bool.true 147008037433646261728903 75557863725914323419136 389890594628524038105653 hp753952 (hd4340 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248) hd5026)

noncomputable def hp792255 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248)) 97118063959614914181383

noncomputable def hp792256 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 828859 1000))

noncomputable def hp792257 := @hp792255 75557863725914323419136 hp754209 hp738860 (@hp792256 Bool.false 97118063959614914181383 75557863725914323419136 hp754209 hp738860 (hd4359 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248) hd5027)

noncomputable def hp792258 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248) hp792250 (hp792251 (hp792254 rfl rfl rfl) (hp792257 rfl rfl rfl))

noncomputable def hp792259 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792260 := hp792259 (Enclosure.sfrac Bool.false 827572 1000) 749551 1000 827572 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792261 := hp792260 (@Eq.refl Real (Enclosure.sfrac Bool.false 827572 1000)) rfl rfl rfl rfl

noncomputable def hp792262 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792263 := @hp792262 Bool.true Bool.false 147008037433646261728903 75557863725914323419136 389890594628524038105653 hp753952 556919581 10737418240 1213 10737418240 (@hp792253 Bool.true 147008037433646261728903 75557863725914323419136 389890594628524038105653 hp753952 (hd4340 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248) hd5026)

noncomputable def hp792264 := hp792263 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792265 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792266 := hp792265 (Enclosure.sfrac Bool.false 828859 1000) 749551 1000 828859 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792267 := hp792266 (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl rfl rfl rfl

noncomputable def hp792268 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792269 := @hp792268 Bool.false Bool.false 97118063959614914181383 75557863725914323419136 hp754209 hp738860 556919581 10737418240 1213 10737418240 (@hp792256 Bool.false 97118063959614914181383 75557863725914323419136 hp754209 hp738860 (hd4359 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248) hd5027)

noncomputable def hp792270 := hp792269 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792272 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) 828859 1000 830146 1000

noncomputable def hp792273 := hp792272 (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl rfl rfl

noncomputable def hp792274 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273))

noncomputable def hp792275 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 828859 1000) 828859 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl rfl

noncomputable def hp792276 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273))

noncomputable def hp792277 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273)) 97118063959614914181383

noncomputable def hp792278 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 828859 1000))

noncomputable def hp792279 := @hp792277 75557863725914323419136 hp754209 hp738860 (@hp792278 Bool.false 97118063959614914181383 75557863725914323419136 hp754209 hp738860 (hd4340 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273) hd5027)

noncomputable def hp792280 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273)) 72094639779617503274629

noncomputable def hp792281 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 830146 1000))

noncomputable def hp792282 := @hp792280 37778931862957161709568 hp754467 hp743344 (@hp792281 Bool.true 72094639779617503274629 37778931862957161709568 hp754467 hp743344 (hd4359 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273) hd5028)

noncomputable def hp792283 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273) hp792275 (hp792276 (hp792279 rfl rfl rfl) (hp792282 rfl rfl rfl))

noncomputable def hp792284 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792285 := hp792284 (Enclosure.sfrac Bool.false 828859 1000) 749551 1000 828859 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792286 := hp792285 (@Eq.refl Real (Enclosure.sfrac Bool.false 828859 1000)) rfl rfl rfl rfl

noncomputable def hp792287 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792288 := @hp792287 Bool.false Bool.false 97118063959614914181383 75557863725914323419136 hp754209 hp738860 556919581 10737418240 1213 10737418240 (@hp792278 Bool.false 97118063959614914181383 75557863725914323419136 hp754209 hp738860 (hd4340 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273) hd5027)

noncomputable def hp792289 := hp792288 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp792290 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp792291 := hp792290 (Enclosure.sfrac Bool.false 830146 1000) 749551 1000 830146 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792292 := hp792291 (@Eq.refl Real (Enclosure.sfrac Bool.false 830146 1000)) rfl rfl rfl rfl

noncomputable def hp792293 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp792294 := @hp792293 Bool.true Bool.false 72094639779617503274629 37778931862957161709568 hp754467 hp743344 556919581 10737418240 1213 10737418240 (@hp792281 Bool.true 72094639779617503274629 37778931862957161709568 hp754467 hp743344 (hd4359 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273) hd5028)

noncomputable def hp792295 := hp792294 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl
open Zeta.Certificates
noncomputable def certificatePairs : List (Σ' I : ZIntervalRS, I.Certified) := [(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 814678 1000) (Enclosure.sfrac Bool.false 815969 1000) hp791998) (hp791999 (hp792008 (hp792011 (hp792014 rfl rfl)) (hp792017 (hp792020 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 815969 1000) (Enclosure.sfrac Bool.false 817260 1000) hp792023) (hp792024 (hp792033 (hp792036 (hp792039 rfl rfl)) (hp792042 (hp792045 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 817260 1000) (Enclosure.sfrac Bool.false 818551 1000) hp792048) (hp792049 (hp792058 (hp792061 (hp792064 rfl rfl)) (hp792067 (hp792070 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 818551 1000) (Enclosure.sfrac Bool.false 819841 1000) hp792073) (hp792074 (hp792083 (hp792086 (hp792089 rfl rfl)) (hp792092 (hp792095 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 819841 1000) (Enclosure.sfrac Bool.false 821372 1000) hp792098) (hp792099 (hp792108 (hp792111 (hp792114 rfl rfl)) (hp792117 (hp792120 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 821372 1000) (Enclosure.sfrac Bool.false 821936 1000) hp792123) (hp792124 (hp792133 (hp792136 (hp792139 rfl rfl)) (hp792142 (hp792145 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 821936 1000) (Enclosure.sfrac Bool.false 822983 1000) hp792148) (hp792149 (hp792158 (hp792161 (hp792164 rfl rfl)) (hp792167 (hp792170 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 822983 1000) (Enclosure.sfrac Bool.false 824997 1000) hp792173) (hp792174 (hp792183 (hp792186 (hp792189 rfl rfl)) (hp792192 (hp792195 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 824997 1000) (Enclosure.sfrac Bool.false 826285 1000) hp792198) (hp792199 (hp792208 (hp792211 (hp792214 rfl rfl)) (hp792217 (hp792220 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 826285 1000) (Enclosure.sfrac Bool.false 827572 1000) hp792223) (hp792224 (hp792233 (hp792236 (hp792239 rfl rfl)) (hp792242 (hp792245 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 827572 1000) (Enclosure.sfrac Bool.false 828859 1000) hp792248) (hp792249 (hp792258 (hp792261 (hp792264 rfl rfl)) (hp792267 (hp792270 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 828859 1000) (Enclosure.sfrac Bool.false 830146 1000) hp792273) (hp792274 (hp792283 (hp792286 (hp792289 rfl rfl)) (hp792292 (hp792295 rfl rfl)))))]

theorem solution : Zeta.Certificates.BatchSpec 12 814678 1000 830146 1000 :=
  ⟨CertifiedZeroIntervals.ofCertifiedRS certificatePairs (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.singleton _)))))))))))), rfl, rfl, rfl⟩
#print axioms solution
