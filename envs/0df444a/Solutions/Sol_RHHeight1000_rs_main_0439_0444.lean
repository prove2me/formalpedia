-- Prove2me | solution 1 for RHHeight1000.rs_main_0439_0444
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T10:34:18.933278+00:00
-- url     : https://prove2.me/submissions/4d4139b7-8a75-4ccb-b8d9-7d66453b95e2

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

theorem hd4359 : ∀ (a b : Real) (h : @LE.le Real Real.instLE a b), @Eq Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 a b h)) (hardyZApproximantRS₀ b) := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @rfl Real (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 a b h))

noncomputable def hp631123 := nat_lit 72057594037927936000000000000000

noncomputable def hp631146 := nat_lit 39614081257132168796771975168

noncomputable def hp631148 := nat_lit 1208925819614629174706176000000000000000

noncomputable def hp631501 := nat_lit 2882303761517117440000000000000

noncomputable def hp633087 := nat_lit 238218625957466057251055545473924217321462656961770832410330149674186428124198706933734676889600

noncomputable def hp633090 := nat_lit 21677894962129411209846054638127103776253101783521145749340043620350964959302082330969855596953600

noncomputable def hp633286 := nat_lit 14198936579076412752333613960380805571166435299025227571149477343212749250185412581785600

noncomputable def hp633289 := nat_lit 1292103228695953560462358870394653306976145612211295708974602438232360181766872544942489600

noncomputable def hp634261 := nat_lit 618970019642690137449562112

noncomputable def hp634263 := nat_lit 302231454903657293676544000000000000000

noncomputable def hp636853 := nat_lit 241785163922925834941235200000000000000

noncomputable def hp642702 := nat_lit 3570415896635346974072005805030179415937144689025665314440334861177556999349704385084003346650664335197480996044800

noncomputable def hp642705 := nat_lit 124964556382237144092520203176056279557800064115898286005411720141214494977239653477940117132773251731911834861568000

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

noncomputable def hp740271 := @Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (Enclosure.sfrac Bool.true 1 1) Bool.true 1

noncomputable def hp741590 := nat_lit 17142190332816812125716480000

noncomputable def hp742600 := nat_lit 11428126888544541417144320000

noncomputable def hp742826 := nat_lit 3868562622766813359059763200000000000000

noncomputable def hp745658 := nat_lit 3996645342911614855169325114413848961633120431781532997847909552396155328908156533147964360867027353600

noncomputable def hp745661 := nat_lit 363694726204956951820408585411660255508613959292119502804159769268050134930642244516464756838899489177600

noncomputable def hp748296 := nat_lit 18884954981369413745078497

noncomputable def hp748297 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 799149 1000)) Bool.true 99586979194371739750349 75557863725914323419136 hp748296

noncomputable def hp748298 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 799149 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 799149 1000)) Bool.true 99586979194371739750349 75557863725914323419136

noncomputable def hp748299 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 799149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748300 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp748299 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp748301 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 799149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748302 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp748300 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp748303 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 799149 1000)) hp748302 Bool.true 99586979194371739750349 75557863725914323419136

noncomputable def hp748304 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 799149 1000) 799149 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) rfl

noncomputable def hp748305 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp748300 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp748306 := nat_lit 26732676171703690593398259974144

noncomputable def hp748307 := @hp748305 391698971 268435456 24241 33554432 10666479545441180184627 75557863725914323419136 308697937688313313718497 hp740088 hp748306 99586979194371739750349 75557863725914323419136

noncomputable def hp748308 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) 11)

noncomputable def hp748309 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) 11) hp748308

noncomputable def hp748310 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) 11)

noncomputable def hp748311 := @hp748310 391698971 536870912 193928 536870912 391698971 536870912 193928 536870912 420583567580463104 391698971 268435456

noncomputable def hp748312 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp748313 := hp748312 BSN.quadSignNeg 9 10 11 799149 1000 193 241 536870912 268435456 9007199254740992

noncomputable def hp748314 := hp748313 Bool.false 824762104322 3642 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp748315 := hp748314 Bool.true 120459897 166482 Bool.true 378894663 Bool.true 791647706 28296951008113761 1 Bool.false 348215571

noncomputable def hp748316 := hp748315 Bool.true Bool.false 534386669 Bool.true Bool.true 391698971 193928 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 348215571 536870912) BSN.abs_quadSignNeg

noncomputable def hp748317 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp748318 := hp748317 BSN.quadSignPos 7 8 9 799149 1000 79 139 536870912 268435456 9007199254740992

noncomputable def hp748319 := hp748318 Bool.false 824762104322 3642 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp748320 := hp748319 Bool.true 482718169 135966 Bool.true 779313495 Bool.true 714027338 28296951008113761 1 Bool.false 533060568

noncomputable def hp748321 := hp748320 Bool.false Bool.false 521378697 Bool.false Bool.true 120459897 166482 BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 533060568 536870912) BSN.abs_quadSignPos

noncomputable def hp748322 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp748323 := hp748322 BSN.quadSignPos 5 6 7 799149 1000 66 11 536870912 268435456 9007199254740992

noncomputable def hp748324 := hp748323 Bool.false 824762104322 3642 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp748325 := hp748324 Bool.true 515707382 101039 Bool.false 367111337 Bool.true 834423193 28296951008113761 1 Bool.false 416170984

noncomputable def hp748326 := hp748325 Bool.true Bool.false 536797281 Bool.false Bool.true 482718169 135966 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 416170984 536870912) BSN.abs_quadSignPos

noncomputable def hp748327 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp748328 := hp748327 BSN.quadSignPos 3 4 5 799149 1000 272 159 536870912 268435456 9007199254740992

noncomputable def hp748329 := hp748328 Bool.false 824762104322 3642 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp748330 := hp748329 Bool.true 702389855 59721 Bool.false 604946344 Bool.false 162050320 28296951008113761 1 Bool.false 230613652

noncomputable def hp748331 := hp748330 Bool.false Bool.false 159600805 Bool.false Bool.true 515707382 101039 BSN.abs_quadSignPos (BSN.cos_quad_nat0 272 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 230613652 536870912) BSN.abs_quadSignPos

noncomputable def hp748332 := hp748312 BSN.quadSignPos 1 2 3 799149 1000 625 419 536870912 268435456 9007199254740992

noncomputable def hp748333 := hp748332 Bool.false 824762104322 3642 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp748334 := hp748333 Bool.true 536870880 3698 Bool.false 302566882 Bool.false 64729477 28296951008113761 1 Bool.false 286802620

noncomputable def hp748335 := hp748334 Bool.true Bool.false 64572765 Bool.false Bool.true 702389855 59721 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 625 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 286802620 536870912) BSN.abs_quadSignPos

noncomputable def hp748336 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) 1) Bool.true

noncomputable def hp748337 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)))

noncomputable def hp748338 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000))) Bool.true 67108860 67108864

noncomputable def hp748339 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1610863485) (@Nat.cast Real Real.instNatCast 1048576)) Bool.false 1610863485 1048576

noncomputable def hp748340 := nat_lit 7208512597026374952208985315419369671002621722420046322707

noncomputable def hp748341 := nat_lit 4692311530615706681803881276644227254246815914000384000

noncomputable def hp748342 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) Bool.false hp748340 hp748341 121001986099096028827

noncomputable def hp748343 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 799149 4000) (Real.log (Enclosure.sfrac Bool.false 2554557496804 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1598298))))))

noncomputable def hp748344 := nat_lit 156451766015928090917318145959520000

noncomputable def hp748345 := nat_lit 750169771200528148402407628655162690880

noncomputable def hp748346 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp748343 (Enclosure.sfrac Bool.false 799149 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 799149 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp748344 hp748345)) Bool.false

noncomputable def hp748347 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 799149 1000) 799149 1000 2554557496804 16000000 1598298

noncomputable def hp748348 := hp748347 4000 2000 hp748344 hp748345 (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) rfl rfl rfl rfl

noncomputable def hp748349 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp748343 (Enclosure.sfrac Bool.false 799149 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 799149 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp748344 hp748345) 27674427702673877324507 18014398509481984000

noncomputable def hp748350 := nat_lit 20760516279435959862361877708407784652487550560569733409396160

noncomputable def hp748351 := @hp748349 121001986099096028827 hp738659 hp748344 hp748345 0 1 hp748350 hp748340 hp748341 121001986099096028827 hp738659

noncomputable def hp748352 := @Enclosure.Real.IsNear.subLit_ff_p (hp748343 (Enclosure.sfrac Bool.false 799149 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 799149 2000) (Real.log Real.pi)) 35914301318714655068891 18014398509481984000 10089377295189937 4356000000000000000000

noncomputable def hp748353 := nat_lit 1857199404976573669723024130048000

noncomputable def hp748354 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 799149 4000) (Real.log (Enclosure.sfrac Bool.false 2554557496804 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1598298))))))

noncomputable def hp748355 := @hp748354 (Enclosure.sfrac Bool.false 799149 2000) 43112395595941664084699 18014398509481984000 10089377295189937 4356000000000000000000 799149 2000 0

noncomputable def hp748356 := nat_lit 71828602637429310137782000

noncomputable def hp748357 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 799149 4000) (Real.log (Enclosure.sfrac Bool.false 2554557496804 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1598298))))) 43119467016060928620699

noncomputable def hp748358 := nat_lit 97080484370466145602161857791998820352

noncomputable def hp748359 := @hp748357 18014398509481984000 3329792431548479 1452000000000000000000 883927514908067 2251799813685248 200000001089 8712000000000000000 hp748358 43112395595941664084699 18014398509481984000 10089377295189937

noncomputable def hp748360 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 799149 4000) (Real.log (Enclosure.sfrac Bool.false 2554557496804 16000000)) 799149 4000 0 1 53956730241870951 4503599627370496

noncomputable def hp748361 := nat_lit 115871195893964952198709248

noncomputable def hp748362 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2554557496804) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp748361 hp617687

noncomputable def hp748363 := BSN.log_rat_reduce_isNear 2554557496804 16000000 17 5109114993608 4194304000000 52961988 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp748364 := nat_lit 1063811811890355934138379841259917881926048039606924081896460636321500144046080

noncomputable def hp748365 := nat_lit 3448662186751743317506809549547986713799985423117543661914777259147301974016

noncomputable def hp748366 := nat_lit 137372415665364965319841967227814444115041771787371555110886574809149440

noncomputable def hp748367 := BSN.log_dyadic_bound 457405496804 4651709496804 4 3 hp748364 268435456 87120000 hp748365 hp748366 52961988 5109114993608

noncomputable def hp748368 := hp748367 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp748369 := @BSN.binarySplit_of_base3 (BSN.artanhP 457405496804) (BSN.artanhQ 4651709496804) 0 3 hp748365 hp748364 hp748366 rfl rfl rfl

noncomputable def hp748370 := hp748363 rfl rfl rfl rfl (hp748368 (hp748369 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp748371 := @hp748360 12500018513 1089000000000000000 43119467016060928620699 18014398509481984000 3329792431548479 1452000000000000000000 (Enclosure.Real.IsNear.const Bool.false 799149 4000) (BSN.isNear_log_sfrac 2554557496804 16000000 53956730241870951 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp748362 1000001481040000 87120000000000000000000 53956730241870951 4503599627370496 12500018513 1089000000000000000 (hp748370 rfl rfl rfl) rfl)) rfl

noncomputable def hp748372 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1598298)))) 1 4

noncomputable def hp748373 := @hp748372 0 1 883927514908067 562949953421312 200000001089 2178000000000000000 883927514908067 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp748374 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1598298))) 884279719003555 562949953421312 1

noncomputable def hp748375 := @hp748374 2000000000000000 20993 33554432 1 10890000 29659685691911720402944 883927514908067 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp748376 := BSN.arctan_dyadic_bound_f 1000 1598298 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp748377 := hp748376 1 20993 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1598298) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1598298) 0 0 rfl)

noncomputable def hp748378 := hp748373 (hp748375 (hp748377 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp748379 := @hp748352 30695921242389 67108864000 2397447 536870912000 hp748353 27674427702673877324507 18014398509481984000 121001986099096028827 hp738659 (@hp748355 1 hp748356 35914301318714655068891 18014398509481984000 10089377295189937 4356000000000000000000 (@hp748359 4356000000000000000000 hp748371 hp748378 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 799149 2000) rfl rfl)

noncomputable def hp748380 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 799149 2000) (Real.log Real.pi) 799149 2000 0 1 38410761 33554432

noncomputable def hp748381 := hp748379 (@hp748380 3 268435456 30695921242389 67108864000 2397447 536870912000 (Enclosure.Real.IsNear.const Bool.false 799149 2000) hd4909 rfl) rfl

noncomputable def hp748382 := @hp748342 hp738659 1610863485 1048576 57 8388608 (@hp748346 hp748340 hp748341 121001986099096028827 hp738659 (hp748348 rfl rfl rfl rfl rfl) (hp748351 (hp748381 rfl) (Enclosure.Real.IsNear.const Bool.true hp748344 hp748345) rfl rfl)) rfl

noncomputable def hp748383 := BSN.cos_reduce2 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1610863485) (@Nat.cast Real Real.instNatCast 1048576)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 49154282447626567680) (@Nat.cast Real Real.instNatCast 151115727451828646838272)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp748384 := BSN.sin_reduce_arg_pos_rat_q2 1610863485 1048576 226375608064910080 72057594037927936 244 49154282447626567680 151115727451828646838272 rfl rfl rfl rfl

noncomputable def hp748385 := BSN.cos_dyadic_bound_f 44705559 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp748386 := hp748385 1 67108860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 44705559) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp748387 := hp748386 (@BSN.binarySplit_of_le (BSN.cosOddP 44705559) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp748388 := @BSN.cos_arg_round Bool.false 67108860 67108864 49154282447626567680 151115727451828646838272 44705559 137438953472 21801270 21780000 hp748387 rfl

noncomputable def hp748389 := hp748383 67108860 67108864 244 1000000000000000 21780000 10890000 hp748384 BSN.pi_near_15 hp748388 rfl rfl

noncomputable def hp748390 := @hp748339 57 8388608 Bool.true 67108860 67108864 1 10890000 hp748382 (Enclosure.sfrac_false_div 1610863485 1048576) (hp748389 rfl rfl) rfl

noncomputable def hp748391 := @hp748336 16777215 16777216 39319913 5709496320000 536870880 536870912 3698 536870912 (@hp748337 Bool.true 16777215 16777216 39319913 5709496320000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000)) (@hp748338 629118608 91351941120000 16777215 16777216 39319913 5709496320000 (hp748390 rfl) rfl))

noncomputable def hp748392 := @hp748342 hp738659 824762104322 536870912 3642 536870912 (@hp748346 hp748340 hp748341 121001986099096028827 hp738659 (hp748348 rfl rfl rfl rfl rfl) (hp748351 (hp748381 rfl) (Enclosure.Real.IsNear.const Bool.true hp748344 hp748345) rfl rfl)) rfl

noncomputable def hp748393 := hp748335 (BSN.cos_quad_nat3 419 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 64572765 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) rfl rfl (hp748391 rfl) hp748392

noncomputable def hp748394 := nat_lit 2105529501292176685148964763426076617601576702653960783742722315421712640

noncomputable def hp748395 := nat_lit 70237835321205414823454435854250500424371741107193844585896732754176

noncomputable def hp748396 := nat_lit 5514368308793752223766145930362627116717728095560485643577800326632407296

noncomputable def hp748397 := BSN.sin_dyadic_bound_f 302566882 536870912 3 2 536870912 268435456 hp748394 hp708845 hp748395 hp748396 hp708848

noncomputable def hp748398 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 302566882) (BSN.sinEvenQ 536870912) 0 2 hp748394 hp708845 hp748395 rfl rfl rfl

noncomputable def hp748399 := hp748397 hp748395 286802620 rfl rfl rfl rfl rfl rfl rfl rfl (hp748398 rfl)

noncomputable def hp748400 := @BSN.binarySplit_of_base2 (BSN.sinOddP 302566882) (BSN.sinOddQ 536870912) 0 2 hp748396 hp708848 hp748395 rfl rfl rfl

noncomputable def hp748401 := nat_lit 17555305523760198380286118473841

noncomputable def hp748402 := BSN.sin_dyadic_bound_f 64729477 536870912 2 1 536870912 268435456 hp748401 hp708890 hp748401 hp748401 hp708891

noncomputable def hp748403 := @BSN.binarySplit_of_base (BSN.sinEvenP 64729477) (BSN.sinEvenQ 536870912) 0 1 hp748401 hp708890 hp748401 rfl rfl rfl

noncomputable def hp748404 := hp748402 hp748401 64572765 rfl rfl rfl rfl rfl rfl rfl rfl (hp748403 rfl)

noncomputable def hp748405 := @BSN.binarySplit_of_base (BSN.sinOddP 64729477) (BSN.sinOddQ 536870912) 0 1 hp748401 hp708891 hp748401 rfl rfl rfl

noncomputable def hp748406 := hp748393 hd4911 hd4913 hd4915 hd4917 hd4918 (hp748399 (hp748400 rfl) rfl rfl rfl rfl) (hp748404 (hp748405 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748407 := hp748331 (BSN.cos_quad_nat3 159 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 159600805 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) rfl rfl (hp748406 rfl rfl rfl rfl rfl) hp748392

noncomputable def hp748408 := nat_lit 18465825898626659668126686126718410200438934555072038973564403072477243362089254785992619872686708035209622716416

noncomputable def hp748409 := nat_lit 2402161913403952079907607063280119045874434707383108292080729720716901905240513292026462644523136645595136

noncomputable def hp748410 := nat_lit 111954402131722830046383606968135960433441812889523296349869826046147381454410404664202357749699381973822755307520

noncomputable def hp748411 := BSN.cos_dyadic_bound_f 604946344 536870912 4 3 536870912 268435456 hp748408 hp716712 hp748409 hp748410 hp716714

noncomputable def hp748412 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 604946344) (BSN.cosEvenQ 536870912) 0 3 hp748408 hp716712 hp748409 rfl rfl rfl

noncomputable def hp748413 := hp748411 hp748409 230613652 rfl rfl rfl rfl rfl rfl rfl rfl (hp748412 rfl)

noncomputable def hp748414 := @BSN.binarySplit_of_base3 (BSN.cosOddP 604946344) (BSN.cosOddQ 536870912) 0 3 hp748410 hp716714 hp748409 rfl rfl rfl

noncomputable def hp748415 := nat_lit 689603682353383899656228085760000

noncomputable def hp748416 := BSN.sin_dyadic_bound_f 162050320 536870912 2 1 536870912 268435456 hp748415 hp708890 hp748415 hp748415 hp708891

noncomputable def hp748417 := @BSN.binarySplit_of_base (BSN.sinEvenP 162050320) (BSN.sinEvenQ 536870912) 0 1 hp748415 hp708890 hp748415 rfl rfl rfl

noncomputable def hp748418 := hp748416 hp748415 159600805 rfl rfl rfl rfl rfl rfl rfl rfl (hp748417 rfl)

noncomputable def hp748419 := @BSN.binarySplit_of_base (BSN.sinOddP 162050320) (BSN.sinOddQ 536870912) 0 1 hp748415 hp708891 hp748415 rfl rfl rfl

noncomputable def hp748420 := hp748407 hd4920 hd4922 hd4924 hd4926 hd4918 (hp748413 (hp748414 rfl) rfl rfl rfl rfl) (hp748418 (hp748419 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748421 := hp748326 (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536797281 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) rfl rfl (hp748420 rfl rfl rfl rfl rfl) hp748392

noncomputable def hp748422 := nat_lit 2535341578993224315404600041980864526848663533419554875354521878849422401

noncomputable def hp748423 := nat_lit 329900042499859055599113559324154205706853060330370420610945936557121

noncomputable def hp748424 := nat_lit 7605364936894673228102601898823945272134576894138003885222343744675152961

noncomputable def hp748425 := BSN.cos_dyadic_bound_f 367111337 536870912 3 2 536870912 268435456 hp748422 hp708868 hp748423 hp748424 hp708870

noncomputable def hp748426 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 367111337) (BSN.cosEvenQ 536870912) 0 2 hp748422 hp708868 hp748423 rfl rfl rfl

noncomputable def hp748427 := hp748425 hp748423 416170984 rfl rfl rfl rfl rfl rfl rfl rfl (hp748426 rfl)

noncomputable def hp748428 := @BSN.binarySplit_of_base2 (BSN.cosOddP 367111337) (BSN.cosOddQ 536870912) 0 2 hp748424 hp708870 hp748423 rfl rfl rfl

noncomputable def hp748429 := nat_lit 173956658239974981384378836302560323967004254229272636030782957298302701523798960896421192310325941214630400618401

noncomputable def hp748430 := nat_lit 113929555485052067017042066309909459001447224063989618804583940089849181215328529801553347766160453921796001

noncomputable def hp748431 := nat_lit 868747278627097707061924340003762597082098677396413362087620062742089388062479761491009577726306406522397057478561

noncomputable def hp748432 := BSN.sin_dyadic_bound_f 834423193 536870912 4 3 536870912 268435456 hp748429 hp642702 hp748430 hp748431 hp642705

noncomputable def hp748433 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 834423193) (BSN.sinEvenQ 536870912) 0 3 hp748429 hp642702 hp748430 rfl rfl rfl

noncomputable def hp748434 := hp748432 hp748430 536797281 rfl rfl rfl rfl rfl rfl rfl rfl (hp748433 rfl)

noncomputable def hp748435 := @BSN.binarySplit_of_base3 (BSN.sinOddP 834423193) (BSN.sinOddQ 536870912) 0 3 hp748431 hp642705 hp748430 rfl rfl rfl

noncomputable def hp748436 := hp748421 hd4928 hd4930 hd4932 hd4934 hd4918 (hp748427 (hp748428 rfl) rfl rfl rfl rfl) (hp748434 (hp748435 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748437 := hp748321 (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 521378697 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) rfl rfl (hp748436 rfl rfl rfl rfl rfl) hp748392

noncomputable def hp748438 := nat_lit 132295229216896493573095159865538491235183410818108584291112102274441621617589815103408034029103119456243920790625

noncomputable def hp748439 := nat_lit 50181814568035573059320708833855915806230516626715407543596883348794171035209229597506082996774316650390625

noncomputable def hp748440 := nat_lit 660876457229675342278639965661026108170197032015900186424165472842455547774569675510686069894109227360529002390625

noncomputable def hp748441 := BSN.sin_dyadic_bound_f 779313495 536870912 4 3 536870912 268435456 hp748438 hp642702 hp748439 hp748440 hp642705

noncomputable def hp748442 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 779313495) (BSN.sinEvenQ 536870912) 0 3 hp748438 hp642702 hp748439 rfl rfl rfl

noncomputable def hp748443 := hp748441 hp748439 533060568 rfl rfl rfl rfl rfl rfl rfl rfl (hp748442 rfl)

noncomputable def hp748444 := @BSN.binarySplit_of_base3 (BSN.sinOddP 779313495) (BSN.sinOddQ 536870912) 0 3 hp748440 hp642705 hp748439 rfl rfl rfl

noncomputable def hp748445 := nat_lit 93189422690953490924734455486574878729373019182245465619627524712853675805367220712773636454535350161417246150656

noncomputable def hp748446 := nat_lit 17562166062187829526873688603097884883631724676301108668377569543469646229564115730043447384428092921286656

noncomputable def hp748447 := nat_lit 465649327510015135304127439823374217964063389113720747083095122904147534678544620880462635270314223946626318012416

noncomputable def hp748448 := BSN.sin_dyadic_bound_f 714027338 536870912 4 3 536870912 268435456 hp748445 hp642702 hp748446 hp748447 hp642705

noncomputable def hp748449 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 714027338) (BSN.sinEvenQ 536870912) 0 3 hp748445 hp642702 hp748446 rfl rfl rfl

noncomputable def hp748450 := hp748448 hp748446 521378697 rfl rfl rfl rfl rfl rfl rfl rfl (hp748449 rfl)

noncomputable def hp748451 := @BSN.binarySplit_of_base3 (BSN.sinOddP 714027338) (BSN.sinOddQ 536870912) 0 3 hp748447 hp642705 hp748446 rfl rfl rfl

noncomputable def hp748452 := hp748437 hd4936 hd4938 hd4940 hd4942 hd4918 (hp748443 (hp748444 rfl) rfl rfl rfl rfl) (hp748450 (hp748451 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748453 := hp748316 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 534386669 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) rfl rfl (hp748452 rfl rfl rfl rfl rfl) hp748392

noncomputable def hp748454 := nat_lit 5178105119907409089529760191095578585163394398551373268662037717195922625

noncomputable def hp748455 := nat_lit 424764197451846940150638212332871407921975132434816695580851230973121

noncomputable def hp748456 := nat_lit 13561016172009244625151032800525595455053206893610606952798205976377269441

noncomputable def hp748457 := BSN.sin_dyadic_bound_f 378894663 536870912 3 2 536870912 268435456 hp748454 hp708845 hp748455 hp748456 hp708848

noncomputable def hp748458 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 378894663) (BSN.sinEvenQ 536870912) 0 2 hp748454 hp708845 hp748455 rfl rfl rfl

noncomputable def hp748459 := hp748457 hp748455 348215571 rfl rfl rfl rfl rfl rfl rfl rfl (hp748458 rfl)

noncomputable def hp748460 := @BSN.binarySplit_of_base2 (BSN.sinOddP 378894663) (BSN.sinOddQ 536870912) 0 2 hp748456 hp708848 hp748455 rfl rfl rfl

noncomputable def hp748461 := nat_lit 140884923952576605704743615877117033538193511475800812308607822359361199870416084453050187219464550335582811918336

noncomputable def hp748462 := nat_lit 60587564004750380124681651082655163037059275340148727433586523496499489161364295998199735923796313775476736

noncomputable def hp748463 := nat_lit 703744643913873007627176618733228576065537930334840271812733666873238283824780503018923874050289346845624072605696

noncomputable def hp748464 := BSN.sin_dyadic_bound_f 791647706 536870912 4 3 536870912 268435456 hp748461 hp642702 hp748462 hp748463 hp642705

noncomputable def hp748465 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 791647706) (BSN.sinEvenQ 536870912) 0 3 hp748461 hp642702 hp748462 rfl rfl rfl

noncomputable def hp748466 := hp748464 hp748462 534386669 rfl rfl rfl rfl rfl rfl rfl rfl (hp748465 rfl)

noncomputable def hp748467 := @BSN.binarySplit_of_base3 (BSN.sinOddP 791647706) (BSN.sinOddQ 536870912) 0 3 hp748463 hp642705 hp748462 rfl rfl rfl

noncomputable def hp748468 := hp748453 hd4944 hd4946 hd4961 hd4963 hd4918 (hp748459 (hp748460 rfl) rfl rfl rfl rfl) (hp748466 (hp748467 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748469 := @hp748311 24241 33554432 (hp748468 rfl rfl rfl rfl rfl) (hp748468 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp748470 := @hp748309 Bool.true 391698971 268435456 24241 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 799149 1000)) (Enclosure.sfrac Bool.false 799149 1000) 11) hp748469

noncomputable def hp748471 := @Enclosure.Real.IsNear.mulLit_tf hp748300 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1))) 19983333 67108864 1

noncomputable def hp748472 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp748299 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp748473 := @hp748472 1 1 0 1 19983333 67108864 1 67108864 19983333 67108864 1

noncomputable def hp748474 := @Enclosure.Real.IsNear.of_eq (hp748299 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp748475 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 799149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748476 := @hp748474 (@Inv.inv Real Real.instInv (Real.sqrt hp748301)) Bool.false 19983333 67108864 1 67108864 (hp748475 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 799149 1000) 799149 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000))))

noncomputable def hp748477 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp748301)) Bool.false 19983333 67108864 1 67108864 19983333 67108864

noncomputable def hp748478 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp748301) Bool.false 225367795 67108864 7 67108864 225367795 67108864 7 67108864

noncomputable def hp748479 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 799149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748480 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 799149 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748481 := @hp748480 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 799149 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8535476318343

noncomputable def hp748482 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 799149 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 799149 1000 0

noncomputable def hp748483 := @hp748482 1 10680707 67108864 1 67108864 8535476318343 67108864000 799149 67108864000 (Enclosure.Real.IsNear.const Bool.false 799149 1000) hd4949

noncomputable def hp748484 := @hp748481 67108864000 799149 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 799149 1000) 799149 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000))) (hp748483 rfl)

noncomputable def hp748485 := @hp748479 8535476318343 67108864000 799149 67108864000 378419762 378419798 33554432 hp748484 rfl rfl rfl

noncomputable def hp748486 := @Enclosure.Real.IsNear.recentre' hp748301 Bool.false 756839560 67108864 36 67108864 94604945 8388608 9 16777216 (hp748485 rfl rfl rfl)

noncomputable def hp748487 := @Enclosure.Real.IsNear.sqrt_image hp748301 94604945 8388608 9 16777216 112683894 112683901 33554432 (hp748486 rfl) rfl rfl

noncomputable def hp748488 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp748301) 225367795 67108864 7 67108864 9991666 9991667 33554432 (hp748478 (hp748487 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp748489 := @hp748473 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp748476 (@hp748477 1 67108864 (hp748488 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp748490 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748491 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp748492 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1))) (hp748490 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748491 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp748493 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 799149 1000) 799149 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) rfl

noncomputable def hp748494 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748495 := @hp748494 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748491 (Enclosure.sfrac Bool.false 1 16)))) 193159969

noncomputable def hp748496 := @hp748495 33554432 483 4194304 2763351 33554432 244454929 45675970560000 533768793496119 1125899906842624 61754718105752857 1532631248189521920000

noncomputable def hp748497 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748498 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748499 := @hp748497 (@Neg.neg Real Real.instNeg hp748498) Bool.true 193159969 33554432 483 4194304 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748500 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748501 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp748502 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp748503 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 29282873) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false

noncomputable def hp748504 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1))) Bool.false 2060599005166067063635

noncomputable def hp748505 := nat_lit 242874678721429919521620991

noncomputable def hp748506 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp748507 := @Enclosure.Real.IsNear.subLit_ff_p hp748301 (Enclosure.sfrac Bool.false 11 1) 94604945 8388608 9 16777216 11 1 0

noncomputable def hp748508 := @hp748506 500000000000000 2330257 8388608 9 16777216 2060599005166067063635 1180591620717411303424 hp748505 hp631123 hd4948 (@hp748507 1 2330257 2330257 8388608 9 16777216 (hp748486 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp748509 := @hp748503 29282873 16777216 227 67108864 Bool.true 5828847 33554432 1 10890000 (@hp748504 1180591620717411303424 hp748505 hp631123 29282873 16777216 227 67108864 (hp748508 rfl) rfl) (Enclosure.sfrac_false_div 29282873 16777216)

noncomputable def hp748510 := nat_lit 92626231994179734172872586468866613862986555346566498257461026001962986289414655102531459431201

noncomputable def hp748511 := nat_lit 397524781465176777587551539858372193769255417995187223645367134060747234400183675333458721

noncomputable def hp748512 := nat_lit 559872369935572317607292027691937139528725731775999910382194457389520374848709314114801858853665

noncomputable def hp748513 := BSN.cos_dyadic_bound_t 29282873 16777216 4 3 33554432 10890000 hp748510 hp633087 hp748511 hp748512 hp633090

noncomputable def hp748514 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 29282873) (BSN.cosEvenQ 16777216) 0 3 hp748510 hp633087 hp748511 rfl rfl rfl

noncomputable def hp748515 := hp748513 hp748511 5828847 rfl rfl rfl rfl rfl rfl rfl rfl (hp748514 rfl)

noncomputable def hp748516 := @BSN.binarySplit_of_base3 (BSN.cosOddP 29282873) (BSN.cosOddQ 16777216) 0 3 hp748512 hp633090 hp748511 rfl rfl rfl

noncomputable def hp748517 := hp748509 (hp748515 (hp748516 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp748518 := @hp748501 5828847 33554432 158696179 45675970560000 (@hp748502 5828847 33554432 2539138864 730815528960000 5828847 33554432 158696179 45675970560000 hp748517 rfl)

noncomputable def hp748519 := @hp748500 5828847 33554432 158696179 45675970560000 193156105 193163833 33554432 hp748518 rfl rfl rfl

noncomputable def hp748520 := @Enclosure.Real.IsNear.recentre' hp748498 Bool.false 386319938 67108864 7728 67108864 193159969 33554432 483 4194304 (hp748519 rfl rfl rfl)

noncomputable def hp748521 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748491 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp748522 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748491 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 110947325)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp748523 := nat_lit 16372935376550458116163140605

noncomputable def hp748524 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748491 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp748523

noncomputable def hp748525 := nat_lit 6338604812156979721179160883280307

noncomputable def hp748526 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748491 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp748527 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp748528 := @hp748527 (Enclosure.sfrac Bool.false 1 16) 14117514826207 70368744177664 234884277 281474976710656 1 16 0

noncomputable def hp748529 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)) 5430097686049

noncomputable def hp748530 := @hp748529 70368744177664 83889333 281474976710656 2330257 8388608 9 16777216 118426297811238649856 14117514826207 70368744177664 234884277

noncomputable def hp748531 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)) 2330257 8388608 9

noncomputable def hp748532 := @hp748531 16777216 2330257 8388608 9 16777216 5430097686049 70368744177664 83889333 281474976710656 (@hp748507 1 2330257 2330257 8388608 9 16777216 (hp748486 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp748533 := hp748532 (@hp748507 1 2330257 2330257 8388608 9 16777216 (hp748486 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp748534 := @hp748530 281474976710656 (hp748533 rfl) (@hp748507 1 2330257 2330257 8388608 9 16777216 (hp748486 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp748535 := @hp748526 500000000000000 18515561337311 70368744177664 234884277 281474976710656 hp748523 hp619387 hp748525 hp631148 hd4948 (@hp748528 1 296248981396976 18515561337311 70368744177664 234884277 281474976710656 (hp748534 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp748536 := @hp748522 110947325 67108864 353 67108864 Bool.true 2763351 33554432 1 10890000 (@hp748524 hp619387 hp748525 hp631148 110947325 67108864 353 67108864 (hp748535 rfl) rfl) (Enclosure.sfrac_true_div 110947325 67108864)

noncomputable def hp748537 := nat_lit 1249569082867566648010653897457700032848150207577143738719148915028063705084203052033113219816806640625

noncomputable def hp748538 := nat_lit 3478580254454968659691773110357616893330508348354099981587968192659274112588810980319976806640625

noncomputable def hp748539 := nat_lit 7558328203536929050594789279751780807627245550601721150268671088466299700771065264502373245672806640625

noncomputable def hp748540 := BSN.cos_dyadic_bound_t 110947325 67108864 4 3 33554432 10890000 hp748537 hp745658 hp748538 hp748539 hp745661

noncomputable def hp748541 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 110947325) (BSN.cosEvenQ 67108864) 0 3 hp748537 hp745658 hp748538 rfl rfl rfl

noncomputable def hp748542 := hp748540 hp748538 2763351 rfl rfl rfl rfl rfl rfl rfl rfl (hp748541 rfl)

noncomputable def hp748543 := @BSN.binarySplit_of_base3 (BSN.cosOddP 110947325) (BSN.cosOddQ 67108864) 0 3 hp748539 hp745661 hp748538 rfl rfl rfl

noncomputable def hp748544 := hp748536 (BSN.cos_neg_of_bound 110947325 67108864 Bool.true 2763351 33554432 1 10890000 (hp748542 (hp748543 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp748545 := hp748496 (hp748499 (@Enclosure.Real.IsNear.neg hp748498 Bool.false 193159969 33554432 483 4194304 (hp748520 rfl))) (@hp748521 2763351 33554432 3911278864 730815528960000 2763351 33554432 244454929 45675970560000 (hp748544 rfl) rfl)

noncomputable def hp748546 := @hp748471 67108864 533768793496119 1125899906842624 61754718105752857 1532631248189521920000 10666479545441180184627 75557863725914323419136 308697937688313313718497 hp740088 (hp748489 rfl) (@hp748492 Bool.false 533768793496119 1125899906842624 61754718105752857 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748301 (Enclosure.sfrac Bool.false 11 1)) (hp748493 rfl (hp748304 rfl rfl))) (hp748545 rfl))

noncomputable def hp748547 := @hp748298 hp748296 hp740088 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 799149 1000))) (@hp748303 hp748296 hp740088 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 799149 1000) 11 (hp748304 rfl rfl)) (@hp748307 hp748296 hp740088 hp748470 (hp748546 rfl) rfl rfl))

theorem hd5004 : hp748297 hp740088 := hp748547

noncomputable def hp748548 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 800445 1000)) Bool.false 4336259190851626260111 1180591620717411303424 209342818390221548923717

noncomputable def hp748549 := nat_lit 285703172213613535428608000

noncomputable def hp748550 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 800445 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 800445 1000)) Bool.false 4336259190851626260111 1180591620717411303424

noncomputable def hp748551 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 800445 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748552 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp748551 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp748553 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 800445 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748554 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp748552 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp748555 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 800445 1000)) hp748554 Bool.false 4336259190851626260111 1180591620717411303424

noncomputable def hp748556 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 800445 1000) 800445 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl

noncomputable def hp748557 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp748552 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp748558 := nat_lit 582002856615223661737235447808

noncomputable def hp748559 := @hp748557 474344541 134217728 194245 268435456 163880483639069693583 1180591620717411303424 2602570609267600763717 hp748549 hp748558 4336259190851626260111 1180591620717411303424

noncomputable def hp748560 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) 11)

noncomputable def hp748561 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) 11) hp748560

noncomputable def hp748562 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) 11)

noncomputable def hp748563 := @hp748562 948689082 536870912 194245 536870912 948689082 536870912 194245 536870912 1018647145315565568 474344541 134217728

noncomputable def hp748564 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp748565 := hp748564 BSN.quadSignNeg 9 10 11 800445 1000 193 241 536870912 268435456 9007199254740992

noncomputable def hp748566 := hp748565 Bool.false 826448158098 3648 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp748567 := hp748566 Bool.false 1197863183 166754 Bool.true 294944366 Bool.true 774012775 28296951008113761 1 Bool.false 280330229

noncomputable def hp748568 := hp748567 Bool.true Bool.false 532404183 Bool.true Bool.false 948689082 194245 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 280330229 536870912) BSN.abs_quadSignNeg

noncomputable def hp748569 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp748570 := hp748569 BSN.quadSignPos 7 8 9 800445 1000 79 139 536870912 268435456 9007199254740992

noncomputable def hp748571 := hp748570 Bool.false 826448158098 3648 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp748572 := hp748571 Bool.false 883460382 136188 Bool.true 540103331 Bool.true 556768790 28296951008113761 1 Bool.false 453499579

noncomputable def hp748573 := hp748572 Bool.false Bool.false 462199459 Bool.false Bool.false 1197863183 166754 BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 453499579 536870912) BSN.abs_quadSignPos

noncomputable def hp748574 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp748575 := hp748574 BSN.quadSignPos 5 6 7 800445 1000 66 11 536870912 268435456 9007199254740992

noncomputable def hp748576 := hp748575 Bool.false 826448158098 3648 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp748577 := hp748576 Bool.false 735142099 101205 Bool.false 806486294 Bool.true 502303910 28296951008113761 1 Bool.false 36799684

noncomputable def hp748578 := hp748577 Bool.true Bool.false 432161486 Bool.false Bool.false 883460382 136188 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 66 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 36799684 536870912) BSN.abs_quadSignPos

noncomputable def hp748579 := hp748564 BSN.quadSignPos 3 4 5 800445 1000 273 159 536870912 268435456 9007199254740992

noncomputable def hp748580 := hp748579 Bool.false 826448158098 3648 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp748581 := hp748580 Bool.false 710790213 59820 Bool.false 483122873 Bool.false 728281838 28296951008113761 1 Bool.false 420507543

noncomputable def hp748582 := hp748581 Bool.true Bool.false 524594173 Bool.false Bool.false 735142099 101205 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 273 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 420507543 536870912) BSN.abs_quadSignPos

noncomputable def hp748583 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp748584 := hp748583 BSN.quadSignPos 1 2 3 800445 1000 626 420 536870912 268435456 9007199254740992

noncomputable def hp748585 := hp748584 Bool.false 826448158098 3648 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp748586 := hp748585 Bool.false 536870760 3706 Bool.false 663024616 Bool.false 143070779 28296951008113761 1 Bool.false 176920654

noncomputable def hp748587 := hp748586 Bool.true Bool.false 517919991 Bool.false Bool.false 710790213 59820 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 626 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 176920654 536870912) BSN.abs_quadSignPos

noncomputable def hp748588 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) 1) Bool.false

noncomputable def hp748589 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)))

noncomputable def hp748590 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000))) Bool.false 67108845 67108864

noncomputable def hp748591 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 51653009881) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 51653009881 33554432

noncomputable def hp748592 := nat_lit 3734435422663794134806066620216065711236214297684583

noncomputable def hp748593 := nat_lit 2425935288891556291314292136628369014502553812992

noncomputable def hp748594 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) Bool.false hp748592 hp748593 2203591887267536077

noncomputable def hp748595 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 800445 4000) (Real.log (Enclosure.sfrac Bool.false 2562849792100 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1600890))))))

noncomputable def hp748596 := nat_lit 157724495644891092884111173500000000

noncomputable def hp748597 := nat_lit 757498841431336841148063880243245000000

noncomputable def hp748598 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp748595 (Enclosure.sfrac Bool.false 800445 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 800445 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp748596 hp748597)) Bool.false

noncomputable def hp748599 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 800445 1000) 800445 1000 2562849792100 16000000 1600890

noncomputable def hp748600 := hp748599 4000 2000 hp748596 hp748597 (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl rfl rfl rfl

noncomputable def hp748601 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp748595 (Enclosure.sfrac Bool.false 800445 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 800445 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp748596 hp748597) 221848018186835571303 144115188075855872

noncomputable def hp748602 := nat_lit 168049594019870736066272997909722957005629643395806235000000

noncomputable def hp748603 := @hp748601 2203591887267536077 324403200000000000000000 hp748596 hp748597 0 1 hp748602 hp748592 hp748593 2203591887267536077 324403200000000000000000

noncomputable def hp748604 := @Enclosure.Real.IsNear.subLit_ff_p (hp748595 (Enclosure.sfrac Bool.false 800445 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 800445 2000) (Real.log Real.pi)) 7196847739868458281999 3602879701896396800 183737769439687 79200000000000000000

noncomputable def hp748605 := nat_lit 74439842405849374724676648960000

noncomputable def hp748606 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 800445 4000) (Real.log (Enclosure.sfrac Bool.false 2562849792100 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1600890))))))

noncomputable def hp748607 := @hp748606 (Enclosure.sfrac Bool.false 800445 2000) 8638801261360688950287 3602879701896396800 183737769439687 79200000000000000000 800445 2000 0

noncomputable def hp748608 := nat_lit 14393695479736916563998000

noncomputable def hp748609 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 800445 4000) (Real.log (Enclosure.sfrac Bool.false 2562849792100 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1600890))))) 8640215546297222407887

noncomputable def hp748610 := nat_lit 19452851070795884790552322278137266176

noncomputable def hp748611 := @hp748609 3602879701896396800 667038487909219 290400000000000000000 883928085333411 2251799813685248 200000001089 8712000000000000000 hp748610 8638801261360688950287 3602879701896396800 183737769439687

noncomputable def hp748612 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 800445 4000) (Real.log (Enclosure.sfrac Bool.false 2562849792100 16000000)) 800445 4000 0 1 53971325614484583 4503599627370496

noncomputable def hp748613 := nat_lit 115902539217989193940598784

noncomputable def hp748614 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2562849792100) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp748613 hp617687

noncomputable def hp748615 := BSN.log_rat_reduce_isNear 2562849792100 16000000 17 5125699584200 4194304000000 53831940 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp748616 := nat_lit 1075240963380328770570752545704644019502527103408517375396918169705000000000000

noncomputable def hp748617 := nat_lit 3601088632129400698471708209076399790575017159684689452564049991000000000000

noncomputable def hp748618 := nat_lit 153008773034614566847117220124723670383664931269826011852815000000000000

noncomputable def hp748619 := BSN.log_dyadic_bound 465697792100 4660001792100 4 3 hp748616 268435456 87120000 hp748617 hp748618 53831940 5125699584200

noncomputable def hp748620 := hp748619 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp748621 := @BSN.binarySplit_of_base3 (BSN.artanhP 465697792100) (BSN.artanhQ 4660001792100) 0 3 hp748617 hp748616 hp748618 rfl rfl rfl

noncomputable def hp748622 := hp748615 rfl rfl rfl rfl (hp748620 (hp748621 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp748623 := @hp748612 12500018513 1089000000000000000 8640215546297222407887 3602879701896396800 667038487909219 290400000000000000000 (Enclosure.Real.IsNear.const Bool.false 800445 4000) (BSN.isNear_log_sfrac 2562849792100 16000000 53971325614484583 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp748614 1000001481040000 87120000000000000000000 53971325614484583 4503599627370496 12500018513 1089000000000000000 (hp748622 rfl rfl rfl) rfl)) rfl

noncomputable def hp748624 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1600890)))) 1 4

noncomputable def hp748625 := @hp748624 0 1 883928085333411 562949953421312 200000001089 2178000000000000000 883928085333411 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp748626 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1600890))) 884279719003555 562949953421312 1

noncomputable def hp748627 := @hp748626 2000000000000000 20959 33554432 1 10890000 29659704832210136727552 883928085333411 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp748628 := BSN.arctan_dyadic_bound_f 1000 1600890 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp748629 := hp748628 1 20959 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1600890) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1600890) 0 0 rfl)

noncomputable def hp748630 := hp748625 (hp748627 (hp748629 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp748631 := @hp748604 6149140317729 13421772800 480267 107374182400 hp748605 221848018186835571303 144115188075855872 2203591887267536077 324403200000000000000000 (@hp748607 1 hp748608 7196847739868458281999 3602879701896396800 183737769439687 79200000000000000000 (@hp748611 79200000000000000000 hp748623 hp748630 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 800445 2000) rfl rfl)

noncomputable def hp748632 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 800445 2000) (Real.log Real.pi) 800445 2000 0 1 38410761 33554432

noncomputable def hp748633 := hp748631 (@hp748632 3 268435456 6149140317729 13421772800 480267 107374182400 (Enclosure.Real.IsNear.const Bool.false 800445 2000) hd4909 rfl) rfl

noncomputable def hp748634 := @hp748594 324403200000000000000000 51653009881 33554432 457 67108864 (@hp748598 hp748592 hp748593 2203591887267536077 324403200000000000000000 (hp748600 rfl rfl rfl rfl rfl) (hp748603 (hp748633 rfl) (Enclosure.Real.IsNear.const Bool.true hp748596 hp748597) rfl rfl)) rfl

noncomputable def hp748635 := nat_lit 7592290304406082648276992

noncomputable def hp748636 := BSN.cos_reduce3 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 51653009881) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp748635) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp748637 := BSN.sin_reduce_arg_pos_rat_q3 51653009881 33554432 226375608064910080 72057594037927936 244 hp748635 hp619237 rfl rfl rfl rfl

noncomputable def hp748638 := nat_lit 14352974173956658812149680195113259743881620813123955809584652227563090142230137553208914086446686549953692080490941402785641372383216467899201

noncomputable def hp748639 := nat_lit 10192389466067450712580897005031965028462086825870427702206615682102657313854404937322631954104859454557712215950282727094167836413064001

noncomputable def hp748640 := nat_lit 71675863523389484995283690049395437735845008402583848218999487282698892900671601575317285953381078033232737309687028842782830534507255952765761

noncomputable def hp748641 := BSN.sin_dyadic_bound_f 215785868943 137438953472 4 3 67108864 21801270 hp748638 hp737934 hp748639 hp748640 hp737937

noncomputable def hp748642 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215785868943) (BSN.sinEvenQ 137438953472) 0 3 hp748638 hp737934 hp748639 rfl rfl rfl

noncomputable def hp748643 := hp748641 hp748639 67108845 rfl rfl rfl rfl rfl rfl rfl rfl (hp748642 rfl)

noncomputable def hp748644 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215785868943) (BSN.sinOddQ 137438953472) 0 3 hp748640 hp737937 hp748639 rfl rfl rfl

noncomputable def hp748645 := @BSN.sin_arg_round Bool.false 67108845 67108864 hp748635 hp619237 215785868943 137438953472 21801270 21780000 (hp748643 (hp748644 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748646 := hp748636 67108845 67108864 244 1000000000000000 21780000 10890000 hp748637 BSN.pi_near_15 hp748645 rfl rfl

noncomputable def hp748647 := @hp748591 457 67108864 Bool.false 67108845 67108864 1 10890000 hp748634 (Enclosure.sfrac_false_div 51653009881 33554432) (hp748646 rfl rfl) rfl

noncomputable def hp748648 := @hp748588 67108845 67108864 315239929 45675970560000 536870760 536870912 3706 536870912 (@hp748589 Bool.false 67108845 67108864 315239929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000)) (@hp748590 5043838864 730815528960000 67108845 67108864 315239929 45675970560000 (hp748647 rfl) rfl))

noncomputable def hp748649 := @hp748594 324403200000000000000000 826448158098 536870912 3648 536870912 (@hp748598 hp748592 hp748593 2203591887267536077 324403200000000000000000 (hp748600 rfl rfl rfl rfl rfl) (hp748603 (hp748633 rfl) (Enclosure.Real.IsNear.const Bool.true hp748596 hp748597) rfl rfl)) rfl

noncomputable def hp748650 := hp748587 (BSN.cos_quad_nat0 420 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 517919991 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl rfl (hp748648 rfl) hp748649

noncomputable def hp748651 := nat_lit 26656575779878795034592911195658127423683619234233839782690838932180198422301277631516555983641961588316266561536

noncomputable def hp748652 := nat_lit 7216985490434032170764768986004128174817571996106197069201458375921495113435144969475946535726516698873856

noncomputable def hp748653 := nat_lit 161567452553589421846452505586543027274941674734932674129452569490720887793751432772737818672051906047608681922560

noncomputable def hp748654 := BSN.cos_dyadic_bound_f 663024616 536870912 4 3 536870912 268435456 hp748651 hp716712 hp748652 hp748653 hp716714

noncomputable def hp748655 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 663024616) (BSN.cosEvenQ 536870912) 0 3 hp748651 hp716712 hp748652 rfl rfl rfl

noncomputable def hp748656 := hp748654 hp748652 176920654 rfl rfl rfl rfl rfl rfl rfl rfl (hp748655 rfl)

noncomputable def hp748657 := @BSN.binarySplit_of_base3 (BSN.cosOddP 663024616) (BSN.cosOddQ 536870912) 0 3 hp748653 hp716714 hp748652 rfl rfl rfl

noncomputable def hp748658 := nat_lit 418990105647919794157845322919281

noncomputable def hp748659 := BSN.cos_dyadic_bound_f 143070779 536870912 2 1 536870912 268435456 hp748658 hp708767 hp748658 hp748658 hp708768

noncomputable def hp748660 := @BSN.binarySplit_of_base (BSN.cosEvenP 143070779) (BSN.cosEvenQ 536870912) 0 1 hp748658 hp708767 hp748658 rfl rfl rfl

noncomputable def hp748661 := hp748659 hp748658 517919991 rfl rfl rfl rfl rfl rfl rfl rfl (hp748660 rfl)

noncomputable def hp748662 := @BSN.binarySplit_of_base (BSN.cosOddP 143070779) (BSN.cosOddQ 536870912) 0 1 hp748658 hp708768 hp748658 rfl rfl rfl

noncomputable def hp748663 := hp748650 hd4911 hd4913 hd4915 hd4917 hd4918 (hp748656 (hp748657 rfl) rfl rfl rfl rfl) (hp748661 (hp748662 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748664 := hp748582 (BSN.cos_quad_nat3 159 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 524594173 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl rfl (hp748663 rfl rfl rfl rfl rfl) hp748649

noncomputable def hp748665 := nat_lit 13689445258821871535198466769368259814105814979075379765409060590410816705

noncomputable def hp748666 := nat_lit 2967978796022738540448744329661357096446235500845132074836756462066881

noncomputable def hp748667 := nat_lit 35848503712197055301216210238478371601644792944862721552712089654899268801

noncomputable def hp748668 := BSN.sin_dyadic_bound_f 483122873 536870912 3 2 536870912 268435456 hp748665 hp708845 hp748666 hp748667 hp708848

noncomputable def hp748669 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 483122873) (BSN.sinEvenQ 536870912) 0 2 hp748665 hp708845 hp748666 rfl rfl rfl

noncomputable def hp748670 := hp748668 hp748666 420507543 rfl rfl rfl rfl rfl rfl rfl rfl (hp748669 rfl)

noncomputable def hp748671 := @BSN.binarySplit_of_base2 (BSN.sinOddP 483122873) (BSN.sinOddQ 536870912) 0 2 hp748667 hp708848 hp748666 rfl rfl rfl

noncomputable def hp748672 := nat_lit 100865379110388065820613489507227857979363702859177957977576713205649188532660946338625081565927773711290185158656

noncomputable def hp748673 := nat_lit 22263516155528195805918738095719078791142363826556331903034243159249832767403813607412766314935145313734656

noncomputable def hp748674 := nat_lit 503978084897478102476667409933727828396981326808678693316973789250844214944260875761818266271547915692309601980416

noncomputable def hp748675 := BSN.sin_dyadic_bound_f 728281838 536870912 4 3 536870912 268435456 hp748672 hp642702 hp748673 hp748674 hp642705

noncomputable def hp748676 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 728281838) (BSN.sinEvenQ 536870912) 0 3 hp748672 hp642702 hp748673 rfl rfl rfl

noncomputable def hp748677 := hp748675 hp748673 524594173 rfl rfl rfl rfl rfl rfl rfl rfl (hp748676 rfl)

noncomputable def hp748678 := @BSN.binarySplit_of_base3 (BSN.sinOddP 728281838) (BSN.sinOddQ 536870912) 0 3 hp748674 hp642705 hp748673 rfl rfl rfl

noncomputable def hp748679 := hp748664 hd4920 hd4922 hd4924 hd4926 hd4918 (hp748670 (hp748671 rfl) rfl rfl rfl rfl) (hp748677 (hp748678 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748680 := hp748578 (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 432161486 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl rfl (hp748679 rfl rfl rfl rfl rfl) hp748649

noncomputable def hp748681 := nat_lit 58450420380457299441456338905113007205821190282327627987433958631296931055193508440132122355088224277894158422016

noncomputable def hp748682 := nat_lit 75711856060028362991902342335110790972964516023212697143185722403359744687270099199939434213243525651828736

noncomputable def hp748683 := nat_lit 353884450977797078913326259004263788310565518902972665498174403220916289468962627184332743754597683678502768414720

noncomputable def hp748684 := BSN.cos_dyadic_bound_f 806486294 536870912 4 3 536870912 268435456 hp748681 hp716712 hp748682 hp748683 hp716714

noncomputable def hp748685 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 806486294) (BSN.cosEvenQ 536870912) 0 3 hp748681 hp716712 hp748682 rfl rfl rfl

noncomputable def hp748686 := hp748684 hp748682 36799684 rfl rfl rfl rfl rfl rfl rfl rfl (hp748685 rfl)

noncomputable def hp748687 := @BSN.binarySplit_of_base3 (BSN.cosOddP 806486294) (BSN.cosOddQ 536870912) 0 3 hp748683 hp716714 hp748682 rfl rfl rfl

noncomputable def hp748688 := nat_lit 15996963534637385200661931952642211685269007192780510970068529391931040000

noncomputable def hp748689 := nat_lit 4052588150309251914119725423665519109363196916050255334626592100000000

noncomputable def hp748690 := nat_lit 41890247924187889117682199368138905478098906995608685460590086305943200000

noncomputable def hp748691 := BSN.sin_dyadic_bound_f 502303910 536870912 3 2 536870912 268435456 hp748688 hp708845 hp748689 hp748690 hp708848

noncomputable def hp748692 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 502303910) (BSN.sinEvenQ 536870912) 0 2 hp748688 hp708845 hp748689 rfl rfl rfl

noncomputable def hp748693 := hp748691 hp748689 432161486 rfl rfl rfl rfl rfl rfl rfl rfl (hp748692 rfl)

noncomputable def hp748694 := @BSN.binarySplit_of_base2 (BSN.sinOddP 502303910) (BSN.sinOddQ 536870912) 0 2 hp748690 hp708848 hp748689 rfl rfl rfl

noncomputable def hp748695 := hp748680 hd4928 hd4930 hd4932 hd4934 hd4918 (hp748686 (hp748687 rfl) rfl rfl rfl rfl) (hp748693 (hp748694 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748696 := hp748573 (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 462199459 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl rfl (hp748695 rfl rfl rfl rfl rfl) hp748649

noncomputable def hp748697 := nat_lit 21385321706882766800397031979079676255026626887710051928023372523148570785

noncomputable def hp748698 := nat_lit 7241271748013734739106033582515941278667606125714226218074406274887841

noncomputable def hp748699 := nat_lit 55997451935196176525747959700360792953475703819798979635708140902848819361

noncomputable def hp748700 := BSN.sin_dyadic_bound_f 540103331 536870912 3 2 536870912 268435456 hp748697 hp708845 hp748698 hp748699 hp708848

noncomputable def hp748701 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 540103331) (BSN.sinEvenQ 536870912) 0 2 hp748697 hp708845 hp748698 rfl rfl rfl

noncomputable def hp748702 := hp748700 hp748698 453499579 rfl rfl rfl rfl rfl rfl rfl rfl (hp748701 rfl)

noncomputable def hp748703 := @BSN.binarySplit_of_base2 (BSN.sinOddP 540103331) (BSN.sinOddQ 536870912) 0 2 hp748699 hp708848 hp748698 rfl rfl rfl

noncomputable def hp748704 := nat_lit 24150543171625190064459284524244205482986719733020610248937025074951840000

noncomputable def hp748705 := nat_lit 9234195422075250764070589059894498993444632271617138684231616100000000

noncomputable def hp748706 := nat_lit 63236471990239756905680107085971185171356784181852313379822500198807200000

noncomputable def hp748707 := BSN.sin_dyadic_bound_f 556768790 536870912 3 2 536870912 268435456 hp748704 hp708845 hp748705 hp748706 hp708848

noncomputable def hp748708 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 556768790) (BSN.sinEvenQ 536870912) 0 2 hp748704 hp708845 hp748705 rfl rfl rfl

noncomputable def hp748709 := hp748707 hp748705 462199459 rfl rfl rfl rfl rfl rfl rfl rfl (hp748708 rfl)

noncomputable def hp748710 := @BSN.binarySplit_of_base2 (BSN.sinOddP 556768790) (BSN.sinOddQ 536870912) 0 2 hp748706 hp708848 hp748705 rfl rfl rfl

noncomputable def hp748711 := hp748696 hd4936 hd4938 hd4940 hd4942 hd4918 (hp748702 (hp748703 rfl) rfl rfl rfl rfl) (hp748709 (hp748710 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748712 := hp748568 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 532404183 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl rfl (hp748711 rfl rfl rfl rfl rfl) hp748649

noncomputable def hp748713 := nat_lit 1901230553074908754248656068780116962437495483791707855254361166360428800

noncomputable def hp748714 := nat_lit 57269163262406308633353868873689318858020025041916621394858883236096

noncomputable def hp748715 := nat_lit 4979320631789002841389645226255463214153384710842500327326782807037788416

noncomputable def hp748716 := BSN.sin_dyadic_bound_f 294944366 536870912 3 2 536870912 268435456 hp748713 hp708845 hp748714 hp748715 hp708848

noncomputable def hp748717 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 294944366) (BSN.sinEvenQ 536870912) 0 2 hp748713 hp708845 hp748714 rfl rfl rfl

noncomputable def hp748718 := hp748716 hp748714 280330229 rfl rfl rfl rfl rfl rfl rfl rfl (hp748717 rfl)

noncomputable def hp748719 := @BSN.binarySplit_of_base2 (BSN.sinOddP 294944366) (BSN.sinOddQ 536870912) 0 2 hp748715 hp708848 hp748714 rfl rfl rfl

noncomputable def hp748720 := nat_lit 128727328094751990440681190943166069773090081182489706060947602551277207771435102388909860485871354133923775390625

noncomputable def hp748721 := nat_lit 46235711452297809222407880298373914813928054322154275998026182015249774022617584748701019346714019775390625

noncomputable def hp748722 := nat_lit 643068821999602741890574046487589831724516441778527988673772790220157779100467122716690968046296983813539775390625

noncomputable def hp748723 := BSN.sin_dyadic_bound_f 774012775 536870912 4 3 536870912 268435456 hp748720 hp642702 hp748721 hp748722 hp642705

noncomputable def hp748724 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 774012775) (BSN.sinEvenQ 536870912) 0 3 hp748720 hp642702 hp748721 rfl rfl rfl

noncomputable def hp748725 := hp748723 hp748721 532404183 rfl rfl rfl rfl rfl rfl rfl rfl (hp748724 rfl)

noncomputable def hp748726 := @BSN.binarySplit_of_base3 (BSN.sinOddP 774012775) (BSN.sinOddQ 536870912) 0 3 hp748722 hp642705 hp748721 rfl rfl rfl

noncomputable def hp748727 := hp748712 hd4944 hd4946 hd4961 hd4963 hd4918 (hp748718 (hp748719 rfl) rfl rfl rfl rfl) (hp748725 (hp748726 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748728 := @hp748563 194245 268435456 (hp748727 rfl rfl rfl rfl rfl) (hp748727 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp748729 := @hp748561 Bool.false 474344541 134217728 194245 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 800445 1000)) (Enclosure.sfrac Bool.false 800445 1000) 11) hp748728

noncomputable def hp748730 := @Enclosure.Real.IsNear.mulLit_tf hp748552 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1))) 19975239 67108864 1

noncomputable def hp748731 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp748551 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp748732 := @hp748731 1 1 0 1 19975239 67108864 1 67108864 19975239 67108864 1

noncomputable def hp748733 := @Enclosure.Real.IsNear.of_eq (hp748551 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp748734 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 800445 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748735 := @hp748733 (@Inv.inv Real Real.instInv (Real.sqrt hp748553)) Bool.false 19975239 67108864 1 67108864 (hp748734 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 800445 1000) 800445 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000))))

noncomputable def hp748736 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp748553)) Bool.false 19975239 67108864 1 67108864 19975239 67108864

noncomputable def hp748737 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp748553) Bool.false 225459111 67108864 7 67108864 225459111 67108864 7 67108864

noncomputable def hp748738 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 800445 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748739 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 800445 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748740 := @hp748739 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 800445 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 1709863702923

noncomputable def hp748741 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 800445 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 800445 1000 0

noncomputable def hp748742 := @hp748741 1 10680707 67108864 1 67108864 1709863702923 13421772800 160089 13421772800 (Enclosure.Real.IsNear.const Bool.false 800445 1000) hd4949

noncomputable def hp748743 := @hp748740 13421772800 160089 13421772800 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 800445 1000) 800445 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000))) (hp748742 rfl)

noncomputable def hp748744 := @hp748738 1709863702923 13421772800 160089 13421772800 378726484 378726520 33554432 hp748743 rfl rfl rfl

noncomputable def hp748745 := @Enclosure.Real.IsNear.recentre' hp748553 Bool.false 757453004 67108864 36 67108864 189363251 16777216 9 16777216 (hp748744 rfl rfl rfl)

noncomputable def hp748746 := @Enclosure.Real.IsNear.sqrt_image hp748553 189363251 16777216 9 16777216 112729552 112729559 33554432 (hp748745 rfl) rfl rfl

noncomputable def hp748747 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp748553) 225459111 67108864 7 67108864 9987619 9987620 33554432 (hp748737 (hp748746 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp748748 := @hp748732 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp748735 (@hp748736 1 67108864 (hp748747 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp748749 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748750 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp748751 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1))) (hp748749 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748750 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp748752 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 800445 1000) 800445 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl

noncomputable def hp748753 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748754 := @hp748753 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748750 (Enclosure.sfrac Bool.false 1 16)))) 18239499

noncomputable def hp748755 := @hp748754 4194304 2205 33554432 449803 4194304 247177429 45675970560000 8204181368697 17592186044416 5207617425125057 170292360909946880000

noncomputable def hp748756 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748757 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748758 := @hp748756 (@Neg.neg Real Real.instNeg hp748757) Bool.true 18239499 4194304 2205 33554432 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748759 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp748760 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp748761 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp748762 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 60492937) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp748763 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1))) Bool.false 4256812032318238325625

noncomputable def hp748764 := nat_lit 242874678722747280480584703

noncomputable def hp748765 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp748766 := @Enclosure.Real.IsNear.subLit_ff_p hp748553 (Enclosure.sfrac Bool.false 11 1) 189363251 16777216 9 16777216 11 1 0

noncomputable def hp748767 := @hp748765 500000000000000 4813875 16777216 9 16777216 4256812032318238325625 2361183241434822606848 hp748764 hp631123 hd4948 (@hp748766 1 4813875 4813875 16777216 9 16777216 (hp748745 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp748768 := @hp748762 60492937 33554432 227 67108864 Bool.true 7716083 33554432 1 10890000 (@hp748763 2361183241434822606848 hp748764 hp631123 60492937 33554432 227 67108864 (hp748767 rfl) rfl) (Enclosure.sfrac_false_div 60492937 33554432)

noncomputable def hp748769 := nat_lit 432183544669531406554751593814904857717022717423155289370019224653162244970503778518444840756174561

noncomputable def hp748770 := nat_lit 2401353220105943859260249849873689925524135560047667591709540672651683558910247004952104787681

noncomputable def hp748771 := nat_lit 2610979084142906719098537743719449639554430717389033793119560927372150040366944196999410017945771745

noncomputable def hp748772 := BSN.cos_dyadic_bound_t 60492937 33554432 4 3 33554432 10890000 hp748769 hp681868 hp748770 hp748771 hp681871

noncomputable def hp748773 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 60492937) (BSN.cosEvenQ 33554432) 0 3 hp748769 hp681868 hp748770 rfl rfl rfl

noncomputable def hp748774 := hp748772 hp748770 7716083 rfl rfl rfl rfl rfl rfl rfl rfl (hp748773 rfl)

noncomputable def hp748775 := @BSN.binarySplit_of_base3 (BSN.cosOddP 60492937) (BSN.cosOddQ 33554432) 0 3 hp748771 hp681871 hp748770 rfl rfl rfl

noncomputable def hp748776 := hp748768 (hp748774 (hp748775 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp748777 := @hp748760 7716083 33554432 158696179 45675970560000 (@hp748761 7716083 33554432 2539138864 730815528960000 7716083 33554432 158696179 45675970560000 hp748776 rfl)

noncomputable def hp748778 := @hp748759 7716083 33554432 158696179 45675970560000 145913787 145918197 33554432 hp748777 rfl rfl rfl

noncomputable def hp748779 := @Enclosure.Real.IsNear.recentre' hp748757 Bool.false 291831984 67108864 4410 67108864 18239499 4194304 2205 33554432 (hp748778 rfl rfl rfl)

noncomputable def hp748780 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748750 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp748781 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748750 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 56312535)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp748782 := nat_lit 66482107247540547829212812005

noncomputable def hp748783 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748750 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp748782

noncomputable def hp748784 := nat_lit 6413099819361115449749929994359697

noncomputable def hp748785 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp748750 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp748786 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp748787 := @hp748786 (Enclosure.sfrac Bool.false 1 16) 57590028156375 281474976710656 237644775 281474976710656 1 16 0

noncomputable def hp748788 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)) 23173392515625

noncomputable def hp748789 := @hp748788 281474976710656 86649831 281474976710656 4813875 16777216 9 16777216 966200341825585152000 57590028156375 281474976710656 237644775

noncomputable def hp748790 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)) 4813875 16777216 9

noncomputable def hp748791 := @hp748790 16777216 4813875 16777216 9 16777216 23173392515625 281474976710656 86649831 281474976710656 (@hp748766 1 4813875 4813875 16777216 9 16777216 (hp748745 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp748792 := hp748791 (@hp748766 1 4813875 4813875 16777216 9 16777216 (hp748745 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp748793 := @hp748789 281474976710656 (hp748792 rfl) (@hp748766 1 4813875 4813875 16777216 9 16777216 (hp748745 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp748794 := @hp748785 500000000000000 75182214200791 281474976710656 237644775 281474976710656 hp748782 hp631146 hp748784 hp631148 hd4948 (@hp748787 1 1202915427212656 75182214200791 281474976710656 237644775 281474976710656 (hp748793 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp748795 := @hp748781 56312535 33554432 357 67108864 Bool.true 3598424 33554432 1 10890000 (@hp748783 hp631146 hp748784 hp631148 56312535 33554432 357 67108864 (hp748794 rfl) rfl) (Enclosure.sfrac_true_div 56312535 33554432)

noncomputable def hp748796 := nat_lit 324035337652659706844091313070458563552603194781770594739373060749478569556063306799144141474390625

noncomputable def hp748797 := nat_lit 1016859473386862889915909366679917775884981425835019207738296943016127120829094296191650390625

noncomputable def hp748798 := nat_lit 1959650154463471428490746975857991479677635510323992776892538472944264233718972495011716013115990625

noncomputable def hp748799 := BSN.cos_dyadic_bound_t 56312535 33554432 4 3 33554432 10890000 hp748796 hp681868 hp748797 hp748798 hp681871

noncomputable def hp748800 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 56312535) (BSN.cosEvenQ 33554432) 0 3 hp748796 hp681868 hp748797 rfl rfl rfl

noncomputable def hp748801 := hp748799 hp748797 3598424 rfl rfl rfl rfl rfl rfl rfl rfl (hp748800 rfl)

noncomputable def hp748802 := @BSN.binarySplit_of_base3 (BSN.cosOddP 56312535) (BSN.cosOddQ 33554432) 0 3 hp748798 hp681871 hp748797 rfl rfl rfl

noncomputable def hp748803 := hp748795 (BSN.cos_neg_of_bound 56312535 33554432 Bool.true 3598424 33554432 1 10890000 (hp748801 (hp748802 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp748804 := hp748755 (hp748758 (@Enclosure.Real.IsNear.neg hp748757 Bool.false 18239499 4194304 2205 33554432 (hp748779 rfl))) (@hp748780 3598424 33554432 3954838864 730815528960000 449803 4194304 247177429 45675970560000 (hp748803 rfl) rfl)

noncomputable def hp748805 := @hp748730 67108864 8204181368697 17592186044416 5207617425125057 170292360909946880000 163880483639069693583 1180591620717411303424 2602570609267600763717 hp748549 (hp748748 rfl) (@hp748751 Bool.false 8204181368697 17592186044416 5207617425125057 170292360909946880000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748553 (Enclosure.sfrac Bool.false 11 1)) (hp748752 rfl (hp748556 rfl rfl))) (hp748804 rfl))

noncomputable def hp748806 := @hp748550 209342818390221548923717 hp748549 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 800445 1000))) (@hp748555 209342818390221548923717 hp748549 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 800445 1000) 11 (hp748556 rfl rfl)) (@hp748559 209342818390221548923717 hp748549 hp748729 (hp748805 rfl) rfl rfl))

theorem hd5005 : hp748548 hp748549 := hp748806

noncomputable def hp748807 := nat_lit 18825914602359045902687173

noncomputable def hp748808 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 801741 1000)) Bool.true 7484371100719826081219 18889465931478580854784 hp748807

noncomputable def hp748809 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 801741 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 801741 1000)) Bool.true 7484371100719826081219 18889465931478580854784

noncomputable def hp748810 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 801741 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748811 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp748810 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp748812 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 801741 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748813 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp748811 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp748814 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 801741 1000)) hp748813 Bool.true 7484371100719826081219 18889465931478580854784

noncomputable def hp748815 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 801741 1000) 801741 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl

noncomputable def hp748816 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp748811 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp748817 := nat_lit 2009070569294948442352715300864

noncomputable def hp748818 := @hp748816 143020121 268435456 194553 268435456 2579775206187724696125 18889465931478580854784 189789150545542271327173 hp740088 hp748817 7484371100719826081219 18889465931478580854784

noncomputable def hp748819 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) 11)

noncomputable def hp748820 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) 11) hp748819

noncomputable def hp748821 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) 11)

noncomputable def hp748822 := @hp748821 143020121 536870912 194553 536870912 143020121 536870912 194553 536870912 153566685591240704 143020121 268435456

noncomputable def hp748823 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp748824 := hp748823 BSN.quadSignNeg 9 10 11 801741 1000 193 241 536870912 268435456 9007199254740992

noncomputable def hp748825 := hp748824 Bool.false 828134774905 3654 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp748826 := hp748825 Bool.false 81560690 167018 Bool.true 210431038 Bool.true 755814813 28296951008113761 1 Bool.false 205084141

noncomputable def hp748827 := hp748826 Bool.true Bool.false 529756236 Bool.true Bool.true 143020121 194553 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 205084141 536870912) BSN.abs_quadSignNeg

noncomputable def hp748828 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp748829 := hp748828 BSN.quadSignPos 7 8 9 801741 1000 79 139 536870912 268435456 9007199254740992

noncomputable def hp748830 := hp748829 Bool.false 828134774905 3654 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp748831 := hp748830 Bool.true 140247195 136403 Bool.true 300330136 Bool.true 398947212 28296951008113761 1 Bool.false 284909301

noncomputable def hp748832 := hp748831 Bool.false Bool.false 363231707 Bool.false Bool.false 81560690 167018 BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 284909301 536870912) BSN.abs_quadSignPos

noncomputable def hp748833 := hp748828 BSN.quadSignPos 5 6 7 801741 1000 67 11 536870912 268435456 9007199254740992

noncomputable def hp748834 := hp748833 Bool.false 828134774905 3654 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp748835 := hp748834 Bool.true 352832357 101363 Bool.false 403109426 Bool.true 169621597 28296951008113761 1 Bool.false 366285717

noncomputable def hp748836 := hp748835 Bool.false Bool.false 166813677 Bool.false Bool.true 140247195 136403 BSN.abs_quadSignPos (BSN.cos_quad_nat3 67 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 366285717 536870912) BSN.abs_quadSignPos

noncomputable def hp748837 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp748838 := hp748837 BSN.quadSignPos 3 4 5 801741 1000 274 160 536870912 268435456 9007199254740992

noncomputable def hp748839 := hp748838 Bool.false 828134774905 3654 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp748840 := hp748839 Bool.true 303090761 59911 Bool.false 361862432 Bool.false 451761531 28296951008113761 1 Bool.false 419466994

noncomputable def hp748841 := hp748840 Bool.true Bool.false 357752746 Bool.false Bool.true 352832357 101363 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 274 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 419466994 536870912) BSN.abs_quadSignPos

noncomputable def hp748842 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp748843 := hp748842 BSN.quadSignNeg 1 2 3 801741 1000 628 421 536870912 268435456 9007199254740992

noncomputable def hp748844 := hp748843 Bool.false 828134774905 3654 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp748845 := hp748844 Bool.true 536870752 3706 Bool.false 180730525 Bool.false 221975113 28296951008113761 1 Bool.false 506736832

noncomputable def hp748846 := hp748845 Bool.false Bool.false 215704514 Bool.true Bool.true 303090761 59911 BSN.abs_quadSignPos (BSN.cos_quad_nat0 628 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 506736832 536870912) BSN.abs_quadSignNeg

noncomputable def hp748847 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) 1) Bool.true

noncomputable def hp748848 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)))

noncomputable def hp748849 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000))) Bool.true 67108844 67108864

noncomputable def hp748850 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 103516846863) (@Nat.cast Real Real.instNatCast 67108864)) Bool.false 103516846863 67108864

noncomputable def hp748851 := nat_lit 7379993524037833530296054552596992049968520593035209915699

noncomputable def hp748852 := nat_lit 4784370822074702580172790322797916584942812417490944000

noncomputable def hp748853 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) Bool.false hp748851 hp748852 121393121500332939643

noncomputable def hp748854 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 801741 4000) (Real.log (Enclosure.sfrac Bool.false 2571155524324 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1603482))))))

noncomputable def hp748855 := nat_lit 159005494719986843778402731856480000

noncomputable def hp748856 := nat_lit 764887484881745706771651656644572790080

noncomputable def hp748857 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp748854 (Enclosure.sfrac Bool.false 801741 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 801741 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp748855 hp748856)) Bool.false

noncomputable def hp748858 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 801741 1000) 801741 1000 2571155524324 16000000 1603482

noncomputable def hp748859 := hp748858 4000 2000 hp748855 hp748856 (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl rfl rfl rfl

noncomputable def hp748860 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp748854 (Enclosure.sfrac Bool.false 801741 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 801741 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp748855 hp748856) 27787595736258268292539 18014398509481984000

noncomputable def hp748861 := nat_lit 21254381349228960567252637111479337103909339307941404557213120

noncomputable def hp748862 := @hp748860 121393121500332939643 hp738659 hp748855 hp748856 0 1 hp748861 hp748851 hp748852 121393121500332939643 hp738659

noncomputable def hp748863 := @Enclosure.Real.IsNear.subLit_ff_p (hp748854 (Enclosure.sfrac Bool.false 801741 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 801741 2000) (Real.log Real.pi)) 7210838994438636108479 3602879701896396800 10121777343175633 4356000000000000000000

noncomputable def hp748864 := nat_lit 372958796630307199143902393139200

noncomputable def hp748865 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 801741 4000) (Real.log (Enclosure.sfrac Bool.false 2571155524324 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1603482))))))

noncomputable def hp748866 := @hp748865 (Enclosure.sfrac Bool.false 801741 2000) 43275635909888478209467 18014398509481984000 10121777343175633 4356000000000000000000 801741 2000 0

noncomputable def hp748867 := nat_lit 72108389944386361084790000

noncomputable def hp748868 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 801741 4000) (Real.log (Enclosure.sfrac Bool.false 2571155524324 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1603482))))) 43282707339134548249467

noncomputable def hp748869 := nat_lit 97448068878997503038911625345751842816

noncomputable def hp748870 := @hp748868 18014398509481984000 3340592447543711 1452000000000000000000 883928655758755 2251799813685248 200000001089 8712000000000000000 hp748869 43275635909888478209467 18014398509481984000 10121777343175633

noncomputable def hp748871 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 801741 4000) (Real.log (Enclosure.sfrac Bool.false 2571155524324 16000000)) 801741 4000 0 1 53985897364778087 4503599627370496

noncomputable def hp748872 := nat_lit 115933831813467232981221376

noncomputable def hp748873 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2571155524324) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp748872 hp617687

noncomputable def hp748874 := BSN.log_rat_reduce_isNear 2571155524324 16000000 17 5142311048648 4194304000000 54700484 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp748875 := nat_lit 1086791025927462418842814820494079039902020559611960848284691533449803204628480

noncomputable def hp748876 := nat_lit 3758087245535598189116973060838591852632910088885317894940065537211581034496

noncomputable def hp748877 := nat_lit 170129914458366670058609451682775100917919084302510228178554156389232640

noncomputable def hp748878 := BSN.log_dyadic_bound 474003524324 4668307524324 4 3 hp748875 268435456 87120000 hp748876 hp748877 54700484 5142311048648

noncomputable def hp748879 := hp748878 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp748880 := @BSN.binarySplit_of_base3 (BSN.artanhP 474003524324) (BSN.artanhQ 4668307524324) 0 3 hp748876 hp748875 hp748877 rfl rfl rfl

noncomputable def hp748881 := hp748874 rfl rfl rfl rfl (hp748879 (hp748880 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp748882 := @hp748871 12500018513 1089000000000000000 43282707339134548249467 18014398509481984000 3340592447543711 1452000000000000000000 (Enclosure.Real.IsNear.const Bool.false 801741 4000) (BSN.isNear_log_sfrac 2571155524324 16000000 53985897364778087 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp748873 1000001481040000 87120000000000000000000 53985897364778087 4503599627370496 12500018513 1089000000000000000 (hp748881 rfl rfl rfl) rfl)) rfl

noncomputable def hp748883 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1603482)))) 1 4

noncomputable def hp748884 := @hp748883 0 1 883928655758755 562949953421312 200000001089 2178000000000000000 883928655758755 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp748885 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1603482))) 884279719003555 562949953421312 1

noncomputable def hp748886 := @hp748885 2000000000000000 20925 33554432 1 10890000 29659723972508553052160 883928655758755 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp748887 := BSN.arctan_dyadic_bound_f 1000 1603482 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp748888 := hp748887 1 20925 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1603482) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1603482) 0 0 rfl)

noncomputable def hp748889 := hp748884 (hp748886 (hp748888 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp748890 := @hp748863 30795481934901 67108864000 2405223 536870912000 hp748864 27787595736258268292539 18014398509481984000 121393121500332939643 hp738659 (@hp748866 1 hp748867 7210838994438636108479 3602879701896396800 10121777343175633 4356000000000000000000 (@hp748870 4356000000000000000000 hp748882 hp748889 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 801741 2000) rfl rfl)

noncomputable def hp748891 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 801741 2000) (Real.log Real.pi) 801741 2000 0 1 38410761 33554432

noncomputable def hp748892 := hp748890 (@hp748891 3 268435456 30795481934901 67108864000 2405223 536870912000 (Enclosure.Real.IsNear.const Bool.false 801741 2000) hd4909 rfl) rfl

noncomputable def hp748893 := @hp748853 hp738659 103516846863 67108864 457 67108864 (@hp748857 hp748851 hp748852 121393121500332939643 hp738659 (hp748859 rfl rfl rfl rfl rfl) (hp748862 (hp748892 rfl) (Enclosure.Real.IsNear.const Bool.true hp748855 hp748856) rfl rfl)) rfl

noncomputable def hp748894 := nat_lit 15184348131823919422242816

noncomputable def hp748895 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 103516846863) (@Nat.cast Real Real.instNatCast 67108864)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp748894) (@Nat.cast Real Real.instNatCast hp617687)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp748896 := BSN.sin_reduce_arg_pos_rat_q1 103516846863 67108864 226375608064910080 72057594037927936 245 hp748894 hp617687 rfl rfl rfl rfl

noncomputable def hp748897 := nat_lit 14352093450123290837514156376367447970044477980648594411867791132975405480943109062923403760892202973506838798876437975455867761373412322185216

noncomputable def hp748898 := nat_lit 10190517069247406750648604294934045591620501813348718621864423739932280400315346195163365309166245152739653630375602834348422459812745216

noncomputable def hp748899 := nat_lit 71671470807805297737358021133888828995437994506338160287104347368068884316145933949397761745827977364042755781434249436230174122183965388312576

noncomputable def hp748900 := BSN.sin_dyadic_bound_f 215782565246 137438953472 4 3 67108864 21801270 hp748897 hp737934 hp748898 hp748899 hp737937

noncomputable def hp748901 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215782565246) (BSN.sinEvenQ 137438953472) 0 3 hp748897 hp737934 hp748898 rfl rfl rfl

noncomputable def hp748902 := hp748900 hp748898 67108844 rfl rfl rfl rfl rfl rfl rfl rfl (hp748901 rfl)

noncomputable def hp748903 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215782565246) (BSN.sinOddQ 137438953472) 0 3 hp748899 hp737937 hp748898 rfl rfl rfl

noncomputable def hp748904 := @BSN.sin_arg_round Bool.false 67108844 67108864 hp748894 hp617687 215782565246 137438953472 21801270 21780000 (hp748902 (hp748903 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748905 := hp748895 67108844 67108864 245 1000000000000000 21780000 10890000 hp748896 BSN.pi_near_15 hp748904 rfl rfl

noncomputable def hp748906 := @hp748850 457 67108864 Bool.true 67108844 67108864 1 10890000 hp748893 (Enclosure.sfrac_false_div 103516846863 67108864) (hp748905 rfl rfl) rfl

noncomputable def hp748907 := @hp748847 16777211 16777216 315239929 45675970560000 536870752 536870912 3706 536870912 (@hp748848 Bool.true 16777211 16777216 315239929 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000)) (@hp748849 5043838864 730815528960000 16777211 16777216 315239929 45675970560000 (hp748906 rfl) rfl))

noncomputable def hp748908 := @hp748853 hp738659 828134774905 536870912 3654 536870912 (@hp748857 hp748851 hp748852 121393121500332939643 hp738659 (hp748859 rfl rfl rfl rfl rfl) (hp748862 (hp748892 rfl) (Enclosure.Real.IsNear.const Bool.true hp748855 hp748856) rfl rfl)) rfl

noncomputable def hp748909 := hp748846 (BSN.cos_quad_nat1 421 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 215704514 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl rfl (hp748907 rfl) hp748908

noncomputable def hp748910 := nat_lit 148908037259373265170583176667090932208572419776462833713520205275390625

noncomputable def hp748911 := nat_lit 1138287800438365199025931717388983599793334000778191674957275390625

noncomputable def hp748912 := nat_lit 446721835202518918781351478137838018658517672661386944757210701275390625

noncomputable def hp748913 := BSN.cos_dyadic_bound_f 180730525 536870912 3 2 536870912 268435456 hp748910 hp708868 hp748911 hp748912 hp708870

noncomputable def hp748914 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 180730525) (BSN.cosEvenQ 536870912) 0 2 hp748910 hp708868 hp748911 rfl rfl rfl

noncomputable def hp748915 := hp748913 hp748911 506736832 rfl rfl rfl rfl rfl rfl rfl rfl (hp748914 rfl)

noncomputable def hp748916 := @BSN.binarySplit_of_base2 (BSN.cosOddP 180730525) (BSN.cosOddQ 536870912) 0 2 hp748912 hp708870 hp748911 rfl rfl rfl

noncomputable def hp748917 := nat_lit 609933691859422678479666270045511002493702511435119189065765492791548225

noncomputable def hp748918 := nat_lit 5894327819654056825929635032662707236748149012654402238885457664321

noncomputable def hp748919 := nat_lit 1597435840243922813259503011662475933576551842469767864235284761808312641

noncomputable def hp748920 := BSN.sin_dyadic_bound_f 221975113 536870912 3 2 536870912 268435456 hp748917 hp708845 hp748918 hp748919 hp708848

noncomputable def hp748921 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 221975113) (BSN.sinEvenQ 536870912) 0 2 hp748917 hp708845 hp748918 rfl rfl rfl

noncomputable def hp748922 := hp748920 hp748918 215704514 rfl rfl rfl rfl rfl rfl rfl rfl (hp748921 rfl)

noncomputable def hp748923 := @BSN.binarySplit_of_base2 (BSN.sinOddP 221975113) (BSN.sinOddQ 536870912) 0 2 hp748919 hp708848 hp748918 rfl rfl rfl

noncomputable def hp748924 := hp748909 hd4911 hd4913 hd4915 hd4917 hd4918 (hp748915 (hp748916 rfl) rfl rfl rfl rfl) (hp748922 (hp748923 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748925 := hp748841 (BSN.cos_quad_nat0 160 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 357752746 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl rfl (hp748924 rfl rfl rfl rfl rfl) hp748908

noncomputable def hp748926 := nat_lit 2393404594794886521832245558086236586532168387435843987520456888057593856

noncomputable def hp748927 := nat_lit 294000440637389426564187525633031724649178979139470286371164442853376

noncomputable def hp748928 := nat_lit 7179625783503384786643608299207443696147206804349253021988628335287074816

noncomputable def hp748929 := BSN.cos_dyadic_bound_f 361862432 536870912 3 2 536870912 268435456 hp748926 hp708868 hp748927 hp748928 hp708870

noncomputable def hp748930 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 361862432) (BSN.cosEvenQ 536870912) 0 2 hp748926 hp708868 hp748927 rfl rfl rfl

noncomputable def hp748931 := hp748929 hp748927 419466994 rfl rfl rfl rfl rfl rfl rfl rfl (hp748930 rfl)

noncomputable def hp748932 := @BSN.binarySplit_of_base2 (BSN.cosOddP 361862432) (BSN.cosOddQ 536870912) 0 2 hp748928 hp708870 hp748927 rfl rfl rfl

noncomputable def hp748933 := nat_lit 5815075446542445293537864282200898180992557429823383921323581263824599521

noncomputable def hp748934 := nat_lit 1734898103558169395079505062031921637991230996544931916015972286249441

noncomputable def hp748935 := nat_lit 17441756543420219541823433836478630699701689827477061900138711846901299681

noncomputable def hp748936 := BSN.cos_dyadic_bound_f 451761531 536870912 3 2 536870912 268435456 hp748933 hp708868 hp748934 hp748935 hp708870

noncomputable def hp748937 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 451761531) (BSN.cosEvenQ 536870912) 0 2 hp748933 hp708868 hp748934 rfl rfl rfl

noncomputable def hp748938 := hp748936 hp748934 357752746 rfl rfl rfl rfl rfl rfl rfl rfl (hp748937 rfl)

noncomputable def hp748939 := @BSN.binarySplit_of_base2 (BSN.cosOddP 451761531) (BSN.cosOddQ 536870912) 0 2 hp748935 hp708870 hp748934 rfl rfl rfl

noncomputable def hp748940 := hp748925 hd4920 hd4922 hd4924 hd4926 hd4918 (hp748931 (hp748932 rfl) rfl rfl rfl rfl) (hp748938 (hp748939 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748941 := hp748836 (BSN.cos_quad_nat3 11 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 166813677 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl rfl (hp748940 rfl rfl rfl rfl rfl) hp748908

noncomputable def hp748942 := nat_lit 6634355550291287925046732037092162304896747741010538092550259635158237440

noncomputable def hp748943 := nat_lit 697242141062923913138718852294651843856088467657592849046348147179776

noncomputable def hp748944 := nat_lit 17374564239677366498310645028528138505077619940365677949209366861747568896

noncomputable def hp748945 := BSN.sin_dyadic_bound_f 403109426 536870912 3 2 536870912 268435456 hp748942 hp708845 hp748943 hp748944 hp708848

noncomputable def hp748946 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 403109426) (BSN.sinEvenQ 536870912) 0 2 hp748942 hp708845 hp748943 rfl rfl rfl

noncomputable def hp748947 := hp748945 hp748943 366285717 rfl rfl rfl rfl rfl rfl rfl rfl (hp748946 rfl)

noncomputable def hp748948 := @BSN.binarySplit_of_base2 (BSN.sinOddP 403109426) (BSN.sinOddQ 536870912) 0 2 hp748944 hp708848 hp748943 rfl rfl rfl

noncomputable def hp748949 := nat_lit 827798416363199526339255003107281

noncomputable def hp748950 := BSN.sin_dyadic_bound_f 169621597 536870912 2 1 536870912 268435456 hp748949 hp708890 hp748949 hp748949 hp708891

noncomputable def hp748951 := @BSN.binarySplit_of_base (BSN.sinEvenP 169621597) (BSN.sinEvenQ 536870912) 0 1 hp748949 hp708890 hp748949 rfl rfl rfl

noncomputable def hp748952 := hp748950 hp748949 166813677 rfl rfl rfl rfl rfl rfl rfl rfl (hp748951 rfl)

noncomputable def hp748953 := @BSN.binarySplit_of_base (BSN.sinOddP 169621597) (BSN.sinOddQ 536870912) 0 1 hp748949 hp708891 hp748949 rfl rfl rfl

noncomputable def hp748954 := hp748941 hd4928 hd4930 hd4932 hd4934 hd4918 (hp748947 (hp748948 rfl) rfl rfl rfl rfl) (hp748952 (hp748953 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748955 := hp748832 (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 363231707 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl rfl (hp748954 rfl rfl rfl rfl rfl) hp748908

noncomputable def hp748956 := nat_lit 2043953441686235981207676208433799475152909597982794841948808045217710080

noncomputable def hp748957 := nat_lit 66189835548055506514864928690291122828079907614354627788075492704256

noncomputable def hp748958 := nat_lit 5353104230396873575200032669346833392153993960580706107135221329534386176

noncomputable def hp748959 := BSN.sin_dyadic_bound_f 300330136 536870912 3 2 536870912 268435456 hp748956 hp708845 hp748957 hp748958 hp708848

noncomputable def hp748960 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 300330136) (BSN.sinEvenQ 536870912) 0 2 hp748956 hp708845 hp748957 rfl rfl rfl

noncomputable def hp748961 := hp748959 hp748957 284909301 rfl rfl rfl rfl rfl rfl rfl rfl (hp748960 rfl)

noncomputable def hp748962 := @BSN.binarySplit_of_base2 (BSN.sinOddP 300330136) (BSN.sinOddQ 536870912) 0 2 hp748958 hp708848 hp748957 rfl rfl rfl

noncomputable def hp748963 := nat_lit 6364536921528021076530523706140009531508443512526259611510238907113472000

noncomputable def hp748964 := nat_lit 641687346079549597335670146018763543641907897462984136342761593962496

noncomputable def hp748965 := nat_lit 16667986348298783548708066240606470774880027062877644627258451714145058816

noncomputable def hp748966 := BSN.sin_dyadic_bound_f 398947212 536870912 3 2 536870912 268435456 hp748963 hp708845 hp748964 hp748965 hp708848

noncomputable def hp748967 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 398947212) (BSN.sinEvenQ 536870912) 0 2 hp748963 hp708845 hp748964 rfl rfl rfl

noncomputable def hp748968 := hp748966 hp748964 363231707 rfl rfl rfl rfl rfl rfl rfl rfl (hp748967 rfl)

noncomputable def hp748969 := @BSN.binarySplit_of_base2 (BSN.sinOddP 398947212) (BSN.sinOddQ 536870912) 0 2 hp748965 hp708848 hp748964 rfl rfl rfl

noncomputable def hp748970 := hp748955 hd4936 hd4938 hd4940 hd4942 hd4918 (hp748961 (hp748962 rfl) rfl rfl rfl rfl) (hp748968 (hp748969 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748971 := hp748827 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 529756236 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl rfl (hp748970 rfl rfl rfl rfl rfl) hp748908

noncomputable def hp748972 := nat_lit 1960826600005441484468532385413136

noncomputable def hp748973 := BSN.sin_dyadic_bound_f 210431038 536870912 2 1 536870912 268435456 hp748972 hp708890 hp748972 hp748972 hp708891

noncomputable def hp748974 := @BSN.binarySplit_of_base (BSN.sinEvenP 210431038) (BSN.sinEvenQ 536870912) 0 1 hp748972 hp708890 hp748972 rfl rfl rfl

noncomputable def hp748975 := hp748973 hp748972 205084141 rfl rfl rfl rfl rfl rfl rfl rfl (hp748974 rfl)

noncomputable def hp748976 := @BSN.binarySplit_of_base (BSN.sinOddP 210431038) (BSN.sinOddQ 536870912) 0 1 hp748972 hp708891 hp748972 rfl rfl rfl

noncomputable def hp748977 := nat_lit 117026323497852440456760508048225705890638208954661793833364482657662993048281561470389570419911166237595187725681

noncomputable def hp748978 := nat_lit 34752399120965423657777332653581768632617016375502144488122879982038957943319038825823444430475826608653681

noncomputable def hp748979 := nat_lit 584662226399338367145004669261689704969945987393369923551234826403095459926679587980577561004388807937713824515441

noncomputable def hp748980 := BSN.sin_dyadic_bound_f 755814813 536870912 4 3 536870912 268435456 hp748977 hp642702 hp748978 hp748979 hp642705

noncomputable def hp748981 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 755814813) (BSN.sinEvenQ 536870912) 0 3 hp748977 hp642702 hp748978 rfl rfl rfl

noncomputable def hp748982 := hp748980 hp748978 529756236 rfl rfl rfl rfl rfl rfl rfl rfl (hp748981 rfl)

noncomputable def hp748983 := @BSN.binarySplit_of_base3 (BSN.sinOddP 755814813) (BSN.sinOddQ 536870912) 0 3 hp748979 hp642705 hp748978 rfl rfl rfl

noncomputable def hp748984 := hp748971 hd4944 hd4946 hd4961 hd4963 hd4918 (hp748975 (hp748976 rfl) rfl rfl rfl rfl) (hp748982 (hp748983 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp748985 := @hp748822 194553 268435456 (hp748984 rfl rfl rfl rfl rfl) (hp748984 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp748986 := @hp748820 Bool.true 143020121 268435456 194553 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 801741 1000)) (Enclosure.sfrac Bool.false 801741 1000) 11) hp748985

noncomputable def hp748987 := @Enclosure.Real.IsNear.mulLit_tf hp748811 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1))) 9983581 33554432 1

noncomputable def hp748988 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp748810 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp748989 := @hp748988 1 1 0 1 9983581 33554432 1 33554432 9983581 33554432 1

noncomputable def hp748990 := @Enclosure.Real.IsNear.of_eq (hp748810 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp748991 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 801741 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748992 := @hp748990 (@Inv.inv Real Real.instInv (Real.sqrt hp748812)) Bool.false 9983581 33554432 1 33554432 (hp748991 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 801741 1000) 801741 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000))))

noncomputable def hp748993 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp748812)) Bool.false 19967162 67108864 2 67108864 9983581 33554432

noncomputable def hp748994 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp748812) Bool.false 225550316 67108864 6 67108864 56387579 16777216 3 33554432

noncomputable def hp748995 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 801741 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748996 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 801741 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp748997 := @hp748996 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 801741 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8563160710887

noncomputable def hp748998 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 801741 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 801741 1000 0

noncomputable def hp748999 := @hp748998 1 10680707 67108864 1 67108864 8563160710887 67108864000 801741 67108864000 (Enclosure.Real.IsNear.const Bool.false 801741 1000) hd4949

noncomputable def hp749000 := @hp748997 67108864000 801741 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 801741 1000) 801741 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000))) (hp748999 rfl)

noncomputable def hp749001 := @hp748995 8563160710887 67108864000 801741 67108864000 379032958 379032994 33554432 hp749000 rfl rfl rfl

noncomputable def hp749002 := @Enclosure.Real.IsNear.recentre' hp748812 Bool.false 758065952 67108864 36 67108864 23689561 2097152 9 16777216 (hp749001 rfl rfl rfl)

noncomputable def hp749003 := @Enclosure.Real.IsNear.sqrt_image hp748812 23689561 2097152 9 16777216 112775155 112775161 33554432 (hp749002 rfl) rfl rfl

noncomputable def hp749004 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp748812) 56387579 16777216 3 33554432 9983580 9983582 33554432 (hp748994 (hp749003 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp749005 := @hp748989 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp748992 (@hp748993 1 33554432 (hp749004 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp749006 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749007 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp749008 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1))) (hp749006 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749007 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp749009 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 801741 1000) 801741 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl

noncomputable def hp749010 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749011 := @hp749010 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749007 (Enclosure.sfrac Bool.false 1 16)))) 117570525

noncomputable def hp749012 := @hp749011 33554432 179 4194304 2197845 16777216 249899929 45675970560000 258401790518625 562949953421312 37949786180591053 1532631248189521920000

noncomputable def hp749013 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749014 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749015 := @hp749013 (@Neg.neg Real Real.instNeg hp749014) Bool.true 117570525 33554432 179 4194304 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749016 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749017 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp749018 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp749019 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 31209285) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false

noncomputable def hp749020 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1))) Bool.false 549039550452398260395

noncomputable def hp749021 := nat_lit 242874678724063576287659007

noncomputable def hp749022 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp749023 := @Enclosure.Real.IsNear.subLit_ff_p hp748812 (Enclosure.sfrac Bool.false 11 1) 23689561 2097152 9 16777216 11 1 0

noncomputable def hp749024 := @hp749022 500000000000000 620889 2097152 9 16777216 549039550452398260395 295147905179352825856 hp749021 hp631123 hd4948 (@hp749023 1 620889 620889 2097152 9 16777216 (hp749002 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749025 := @hp749019 31209285 16777216 227 67108864 Bool.true 9576379 33554432 1 10890000 (@hp749020 295147905179352825856 hp749021 hp631123 31209285 16777216 227 67108864 (hp749024 rfl) rfl) (Enclosure.sfrac_false_div 31209285 16777216)

noncomputable def hp749026 := nat_lit 119703757802269603790378313512887077574876229272604984725295486701090098957019304130142848140625

noncomputable def hp749027 := nat_lit 853897672725811046587507978156235920578133755148445009810588399761502070073104687744140625

noncomputable def hp749028 := nat_lit 722772170401269180231370690169740359274007183457734443041984996923893032903978774681353241740625

noncomputable def hp749029 := BSN.cos_dyadic_bound_t 31209285 16777216 4 3 33554432 10890000 hp749026 hp633087 hp749027 hp749028 hp633090

noncomputable def hp749030 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 31209285) (BSN.cosEvenQ 16777216) 0 3 hp749026 hp633087 hp749027 rfl rfl rfl

noncomputable def hp749031 := hp749029 hp749027 9576379 rfl rfl rfl rfl rfl rfl rfl rfl (hp749030 rfl)

noncomputable def hp749032 := @BSN.binarySplit_of_base3 (BSN.cosOddP 31209285) (BSN.cosOddQ 16777216) 0 3 hp749028 hp633090 hp749027 rfl rfl rfl

noncomputable def hp749033 := hp749025 (hp749031 (hp749032 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp749034 := @hp749017 9576379 33554432 158696179 45675970560000 (@hp749018 9576379 33554432 2539138864 730815528960000 9576379 33554432 158696179 45675970560000 hp749033 rfl)

noncomputable def hp749035 := @hp749016 9576379 33554432 158696179 45675970560000 117569093 117571957 33554432 hp749034 rfl rfl rfl

noncomputable def hp749036 := @Enclosure.Real.IsNear.recentre' hp749014 Bool.false 235141050 67108864 2864 67108864 117570525 33554432 179 4194304 (hp749035 rfl rfl rfl)

noncomputable def hp749037 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749007 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp749038 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749007 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 57115539)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp749039 := nat_lit 1053595732182234472780689805

noncomputable def hp749040 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749007 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp749039

noncomputable def hp749041 := nat_lit 1297506918728905367945881746218107

noncomputable def hp749042 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749007 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp749043 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp749044 := @hp749043 (Enclosure.sfrac Bool.false 1 16) 916595457807 4398046511104 240403041 281474976710656 1 16 0

noncomputable def hp749045 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)) 385503150321

noncomputable def hp749046 := @hp749045 4398046511104 89408097 281474976710656 620889 2097152 9 16777216 1922239997530865664 916595457807 4398046511104 240403041

noncomputable def hp749047 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)) 620889 2097152 9

noncomputable def hp749048 := @hp749047 16777216 620889 2097152 9 16777216 385503150321 4398046511104 89408097 281474976710656 (@hp749023 1 620889 620889 2097152 9 16777216 (hp749002 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749049 := hp749048 (@hp749023 1 620889 620889 2097152 9 16777216 (hp749002 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749050 := @hp749046 281474976710656 (hp749049 rfl) (@hp749023 1 620889 620889 2097152 9 16777216 (hp749002 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749051 := @hp749042 500000000000000 1191473364751 4398046511104 240403041 281474976710656 hp749039 hp634261 hp749041 hp636853 hd4948 (@hp749044 1 19063573836016 1191473364751 4398046511104 240403041 281474976710656 (hp749050 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp749052 := @hp749038 57115539 33554432 361 67108864 Bool.true 4395690 33554432 1 10890000 (@hp749040 hp634261 hp749041 hp636853 57115539 33554432 361 67108864 (hp749051 rfl) rfl) (Enclosure.sfrac_true_div 57115539 33554432)

noncomputable def hp749053 := nat_lit 343011167281367477597048697163937288106175251713427492609945406256407832726200563801297964129482801

noncomputable def hp749054 := nat_lit 1205178443689879565632869101375755908336519540454903840264856978221245875631515591903509379121

noncomputable def hp749055 := nat_lit 2074030532108743458509702700281001463042938437847545284168168456142062714142103049120039863395711025

noncomputable def hp749056 := BSN.cos_dyadic_bound_t 57115539 33554432 4 3 33554432 10890000 hp749053 hp681868 hp749054 hp749055 hp681871

noncomputable def hp749057 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 57115539) (BSN.cosEvenQ 33554432) 0 3 hp749053 hp681868 hp749054 rfl rfl rfl

noncomputable def hp749058 := hp749056 hp749054 4395690 rfl rfl rfl rfl rfl rfl rfl rfl (hp749057 rfl)

noncomputable def hp749059 := @BSN.binarySplit_of_base3 (BSN.cosOddP 57115539) (BSN.cosOddQ 33554432) 0 3 hp749055 hp681871 hp749054 rfl rfl rfl

noncomputable def hp749060 := hp749052 (BSN.cos_neg_of_bound 57115539 33554432 Bool.true 4395690 33554432 1 10890000 (hp749058 (hp749059 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp749061 := hp749012 (hp749015 (@Enclosure.Real.IsNear.neg hp749014 Bool.false 117570525 33554432 179 4194304 (hp749036 rfl))) (@hp749037 4395690 33554432 3998398864 730815528960000 2197845 16777216 249899929 45675970560000 (hp749060 rfl) rfl)

noncomputable def hp749062 := @hp748987 33554432 258401790518625 562949953421312 37949786180591053 1532631248189521920000 2579775206187724696125 18889465931478580854784 189789150545542271327173 hp740088 (hp749005 rfl) (@hp749008 Bool.false 258401790518625 562949953421312 37949786180591053 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp748812 (Enclosure.sfrac Bool.false 11 1)) (hp749009 rfl (hp748815 rfl rfl))) (hp749061 rfl))

noncomputable def hp749063 := @hp748809 hp748807 hp740088 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 801741 1000))) (@hp748814 hp748807 hp740088 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 801741 1000) 11 (hp748815 rfl rfl)) (@hp748818 hp748807 hp740088 hp748986 (hp749062 rfl) rfl rfl))

theorem hd5006 : hp748808 hp740088 := hp749063

noncomputable def hp749064 := nat_lit 8369447526345163838428631

noncomputable def hp749065 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 803037 1000)) Bool.false 49210302343757826609345 151115727451828646838272 hp749064

noncomputable def hp749066 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 803037 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 803037 1000)) Bool.false 49210302343757826609345 151115727451828646838272

noncomputable def hp749067 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 803037 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749068 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp749067 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749069 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 803037 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749070 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp749068 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp749071 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 803037 1000)) hp749070 Bool.false 49210302343757826609345 151115727451828646838272

noncomputable def hp749072 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 803037 1000) 803037 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl

noncomputable def hp749073 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp749068 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp749074 := nat_lit 3302447487386125234862114734080

noncomputable def hp749075 := @hp749073 12831165 67108864 24359 33554432 20317087387393151455425 151115727451828646838272 73144287534371738588631 hp742600 hp749074 49210302343757826609345 151115727451828646838272

noncomputable def hp749076 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) 11)

noncomputable def hp749077 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) 11) hp749076

noncomputable def hp749078 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) 11)

noncomputable def hp749079 := @hp749078 51324660 536870912 194872 536870912 51324660 536870912 194872 536870912 55109434044579840 12831165 67108864

noncomputable def hp749080 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp749081 := hp749080 BSN.quadSignNeg 9 10 11 803037 1000 193 241 536870912 268435456 9007199254740992

noncomputable def hp749082 := hp749081 Bool.false 829821954018 3660 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp749083 := hp749082 Bool.false 249318674 167292 Bool.true 125355404 Bool.true 737054545 28296951008113761 1 Bool.false 124219466

noncomputable def hp749084 := hp749083 Bool.true Bool.false 526389396 Bool.true Bool.false 51324660 194872 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 124219466 536870912) BSN.abs_quadSignNeg

noncomputable def hp749085 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp749086 := hp749085 BSN.quadSignPos 7 8 9 803037 1000 79 139 536870912 268435456 9007199254740992

noncomputable def hp749087 := hp749086 Bool.false 829821954018 3660 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp749088 := hp749087 Bool.false 150620245 136627 Bool.true 59994635 Bool.true 240563328 28296951008113761 1 Bool.false 59869846

noncomputable def hp749089 := hp749088 Bool.false Bool.false 232593730 Bool.false Bool.false 249318674 167292 BSN.abs_quadSignPos (BSN.cos_quad_nat3 79 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 59869846 536870912) BSN.abs_quadSignPos

noncomputable def hp749090 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp749091 := hp749090 BSN.quadSignNeg 5 6 7 803037 1000 68 10 536870912 268435456 9007199254740992

noncomputable def hp749092 := hp749091 Bool.false 829821954018 3660 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp749093 := hp749092 Bool.true 7665625 101530 Bool.false 294864 Bool.true 679691833 28296951008113761 1 Bool.false 536870831

noncomputable def hp749094 := hp749093 Bool.false Bool.false 161101720 Bool.true Bool.false 150620245 136627 BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 536870831 536870912) BSN.abs_quadSignNeg

noncomputable def hp749095 := hp749085 BSN.quadSignNeg 3 4 5 803037 1000 275 161 536870912 268435456 9007199254740992

noncomputable def hp749096 := hp749095 Bool.false 829821954018 3660 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp749097 := hp749096 Bool.true 47009088 60010 Bool.false 241164298 Bool.false 175803530 28296951008113761 1 Bool.false 233135226

noncomputable def hp749098 := hp749097 Bool.false Bool.false 172678436 Bool.true Bool.true 7665625 101530 BSN.abs_quadSignPos (BSN.cos_quad_nat3 275 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 233135226 536870912) BSN.abs_quadSignNeg

noncomputable def hp749099 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp749100 := hp749099 BSN.quadSignNeg 1 2 3 803037 1000 629 422 536870912 268435456 9007199254740992

noncomputable def hp749101 := hp749100 Bool.false 829821954018 3660 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp749102 := hp749101 Bool.false 536870888 3714 Bool.false 542313596 Bool.false 301441753 28296951008113761 1 Bool.false 454678724

noncomputable def hp749103 := hp749102 Bool.true Bool.false 454444342 Bool.true Bool.true 47009088 60010 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 629 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 454678724 536870912) BSN.abs_quadSignNeg

noncomputable def hp749104 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) 1) Bool.false

noncomputable def hp749105 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)))

noncomputable def hp749106 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000))) Bool.false 67108861 67108864

noncomputable def hp749107 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 25931936063) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false 25931936063 16777216

noncomputable def hp749108 := nat_lit 1493408600899021701851020167125543834868450407718991227431

noncomputable def hp749109 := nat_lit 966192366531494002828729038009661297013883248259891200

noncomputable def hp749110 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) Bool.false hp749108 hp749109 121588689200951395051

noncomputable def hp749111 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 803037 4000) (Real.log (Enclosure.sfrac Bool.false 2579474693476 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1606074))))))

noncomputable def hp749112 := nat_lit 160294803473407149817028476299360000

noncomputable def hp749113 := nat_lit 772336088309039861018106995346150937920

noncomputable def hp749114 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp749111 (Enclosure.sfrac Bool.false 803037 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 803037 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp749112 hp749113)) Bool.false

noncomputable def hp749115 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 803037 1000) 803037 1000 2579474693476 16000000 1606074

noncomputable def hp749116 := hp749115 4000 2000 hp749112 hp749113 (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl rfl rfl rfl

noncomputable def hp749117 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp749111 (Enclosure.sfrac Bool.false 803037 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 803037 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp749112 hp749113) 5568841613407921211759 3602879701896396800

noncomputable def hp749118 := nat_lit 4301016770589182501330938081321566244421137174230694735001280

noncomputable def hp749119 := @hp749117 121588689200951395051 hp738659 hp749112 hp749113 0 1 hp749118 hp749108 hp749109 121588689200951395051 hp738659

noncomputable def hp749120 := @Enclosure.Real.IsNear.subLit_ff_p (hp749111 (Enclosure.sfrac Bool.false 803037 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 803037 2000) (Real.log Real.pi)) 36124170112921585561387 18014398509481984000 10137977367168481 4356000000000000000000

noncomputable def hp749121 := nat_lit 1868593172358663805613249658880000

noncomputable def hp749122 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 803037 4000) (Real.log (Enclosure.sfrac Bool.false 2579474693476 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1606074))))))

noncomputable def hp749123 := @hp749122 (Enclosure.sfrac Bool.false 803037 2000) 43357284380851027554091 18014398509481984000 10137977367168481 4356000000000000000000 803037 2000 0

noncomputable def hp749124 := nat_lit 72248340225843171122774000

noncomputable def hp749125 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 803037 4000) (Real.log (Enclosure.sfrac Bool.false 2579474693476 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1606074))))) 43364355814526282618091

noncomputable def hp749126 := nat_lit 97631924890698657034569366114368749568

noncomputable def hp749127 := @hp749125 18014398509481984000 3345992455541327 1452000000000000000000 883929209406883 2251799813685248 200000001089 8712000000000000000 hp749126 43357284380851027554091 18014398509481984000 10137977367168481

noncomputable def hp749128 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 803037 4000) (Real.log (Enclosure.sfrac Bool.false 2579474693476 16000000)) 803037 4000 0 1 54000445576637543 4503599627370496

noncomputable def hp749129 := nat_lit 115965073860543054415396864

noncomputable def hp749130 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2579474693476) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp749129 hp617687

noncomputable def hp749131 := BSN.log_rat_reduce_isNear 2579474693476 16000000 17 5158949386952 4194304000000 55567625 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp749132 := nat_lit 1098463231185678196938857556252194381250303724020764006431423862883435907092480

noncomputable def hp749133 := nat_lit 3919747271759067806883229575132951852100513307470622110022045772019437367296

noncomputable def hp749134 := nat_lit 188850194237671299566308123216544010417756630903197224079897837769584640

noncomputable def hp749135 := BSN.log_dyadic_bound 482322693476 4676626693476 4 3 hp749132 268435456 87120000 hp749133 hp749134 55567625 5158949386952

noncomputable def hp749136 := hp749135 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp749137 := @BSN.binarySplit_of_base3 (BSN.artanhP 482322693476) (BSN.artanhQ 4676626693476) 0 3 hp749133 hp749132 hp749134 rfl rfl rfl

noncomputable def hp749138 := hp749131 rfl rfl rfl rfl (hp749136 (hp749137 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp749139 := @hp749128 12500018513 1089000000000000000 43364355814526282618091 18014398509481984000 3345992455541327 1452000000000000000000 (Enclosure.Real.IsNear.const Bool.false 803037 4000) (BSN.isNear_log_sfrac 2579474693476 16000000 54000445576637543 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp749130 1000001481040000 87120000000000000000000 54000445576637543 4503599627370496 12500018513 1089000000000000000 (hp749138 rfl rfl rfl) rfl)) rfl

noncomputable def hp749140 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1606074)))) 1 4

noncomputable def hp749141 := @hp749140 0 1 883929209406883 562949953421312 200000001089 2178000000000000000 883929209406883 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp749142 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1606074))) 884279719003555 562949953421312 1

noncomputable def hp749143 := @hp749142 2000000000000000 20892 33554432 1 10890000 29659742549857015955456 883929209406883 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp749144 := BSN.arctan_dyadic_bound_f 1000 1606074 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp749145 := hp749144 1 20892 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1606074) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1606074) 0 0 rfl)

noncomputable def hp749146 := hp749141 (hp749143 (hp749145 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp749147 := @hp749120 30845262281157 67108864000 2409111 536870912000 hp749121 5568841613407921211759 3602879701896396800 121588689200951395051 hp738659 (@hp749123 1 hp749124 36124170112921585561387 18014398509481984000 10137977367168481 4356000000000000000000 (@hp749127 4356000000000000000000 hp749139 hp749146 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 803037 2000) rfl rfl)

noncomputable def hp749148 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 803037 2000) (Real.log Real.pi) 803037 2000 0 1 38410761 33554432

noncomputable def hp749149 := hp749147 (@hp749148 3 268435456 30845262281157 67108864000 2409111 536870912000 (Enclosure.Real.IsNear.const Bool.false 803037 2000) hd4909 rfl) rfl

noncomputable def hp749150 := @hp749110 hp738659 25931936063 16777216 229 33554432 (@hp749114 hp749108 hp749109 121588689200951395051 hp738659 (hp749116 rfl rfl rfl rfl rfl) (hp749119 (hp749149 rfl) (Enclosure.Real.IsNear.const Bool.true hp749112 hp749113) rfl rfl)) rfl

noncomputable def hp749151 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 25931936063) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 608832157448893628416) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp749152 := BSN.sin_reduce_arg_pos_rat_q0 25931936063 16777216 226375608064910080 72057594037927936 246 608832157448893628416 hp619230 rfl rfl rfl rfl

noncomputable def hp749153 := BSN.cos_dyadic_bound_f 34608101 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp749154 := hp749153 1 67108861 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 34608101) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp749155 := hp749154 (@BSN.binarySplit_of_le (BSN.cosOddP 34608101) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp749156 := @BSN.cos_arg_round Bool.false 67108861 67108864 608832157448893628416 hp619230 34608101 137438953472 21801270 21780000 hp749155 rfl

noncomputable def hp749157 := hp749151 67108861 67108864 246 1000000000000000 21780000 10890000 hp749152 BSN.pi_near_15 hp749156 rfl rfl

noncomputable def hp749158 := @hp749107 229 33554432 Bool.false 67108861 67108864 1 10890000 hp749150 (Enclosure.sfrac_false_div 25931936063 16777216) (hp749157 rfl rfl) rfl

noncomputable def hp749159 := @hp749104 67108861 67108864 157960277 22837985280000 536870888 536870912 3714 536870912 (@hp749105 Bool.false 67108861 67108864 157960277 22837985280000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000)) (@hp749106 2527364432 365407764480000 67108861 67108864 157960277 22837985280000 (hp749158 rfl) rfl))

noncomputable def hp749160 := @hp749110 hp738659 829821954018 536870912 3660 536870912 (@hp749114 hp749108 hp749109 121588689200951395051 hp738659 (hp749116 rfl rfl rfl rfl rfl) (hp749119 (hp749149 rfl) (Enclosure.Real.IsNear.const Bool.true hp749112 hp749113) rfl rfl)) rfl

noncomputable def hp749161 := hp749103 (BSN.cos_quad_nat2 422 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 454444342 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl rfl (hp749159 rfl) hp749160

noncomputable def hp749162 := nat_lit 21737658262852716029414886676396776408543192605068376040333862209620869120

noncomputable def hp749163 := nat_lit 7481762879816680035067503524956836373444796777457868032258542980366336

noncomputable def hp749164 := nat_lit 56919848786618362595077451051522579525389450961348910224060268146086445056

noncomputable def hp749165 := BSN.sin_dyadic_bound_f 542313596 536870912 3 2 536870912 268435456 hp749162 hp708845 hp749163 hp749164 hp708848

noncomputable def hp749166 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 542313596) (BSN.sinEvenQ 536870912) 0 2 hp749162 hp708845 hp749163 rfl rfl rfl

noncomputable def hp749167 := hp749165 hp749163 454678724 rfl rfl rfl rfl rfl rfl rfl rfl (hp749166 rfl)

noncomputable def hp749168 := @BSN.binarySplit_of_base2 (BSN.sinOddP 542313596) (BSN.sinOddQ 536870912) 0 2 hp749164 hp708848 hp749163 rfl rfl rfl

noncomputable def hp749169 := nat_lit 1152465935724404023694884886694488313764390932926078030480196070900053441

noncomputable def hp749170 := nat_lit 68175330765368092447999866010734238438032875447130879153192529114561

noncomputable def hp749171 := nat_lit 3457261456511681334899758660351443472816296733027339829682281827641931201

noncomputable def hp749172 := BSN.cos_dyadic_bound_f 301441753 536870912 3 2 536870912 268435456 hp749169 hp708868 hp749170 hp749171 hp708870

noncomputable def hp749173 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 301441753) (BSN.cosEvenQ 536870912) 0 2 hp749169 hp708868 hp749170 rfl rfl rfl

noncomputable def hp749174 := hp749172 hp749170 454444342 rfl rfl rfl rfl rfl rfl rfl rfl (hp749173 rfl)

noncomputable def hp749175 := @BSN.binarySplit_of_base2 (BSN.cosOddP 301441753) (BSN.cosOddQ 536870912) 0 2 hp749171 hp708870 hp749170 rfl rfl rfl

noncomputable def hp749176 := hp749161 hd4911 hd4913 hd4915 hd4917 hd4918 (hp749167 (hp749168 rfl) rfl rfl rfl rfl) (hp749174 (hp749175 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749177 := hp749098 (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 172678436 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl rfl (hp749176 rfl rfl rfl rfl rfl) hp749160

noncomputable def hp749178 := nat_lit 849804824232359563231865253522221265309795407556341636069496368739508480

noncomputable def hp749179 := nat_lit 11442057387516115420123123794709878279252491915330872475183429837056

noncomputable def hp749180 := nat_lit 2225660776325171449039443083691102355056059658613031844483721144955166976

noncomputable def hp749181 := BSN.sin_dyadic_bound_f 241164298 536870912 3 2 536870912 268435456 hp749178 hp708845 hp749179 hp749180 hp708848

noncomputable def hp749182 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 241164298) (BSN.sinEvenQ 536870912) 0 2 hp749178 hp708845 hp749179 rfl rfl rfl

noncomputable def hp749183 := hp749181 hp749179 233135226 rfl rfl rfl rfl rfl rfl rfl rfl (hp749182 rfl)

noncomputable def hp749184 := @BSN.binarySplit_of_base2 (BSN.sinOddP 241164298) (BSN.sinOddQ 536870912) 0 2 hp749180 hp708848 hp749179 rfl rfl rfl

noncomputable def hp749185 := nat_lit 955235303066852908653500428810000

noncomputable def hp749186 := BSN.sin_dyadic_bound_f 175803530 536870912 2 1 536870912 268435456 hp749185 hp708890 hp749185 hp749185 hp708891

noncomputable def hp749187 := @BSN.binarySplit_of_base (BSN.sinEvenP 175803530) (BSN.sinEvenQ 536870912) 0 1 hp749185 hp708890 hp749185 rfl rfl rfl

noncomputable def hp749188 := hp749186 hp749185 172678436 rfl rfl rfl rfl rfl rfl rfl rfl (hp749187 rfl)

noncomputable def hp749189 := @BSN.binarySplit_of_base (BSN.sinOddP 175803530) (BSN.sinOddQ 536870912) 0 1 hp749185 hp708891 hp749185 rfl rfl rfl

noncomputable def hp749190 := hp749177 hd4920 hd4922 hd4924 hd4926 hd4918 (hp749183 (hp749184 rfl) rfl rfl rfl rfl) (hp749188 (hp749189 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749191 := hp749094 (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 161101720 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl rfl (hp749190 rfl rfl rfl rfl rfl) hp749160

noncomputable def hp749192 := BSN.cos_dyadic_bound_f 294864 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp749193 := hp749192 1 536870831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 294864) (BSN.cosEvenQ 536870912) 0 0 rfl)

noncomputable def hp749194 := hp749193 (@BSN.binarySplit_of_le (BSN.cosOddP 294864) (BSN.cosOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp749195 := nat_lit 29443990882184619338343365973712042360447407774303070775130667356419266195660460967453727729882904392883660401441

noncomputable def hp749196 := nat_lit 9721753810934669354384531957091682953745903431382980597999364982694088750825224856849774366041905163152161

noncomputable def hp749197 := nat_lit 178445004754648740872567092799960076878235304320406009394295898104518995390664249809073479479537421988779108870945

noncomputable def hp749198 := BSN.cos_dyadic_bound_f 679691833 536870912 4 3 536870912 268435456 hp749195 hp716712 hp749196 hp749197 hp716714

noncomputable def hp749199 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 679691833) (BSN.cosEvenQ 536870912) 0 3 hp749195 hp716712 hp749196 rfl rfl rfl

noncomputable def hp749200 := hp749198 hp749196 161101720 rfl rfl rfl rfl rfl rfl rfl rfl (hp749199 rfl)

noncomputable def hp749201 := @BSN.binarySplit_of_base3 (BSN.cosOddP 679691833) (BSN.cosOddQ 536870912) 0 3 hp749197 hp716714 hp749196 rfl rfl rfl

noncomputable def hp749202 := hp749191 hd4928 hd4930 hd4932 hd4934 hd4918 hp749194 (hp749200 (hp749201 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp749203 := hp749089 (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 232593730 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl rfl (hp749202 rfl rfl rfl rfl) hp749160

noncomputable def hp749204 := nat_lit 12955365261680599547964041400625

noncomputable def hp749205 := BSN.sin_dyadic_bound_f 59994635 536870912 2 1 536870912 268435456 hp749204 hp708890 hp749204 hp749204 hp708891

noncomputable def hp749206 := @BSN.binarySplit_of_base (BSN.sinEvenP 59994635) (BSN.sinEvenQ 536870912) 0 1 hp749204 hp708890 hp749204 rfl rfl rfl

noncomputable def hp749207 := hp749205 hp749204 59869846 rfl rfl rfl rfl rfl rfl rfl rfl (hp749206 rfl)

noncomputable def hp749208 := @BSN.binarySplit_of_base (BSN.sinOddP 59994635) (BSN.sinOddQ 536870912) 0 1 hp749204 hp708891 hp749204 rfl rfl rfl

noncomputable def hp749209 := nat_lit 841365628641897906214953774470827445794874380445637719014917650534891520

noncomputable def hp749210 := nat_lit 11215932475206548379465893260768858498803769208550830779100232155136

noncomputable def hp749211 := nat_lit 2203558487314296562817978845501173494168053885540808753217808636739321856

noncomputable def hp749212 := BSN.sin_dyadic_bound_f 240563328 536870912 3 2 536870912 268435456 hp749209 hp708845 hp749210 hp749211 hp708848

noncomputable def hp749213 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 240563328) (BSN.sinEvenQ 536870912) 0 2 hp749209 hp708845 hp749210 rfl rfl rfl

noncomputable def hp749214 := hp749212 hp749210 232593730 rfl rfl rfl rfl rfl rfl rfl rfl (hp749213 rfl)

noncomputable def hp749215 := @BSN.binarySplit_of_base2 (BSN.sinOddP 240563328) (BSN.sinOddQ 536870912) 0 2 hp749211 hp708848 hp749210 rfl rfl rfl

noncomputable def hp749216 := hp749203 hd4936 hd4938 hd4940 hd4942 hd4918 (hp749207 (hp749208 rfl) rfl rfl rfl rfl) (hp749214 (hp749215 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749217 := hp749084 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 526389396 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl rfl (hp749216 rfl rfl rfl rfl rfl) hp749160

noncomputable def hp749218 := nat_lit 246929082962151817646070794342656

noncomputable def hp749219 := BSN.sin_dyadic_bound_f 125355404 536870912 2 1 536870912 268435456 hp749218 hp708890 hp749218 hp749218 hp708891

noncomputable def hp749220 := @BSN.binarySplit_of_base (BSN.sinEvenP 125355404) (BSN.sinEvenQ 536870912) 0 1 hp749218 hp708890 hp749218 rfl rfl rfl

noncomputable def hp749221 := hp749219 hp749218 124219466 rfl rfl rfl rfl rfl rfl rfl rfl (hp749220 rfl)

noncomputable def hp749222 := @BSN.binarySplit_of_base (BSN.sinOddP 125355404) (BSN.sinOddQ 536870912) 0 1 hp749218 hp708891 hp749218 rfl rfl rfl

noncomputable def hp749223 := nat_lit 105819708920323179557349976888635258050468990280294136423436292309897627987465843973139886819292465727207962290625

noncomputable def hp749224 := nat_lit 25703694041138883014626958511925211965925063098531318143763991642012818219608733802841661848401777587890625

noncomputable def hp749225 := nat_lit 528714663817023298038799807862405744069261510760219060808871658319385065117586270321478877312734066066625459890625

noncomputable def hp749226 := BSN.sin_dyadic_bound_f 737054545 536870912 4 3 536870912 268435456 hp749223 hp642702 hp749224 hp749225 hp642705

noncomputable def hp749227 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 737054545) (BSN.sinEvenQ 536870912) 0 3 hp749223 hp642702 hp749224 rfl rfl rfl

noncomputable def hp749228 := hp749226 hp749224 526389396 rfl rfl rfl rfl rfl rfl rfl rfl (hp749227 rfl)

noncomputable def hp749229 := @BSN.binarySplit_of_base3 (BSN.sinOddP 737054545) (BSN.sinOddQ 536870912) 0 3 hp749225 hp642705 hp749224 rfl rfl rfl

noncomputable def hp749230 := hp749217 hd4944 hd4946 hd4961 hd4963 hd4918 (hp749221 (hp749222 rfl) rfl rfl rfl rfl) (hp749228 (hp749229 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749231 := @hp749079 24359 33554432 (hp749230 rfl rfl rfl rfl rfl) (hp749230 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp749232 := @hp749077 Bool.false 12831165 67108864 24359 33554432 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 803037 1000)) (Enclosure.sfrac Bool.false 803037 1000) 11) hp749231

noncomputable def hp749233 := @Enclosure.Real.IsNear.mulLit_tf hp749068 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1))) 19959101 67108864 1

noncomputable def hp749234 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp749067 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749235 := @hp749234 1 1 0 1 19959101 67108864 1 67108864 19959101 67108864 1

noncomputable def hp749236 := @Enclosure.Real.IsNear.of_eq (hp749067 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749237 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 803037 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749238 := @hp749236 (@Inv.inv Real Real.instInv (Real.sqrt hp749069)) Bool.false 19959101 67108864 1 67108864 (hp749237 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 803037 1000) 803037 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000))))

noncomputable def hp749239 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp749069)) Bool.false 19959101 67108864 1 67108864 19959101 67108864

noncomputable def hp749240 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp749069) Bool.false 225641410 67108864 6 67108864 112820705 33554432 3 33554432

noncomputable def hp749241 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 803037 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749242 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 803037 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749243 := @hp749242 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 803037 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8577002907159

noncomputable def hp749244 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 803037 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 803037 1000 0

noncomputable def hp749245 := @hp749244 1 10680707 67108864 1 67108864 8577002907159 67108864000 803037 67108864000 (Enclosure.Real.IsNear.const Bool.false 803037 1000) hd4949

noncomputable def hp749246 := @hp749243 67108864000 803037 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 803037 1000) 803037 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000))) (hp749245 rfl)

noncomputable def hp749247 := @hp749241 8577002907159 67108864000 803037 67108864000 379339184 379339221 33554432 hp749246 rfl rfl rfl

noncomputable def hp749248 := @Enclosure.Real.IsNear.recentre' hp749069 Bool.false 758678405 67108864 37 67108864 758678405 67108864 37 67108864 (hp749247 rfl rfl rfl)

noncomputable def hp749249 := @Enclosure.Real.IsNear.sqrt_image hp749069 758678405 67108864 37 67108864 112820702 112820708 33554432 (hp749248 rfl) rfl rfl

noncomputable def hp749250 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp749069) 112820705 33554432 3 33554432 9979550 9979551 33554432 (hp749240 (hp749249 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp749251 := @hp749235 67108864 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp749238 (@hp749239 1 67108864 (hp749250 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp749252 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749253 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp749254 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1))) (hp749252 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749253 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp749255 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 803037 1000) 803037 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl

noncomputable def hp749256 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749257 := @hp749256 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749253 (Enclosure.sfrac Bool.false 1 16)))) 197462505

noncomputable def hp749258 := @hp749257 67108864 2071 67108864 5155085 33554432 32513663 5709496320000 1017935997587925 2251799813685248 32947662430954427 1532631248189521920000

noncomputable def hp749259 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749260 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749261 := @hp749259 (@Neg.neg Real Real.instNeg hp749260) Bool.true 197462505 67108864 2071 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749262 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749263 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp749264 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp749265 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 8042831) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false

noncomputable def hp749266 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1))) Bool.false 18110845381219628603055

noncomputable def hp749267 := nat_lit 998484790310559281816479171

noncomputable def hp749268 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp749269 := @Enclosure.Real.IsNear.subLit_ff_p hp749069 (Enclosure.sfrac Bool.false 11 1) 758678405 67108864 37 67108864 11 1 0

noncomputable def hp749270 := @hp749268 500000000000000 20480901 67108864 37 67108864 18110845381219628603055 9444732965739290427392 hp749267 hp738031 hd4948 (@hp749269 1 20480901 20480901 67108864 37 67108864 (hp749248 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749271 := @hp749265 8042831 4194304 233 67108864 Bool.true 11403683 33554432 1 10890000 (@hp749266 9444732965739290427392 hp749267 hp738031 8042831 4194304 233 67108864 (hp749270 rfl) rfl) (Enclosure.sfrac_false_div 8042831 4194304)

noncomputable def hp749272 := nat_lit 8063542543294851204331730520143076155193657002577367584761271646401056395026846538482241

noncomputable def hp749273 := nat_lit 73266815943561227467123934183034311705044684041968605166074248597691041933379191361

noncomputable def hp749274 := nat_lit 48658086220576709733465482795359147411767027878780749064184474553778801039225686032335425

noncomputable def hp749275 := BSN.cos_dyadic_bound_t 8042831 4194304 4 3 33554432 10890000 hp749272 hp633286 hp749273 hp749274 hp633289

noncomputable def hp749276 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 8042831) (BSN.cosEvenQ 4194304) 0 3 hp749272 hp633286 hp749273 rfl rfl rfl

noncomputable def hp749277 := hp749275 hp749273 11403683 rfl rfl rfl rfl rfl rfl rfl rfl (hp749276 rfl)

noncomputable def hp749278 := @BSN.binarySplit_of_base3 (BSN.cosOddP 8042831) (BSN.cosOddQ 4194304) 0 3 hp749274 hp633289 hp749273 rfl rfl rfl

noncomputable def hp749279 := hp749271 (hp749277 (hp749278 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp749280 := @hp749263 11403683 33554432 162779929 45675970560000 (@hp749264 11403683 33554432 2604478864 730815528960000 11403683 33554432 162779929 45675970560000 hp749279 rfl)

noncomputable def hp749281 := @hp749262 11403683 33554432 162779929 45675970560000 98730217 98732288 33554432 hp749280 rfl rfl rfl

noncomputable def hp749282 := @Enclosure.Real.IsNear.recentre' hp749260 Bool.false 197462505 67108864 2071 67108864 197462505 67108864 2071 67108864 (hp749281 rfl rfl rfl)

noncomputable def hp749283 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749253 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp749284 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749253 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 115765521)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp749285 := nat_lit 1093374441646460812904860609045

noncomputable def hp749286 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749253 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp749285

noncomputable def hp749287 := nat_lit 21581390643055596975745875251341097

noncomputable def hp749288 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749253 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp749289 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp749290 := @hp749289 (Enclosure.sfrac Bool.false 1 16) 954982694034663 4503599627370496 3998616011 4503599627370496 1 16 0

noncomputable def hp749291 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)) 419467305771801

noncomputable def hp749292 := @hp749291 4503599627370496 1515588043 4503599627370496 20480901 67108864 37 67108864 64087803736325810552832 954982694034663 4503599627370496 3998616011

noncomputable def hp749293 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)) 20480901 67108864 37

noncomputable def hp749294 := @hp749293 67108864 20480901 67108864 37 67108864 419467305771801 4503599627370496 1515588043 4503599627370496 (@hp749269 1 20480901 20480901 67108864 37 67108864 (hp749248 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749295 := hp749294 (@hp749269 1 20480901 20480901 67108864 37 67108864 (hp749248 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749296 := @hp749292 4503599627370496 (hp749295 rfl) (@hp749269 1 20480901 20480901 67108864 37 67108864 (hp749248 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749297 := @hp749288 500000000000000 1236457670745319 4503599627370496 3998616011 4503599627370496 hp749285 hp627574 hp749287 hp742826 hd4948 (@hp749290 1 19783322731925104 1236457670745319 4503599627370496 3998616011 4503599627370496 (hp749296 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp749298 := @hp749284 115765521 67108864 47 8388608 Bool.true 5155085 33554432 1 10890000 (@hp749286 hp627574 hp749287 hp742826 115765521 67108864 47 8388608 (hp749297 rfl) rfl) (Enclosure.sfrac_true_div 115765521 67108864)

noncomputable def hp749299 := nat_lit 1482403968005404163616925978995733141317080752976318824111154278553953598844079984253428072708395273921

noncomputable def hp749300 := nat_lit 5793630152234849421664261886648832260686164704197355526732673373042919354195117237270156989992641

noncomputable def hp749301 := nat_lit 8961785281406758607130180065221710206950119597358476898088037695669230784396631168606353022768315141825

noncomputable def hp749302 := BSN.cos_dyadic_bound_t 115765521 67108864 4 3 33554432 10890000 hp749299 hp745658 hp749300 hp749301 hp745661

noncomputable def hp749303 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 115765521) (BSN.cosEvenQ 67108864) 0 3 hp749299 hp745658 hp749300 rfl rfl rfl

noncomputable def hp749304 := hp749302 hp749300 5155085 rfl rfl rfl rfl rfl rfl rfl rfl (hp749303 rfl)

noncomputable def hp749305 := @BSN.binarySplit_of_base3 (BSN.cosOddP 115765521) (BSN.cosOddQ 67108864) 0 3 hp749301 hp745661 hp749300 rfl rfl rfl

noncomputable def hp749306 := hp749298 (BSN.cos_neg_of_bound 115765521 67108864 Bool.true 5155085 33554432 1 10890000 (hp749304 (hp749305 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp749307 := hp749258 (hp749261 (@Enclosure.Real.IsNear.neg hp749260 Bool.false 197462505 67108864 2071 67108864 (hp749282 rfl))) (@hp749283 5155085 33554432 520218608 91351941120000 5155085 33554432 32513663 5709496320000 (hp749306 rfl) rfl)

noncomputable def hp749308 := @hp749233 67108864 1017935997587925 2251799813685248 32947662430954427 1532631248189521920000 20317087387393151455425 151115727451828646838272 73144287534371738588631 hp742600 (hp749251 rfl) (@hp749254 Bool.false 1017935997587925 2251799813685248 32947662430954427 1532631248189521920000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749069 (Enclosure.sfrac Bool.false 11 1)) (hp749255 rfl (hp749072 rfl rfl))) (hp749307 rfl))

noncomputable def hp749309 := @hp749066 hp749064 hp742600 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 803037 1000))) (@hp749071 hp749064 hp742600 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 803037 1000) 11 (hp749072 rfl rfl)) (@hp749075 hp749064 hp742600 hp749232 (hp749308 rfl) rfl rfl))

theorem hd5007 : hp749065 hp742600 := hp749309

noncomputable def hp749310 := nat_lit 18839974422992705720975807

noncomputable def hp749311 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 804332 1000)) Bool.true 63287336101024613243211 37778931862957161709568 hp749310

noncomputable def hp749312 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 804332 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 804332 1000)) Bool.true 63287336101024613243211 37778931862957161709568

noncomputable def hp749313 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 804332 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749314 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp749313 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749315 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 804332 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749316 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp749314 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp749317 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 804332 1000)) hp749316 Bool.true 63287336101024613243211 37778931862957161709568

noncomputable def hp749318 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 804332 1000) 804332 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl

noncomputable def hp749319 := @Enclosure.Real.IsNear.subLit_tt_n (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp749314 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp749320 := nat_lit 8494282462651902061582491844608

noncomputable def hp749321 := @hp749319 242617095 134217728 195187 268435456 5003305063707401021109 37778931862957161709568 143118457969692283535807 hp740088 hp749320 63287336101024613243211 37778931862957161709568

noncomputable def hp749322 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) 11)

noncomputable def hp749323 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) 11) hp749322

noncomputable def hp749324 := @Enclosure.Real.IsNear.addLit_tt (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) 11)

noncomputable def hp749325 := @hp749324 485234190 536870912 195187 536870912 485234190 536870912 195187 536870912 521016244237762560 242617095 134217728

noncomputable def hp749326 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) Real.sin Real.sin BSN.quadSignNeg

noncomputable def hp749327 := hp749326 BSN.quadSignNeg 9 10 11 804332 1000 193 241 536870912 268435456 9007199254740992

noncomputable def hp749328 := hp749327 Bool.false 831508392418 3666 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp749329 := hp749328 Bool.true 315199470 167563 Bool.true 39784292 Bool.true 717747630 28296951008113761 1 Bool.false 39747890

noncomputable def hp749330 := hp749329 Bool.true Bool.false 522253447 Bool.true Bool.true 485234190 195187 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 193 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 39747890 536870912) BSN.abs_quadSignNeg

noncomputable def hp749331 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) Real.cos Real.sin BSN.quadSignNeg

noncomputable def hp749332 := hp749331 BSN.quadSignPos 7 8 9 804332 1000 78 139 536870912 268435456 9007199254740992

noncomputable def hp749333 := hp749332 Bool.false 831508392418 3666 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp749334 := hp749333 Bool.true 279647984 136849 Bool.true 662598312 Bool.true 81740530 28296951008113761 1 Bool.false 177323090

noncomputable def hp749335 := hp749334 Bool.true Bool.false 81425089 Bool.false Bool.true 315199470 167563 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 177323090 536870912) BSN.abs_quadSignPos

noncomputable def hp749336 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp749337 := hp749336 BSN.quadSignNeg 5 6 7 804332 1000 68 10 536870912 268435456 9007199254740992

noncomputable def hp749338 := hp749337 Bool.false 831508392418 3666 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp749339 := hp749338 Bool.true 266757977 101696 Bool.false 441016388 Bool.true 346143224 28296951008113761 1 Bool.false 365692401

noncomputable def hp749340 := hp749339 Bool.false Bool.false 429096680 Bool.true Bool.true 279647984 136849 BSN.abs_quadSignPos (BSN.cos_quad_nat0 68 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 365692401 536870912) BSN.abs_quadSignNeg

noncomputable def hp749341 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp749342 := hp749341 BSN.quadSignNeg 3 4 5 804332 1000 276 161 536870912 268435456 9007199254740992

noncomputable def hp749343 := hp749342 Bool.false 831508392418 3666 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp749344 := hp749343 Bool.true 292523190 60109 Bool.false 120469712 Bool.false 743283732 28296951008113761 1 Bool.false 523411291

noncomputable def hp749345 := hp749344 Bool.false Bool.false 527578816 Bool.true Bool.true 266757977 101696 BSN.abs_quadSignPos (BSN.cos_quad_nat0 276 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 523411291 536870912) BSN.abs_quadSignNeg

noncomputable def hp749346 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) Real.sin Real.sin BSN.quadSignPos

noncomputable def hp749347 := hp749346 BSN.quadSignPos 1 2 3 804332 1000 631 423 536870912 268435456 9007199254740992

noncomputable def hp749348 := hp749347 Bool.false 831508392418 3666 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp749349 := hp749348 Bool.true 536870904 3722 Bool.false 60213229 Bool.false 380757492 28296951008113761 1 Bool.false 60087071

noncomputable def hp749350 := hp749349 Bool.false Bool.false 349631322 Bool.false Bool.true 292523190 60109 BSN.abs_quadSignPos (BSN.cos_quad_nat3 631 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 60087071 536870912) BSN.abs_quadSignPos

noncomputable def hp749351 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) 1) Bool.true

noncomputable def hp749352 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)))

noncomputable def hp749353 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000))) Bool.true 67108863 67108864

noncomputable def hp749354 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 25984637263) (@Nat.cast Real Real.instNatCast 16777216)) Bool.false 25984637263 16777216

noncomputable def hp749355 := nat_lit 518754286956793650852989284807589328879732743701080421

noncomputable def hp749356 := nat_lit 334938395910023700922694954498467766098200625152000

noncomputable def hp749357 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) Bool.false hp749355 hp749356 30446026500141571709

noncomputable def hp749358 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 804332 4000) (Real.log (Enclosure.sfrac Bool.false 2587800864896 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1608664))))))

noncomputable def hp749359 := nat_lit 161591457758314591325087138447360000

noncomputable def hp749360 := nat_lit 779839223041254330712125996356987781120

noncomputable def hp749361 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp749358 (Enclosure.sfrac Bool.false 804332 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 804332 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp749359 hp749360)) Bool.false

noncomputable def hp749362 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 804332 1000) 804332 1000 2587800864896 16000000 1608664

noncomputable def hp749363 := hp749362 4000 2000 hp749359 hp749360 (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl rfl rfl rfl

noncomputable def hp749364 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp749358 (Enclosure.sfrac Bool.false 804332 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 804332 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp749359 hp749360) 6975198885906179121933 4503599627370496000

noncomputable def hp749365 := nat_lit 5439532952000068592368240923064027881193946414591041035304960

noncomputable def hp749366 := @hp749364 30446026500141571709 hp739140 hp749359 hp749360 0 1 hp749365 hp749355 hp749356 30446026500141571709 hp739140

noncomputable def hp749367 := @Enclosure.Real.IsNear.subLit_ff_p (hp749358 (Enclosure.sfrac Bool.false 804332 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 804332 2000) (Real.log Real.pi)) 9048527522160904725261 4503599627370496000 317317652848213 136125000000000000000

noncomputable def hp749368 := nat_lit 117024418351807322863360278528000

noncomputable def hp749369 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 804332 4000) (Real.log (Enclosure.sfrac Bool.false 2587800864896 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1608664))))))

noncomputable def hp749370 := @hp749369 (Enclosure.sfrac Bool.false 804332 2000) 10859722169901987619597 4503599627370496000 317317652848213 136125000000000000000 804332 2000 0

noncomputable def hp749371 := nat_lit 18097055044321809450522000

noncomputable def hp749372 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 804332 4000) (Real.log (Enclosure.sfrac Bool.false 2587800864896 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1608664))))) 10861490029461652073597

noncomputable def hp749373 := nat_lit 24453920358858852847617836947714605056

noncomputable def hp749374 := @hp749372 4503599627370496000 2513541222649579 1089000000000000000000 883929779832227 2251799813685248 200000001089 8712000000000000000 hp749373 10859722169901987619597 4503599627370496000 317317652848213

noncomputable def hp749375 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 804332 4000) (Real.log (Enclosure.sfrac Bool.false 2587800864896 16000000)) 804332 4000 0 1 54014959143545959 4503599627370496

noncomputable def hp749376 := nat_lit 115996241508153031688978432

noncomputable def hp749377 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2587800864896) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp749376 hp617687

noncomputable def hp749378 := BSN.log_rat_reduce_isNear 2587800864896 16000000 17 5175601729792 4194304000000 56432701 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp749379 := nat_lit 219317665849903547693192139048813637199197654256153939377537117808618798929885664461450506113019040235520

noncomputable def hp749380 := nat_lit 807150658997961733566395332159443733060593187734409188902282203613454239003350653291254576770222915584

noncomputable def hp749381 := nat_lit 352659580596630229744991031494560172404390642594555613619662971136276159571411873286807911137280

noncomputable def hp749382 := BSN.log_dyadic_bound 490648864896 4684952864896 5 4 hp749379 268435456 87120000 hp749380 hp749381 56432701 5175601729792

noncomputable def hp749383 := hp749382 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp749384 := @BSN.binarySplit_of_base4 (BSN.artanhP 490648864896) (BSN.artanhQ 4684952864896) 0 4 hp749380 hp749379 hp749381 rfl rfl rfl

noncomputable def hp749385 := hp749378 rfl rfl rfl rfl (hp749383 (hp749384 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp749386 := @hp749375 12500018513 1089000000000000000 10861490029461652073597 4503599627370496000 2513541222649579 1089000000000000000000 (Enclosure.Real.IsNear.const Bool.false 804332 4000) (BSN.isNear_log_sfrac 2587800864896 16000000 54014959143545959 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp749377 1000001481040000 87120000000000000000000 54014959143545959 4503599627370496 12500018513 1089000000000000000 (hp749385 rfl rfl rfl) rfl)) rfl

noncomputable def hp749387 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1608664)))) 1 4

noncomputable def hp749388 := @hp749387 0 1 883929779832227 562949953421312 200000001089 2178000000000000000 883929779832227 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp749389 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1608664))) 884279719003555 562949953421312 1

noncomputable def hp749390 := @hp749389 2000000000000000 20858 33554432 1 10890000 29659761690155432280064 883929779832227 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp749391 := BSN.arctan_dyadic_bound_f 1000 1608664 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp749392 := hp749391 1 20858 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1608664) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1608664) 0 0 rfl)

noncomputable def hp749393 := hp749388 (hp749390 (hp749392 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp749394 := @hp749367 7723751054163 16777216000 603249 134217728000 hp749368 6975198885906179121933 4503599627370496000 30446026500141571709 hp739140 (@hp749370 1 hp749371 9048527522160904725261 4503599627370496000 317317652848213 136125000000000000000 (@hp749374 136125000000000000000 hp749386 hp749393 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 804332 2000) rfl rfl)

noncomputable def hp749395 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 804332 2000) (Real.log Real.pi) 804332 2000 0 1 38410761 33554432

noncomputable def hp749396 := hp749394 (@hp749395 3 268435456 7723751054163 16777216000 603249 134217728000 (Enclosure.Real.IsNear.const Bool.false 804332 2000) hd4909 rfl) rfl

noncomputable def hp749397 := @hp749357 hp739140 25984637263 16777216 459 67108864 (@hp749361 hp749355 hp749356 30446026500141571709 hp739140 (hp749363 rfl rfl rfl rfl rfl) (hp749366 (hp749396 rfl) (Enclosure.Real.IsNear.const Bool.true hp749359 hp749360) rfl rfl)) rfl

noncomputable def hp749398 := nat_lit 3797699708344405942337536

noncomputable def hp749399 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 25984637263) (@Nat.cast Real Real.instNatCast 16777216)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp749398) (@Nat.cast Real Real.instNatCast hp619230)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp749400 := BSN.sin_reduce_arg_pos_rat_q1 25984637263 16777216 226375608064910080 72057594037927936 246 hp749398 hp619230 rfl rfl rfl rfl

noncomputable def hp749401 := nat_lit 14376546603837855581115476255375798285696748666852123422581971238112674186712695895139830813280927711678330729378818811947089361757397860745216

noncomputable def hp749402 := nat_lit 10242588949467655138854023346965811068731307069089602393507706935561614321213804445683537924871514413778699109314491709560064812532105216

noncomputable def hp749403 := nat_lit 71793433592900484442864432414139897751591977656500925172080556921490778626222576342206842186831951150604531192982611519839658886724932994072576

noncomputable def hp749404 := BSN.sin_dyadic_bound_f 215874235228 137438953472 4 3 67108864 21801270 hp749401 hp737934 hp749402 hp749403 hp737937

noncomputable def hp749405 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 215874235228) (BSN.sinEvenQ 137438953472) 0 3 hp749401 hp737934 hp749402 rfl rfl rfl

noncomputable def hp749406 := hp749404 hp749402 67108863 rfl rfl rfl rfl rfl rfl rfl rfl (hp749405 rfl)

noncomputable def hp749407 := @BSN.binarySplit_of_base3 (BSN.sinOddP 215874235228) (BSN.sinOddQ 137438953472) 0 3 hp749403 hp737937 hp749402 rfl rfl rfl

noncomputable def hp749408 := @BSN.sin_arg_round Bool.false 67108863 67108864 hp749398 hp619230 215874235228 137438953472 21801270 21780000 (hp749406 (hp749407 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749409 := hp749399 67108863 67108864 246 1000000000000000 21780000 10890000 hp749400 BSN.pi_near_15 hp749408 rfl rfl

noncomputable def hp749410 := @hp749354 459 67108864 Bool.true 67108863 67108864 1 10890000 hp749397 (Enclosure.sfrac_false_div 25984637263 16777216) (hp749409 rfl rfl) rfl

noncomputable def hp749411 := @hp749351 67108863 67108864 316601179 45675970560000 536870904 536870912 3722 536870912 (@hp749352 Bool.true 67108863 67108864 316601179 45675970560000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000)) (@hp749353 5065618864 730815528960000 67108863 67108864 316601179 45675970560000 (hp749410 rfl) rfl))

noncomputable def hp749412 := @hp749357 hp739140 831508392418 536870912 3666 536870912 (@hp749361 hp749355 hp749356 30446026500141571709 hp739140 (hp749363 rfl rfl rfl rfl rfl) (hp749366 (hp749396 rfl) (Enclosure.Real.IsNear.const Bool.true hp749359 hp749360) rfl rfl)) rfl

noncomputable def hp749413 := hp749350 (BSN.cos_quad_nat3 423 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 349631322 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl rfl (hp749411 rfl) hp749412

noncomputable def hp749414 := nat_lit 13145214263518103855178142686481

noncomputable def hp749415 := BSN.sin_dyadic_bound_f 60213229 536870912 2 1 536870912 268435456 hp749414 hp708890 hp749414 hp749414 hp708891

noncomputable def hp749416 := @BSN.binarySplit_of_base (BSN.sinEvenP 60213229) (BSN.sinEvenQ 536870912) 0 1 hp749414 hp708890 hp749414 rfl rfl rfl

noncomputable def hp749417 := hp749415 hp749414 60087071 rfl rfl rfl rfl rfl rfl rfl rfl (hp749416 rfl)

noncomputable def hp749418 := @BSN.binarySplit_of_base (BSN.sinOddP 60213229) (BSN.sinOddQ 536870912) 0 1 hp749414 hp708891 hp749414 rfl rfl rfl

noncomputable def hp749419 := nat_lit 5280699404972422618961088118567043220031007500440037742160055527092060160

noncomputable def hp749420 := nat_lit 441761292682585472679472901010197261129728255313303107246585995657216

noncomputable def hp749421 := nat_lit 13829687970930096958894702116312049066420333417310543976816984288867188736

noncomputable def hp749422 := BSN.sin_dyadic_bound_f 380757492 536870912 3 2 536870912 268435456 hp749419 hp708845 hp749420 hp749421 hp708848

noncomputable def hp749423 := @BSN.binarySplit_of_base2 (BSN.sinEvenP 380757492) (BSN.sinEvenQ 536870912) 0 2 hp749419 hp708845 hp749420 rfl rfl rfl

noncomputable def hp749424 := hp749422 hp749420 349631322 rfl rfl rfl rfl rfl rfl rfl rfl (hp749423 rfl)

noncomputable def hp749425 := @BSN.binarySplit_of_base2 (BSN.sinOddP 380757492) (BSN.sinOddQ 536870912) 0 2 hp749421 hp708848 hp749420 rfl rfl rfl

noncomputable def hp749426 := hp749413 hd4911 hd4913 hd4915 hd4917 hd4918 (hp749417 (hp749418 rfl) rfl rfl rfl rfl) (hp749424 (hp749425 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749427 := hp749345 (BSN.cos_quad_nat1 161 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 527578816 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl rfl (hp749426 rfl rfl rfl rfl rfl) hp749412

noncomputable def hp749428 := nat_lit 210625761513120154426096720347136

noncomputable def hp749429 := BSN.cos_dyadic_bound_f 120469712 536870912 2 1 536870912 268435456 hp749428 hp708767 hp749428 hp749428 hp708768

noncomputable def hp749430 := @BSN.binarySplit_of_base (BSN.cosEvenP 120469712) (BSN.cosEvenQ 536870912) 0 1 hp749428 hp708767 hp749428 rfl rfl rfl

noncomputable def hp749431 := hp749429 hp749428 523411291 rfl rfl rfl rfl rfl rfl rfl rfl (hp749430 rfl)

noncomputable def hp749432 := @BSN.binarySplit_of_base (BSN.cosOddP 120469712) (BSN.cosOddQ 536870912) 0 1 hp749428 hp708768 hp749428 rfl rfl rfl

noncomputable def hp749433 := nat_lit 109447037895308619877876859433884517543865218184227370619485879755610212531802935797845466129174542163090211864576

noncomputable def hp749434 := nat_lit 28435150539263359720152692502996740743249613794713051285044452793917953175168026294365043986929661484466176

noncomputable def hp749435 := nat_lit 546824569240241728019348369838077614700570412700797001831077243145649900355904938307079454652864783992749593460736

noncomputable def hp749436 := BSN.sin_dyadic_bound_f 743283732 536870912 4 3 536870912 268435456 hp749433 hp642702 hp749434 hp749435 hp642705

noncomputable def hp749437 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 743283732) (BSN.sinEvenQ 536870912) 0 3 hp749433 hp642702 hp749434 rfl rfl rfl

noncomputable def hp749438 := hp749436 hp749434 527578816 rfl rfl rfl rfl rfl rfl rfl rfl (hp749437 rfl)

noncomputable def hp749439 := @BSN.binarySplit_of_base3 (BSN.sinOddP 743283732) (BSN.sinOddQ 536870912) 0 3 hp749435 hp642705 hp749434 rfl rfl rfl

noncomputable def hp749440 := hp749427 hd4920 hd4922 hd4924 hd4926 hd4918 (hp749431 (hp749432 rfl) rfl rfl rfl rfl) (hp749438 (hp749439 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749441 := hp749340 (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 429096680 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl rfl (hp749440 rfl rfl rfl rfl rfl) hp749412

noncomputable def hp749442 := nat_lit 5281112086045056670506783257862966322950929776646859645806505144185061376

noncomputable def hp749443 := nat_lit 1430994036439746770543932647555118385316782855978773896413314610692096

noncomputable def hp749444 := nat_lit 15840474270062290517979261908293788732082155764228621389626688803333799936

noncomputable def hp749445 := BSN.cos_dyadic_bound_f 441016388 536870912 3 2 536870912 268435456 hp749442 hp708868 hp749443 hp749444 hp708870

noncomputable def hp749446 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 441016388) (BSN.cosEvenQ 536870912) 0 2 hp749442 hp708868 hp749443 rfl rfl rfl

noncomputable def hp749447 := hp749445 hp749443 365692401 rfl rfl rfl rfl rfl rfl rfl rfl (hp749446 rfl)

noncomputable def hp749448 := @BSN.binarySplit_of_base2 (BSN.cosOddP 441016388) (BSN.cosOddQ 536870912) 0 2 hp749444 hp708870 hp749443 rfl rfl rfl

noncomputable def hp749449 := nat_lit 2003811129309860832795292984117478390625565377184682031720371272397357056

noncomputable def hp749450 := nat_lit 206085138879434039507933625875864625658519127437584640851500729368576

noncomputable def hp749451 := nat_lit 6011021217651823630306863085100683442625379093299170925879410815733334016

noncomputable def hp749452 := BSN.cos_dyadic_bound_f 346143224 536870912 3 2 536870912 268435456 hp749449 hp708868 hp749450 hp749451 hp708870

noncomputable def hp749453 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 346143224) (BSN.cosEvenQ 536870912) 0 2 hp749449 hp708868 hp749450 rfl rfl rfl

noncomputable def hp749454 := hp749452 hp749450 429096680 rfl rfl rfl rfl rfl rfl rfl rfl (hp749453 rfl)

noncomputable def hp749455 := @BSN.binarySplit_of_base2 (BSN.cosOddP 346143224) (BSN.cosOddQ 536870912) 0 2 hp749451 hp708870 hp749450 rfl rfl rfl

noncomputable def hp749456 := hp749441 hd4928 hd4930 hd4932 hd4934 hd4918 (hp749447 (hp749448 rfl) rfl rfl rfl rfl) (hp749454 (hp749455 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749457 := hp749335 (BSN.cos_quad_nat3 139 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 81425089 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl rfl (hp749456 rfl rfl rfl rfl rfl) hp749412

noncomputable def hp749458 := nat_lit 26587990011836251257475772501487783994932838846852438292864725855132703297654460303762569353877813986825114484736

noncomputable def hp749459 := nat_lit 7161498444732832063363253827997561710778391106221275375086527052146132460861180433195186911802994569773056

noncomputable def hp749460 := nat_lit 161152130900354696555619117201356841041493926575989943532314171962543615116631566099946332171246102210465979432960

noncomputable def hp749461 := BSN.cos_dyadic_bound_f 662598312 536870912 4 3 536870912 268435456 hp749458 hp716712 hp749459 hp749460 hp716714

noncomputable def hp749462 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 662598312) (BSN.cosEvenQ 536870912) 0 3 hp749458 hp716712 hp749459 rfl rfl rfl

noncomputable def hp749463 := hp749461 hp749459 177323090 rfl rfl rfl rfl rfl rfl rfl rfl (hp749462 rfl)

noncomputable def hp749464 := @BSN.binarySplit_of_base3 (BSN.cosOddP 662598312) (BSN.cosOddQ 536870912) 0 3 hp749460 hp716714 hp749459 rfl rfl rfl

noncomputable def hp749465 := nat_lit 44642632601873777633942824810000

noncomputable def hp749466 := BSN.sin_dyadic_bound_f 81740530 536870912 2 1 536870912 268435456 hp749465 hp708890 hp749465 hp749465 hp708891

noncomputable def hp749467 := @BSN.binarySplit_of_base (BSN.sinEvenP 81740530) (BSN.sinEvenQ 536870912) 0 1 hp749465 hp708890 hp749465 rfl rfl rfl

noncomputable def hp749468 := hp749466 hp749465 81425089 rfl rfl rfl rfl rfl rfl rfl rfl (hp749467 rfl)

noncomputable def hp749469 := @BSN.binarySplit_of_base (BSN.sinOddP 81740530) (BSN.sinOddQ 536870912) 0 1 hp749465 hp708891 hp749465 rfl rfl rfl

noncomputable def hp749470 := hp749457 hd4936 hd4938 hd4940 hd4942 hd4918 (hp749463 (hp749464 rfl) rfl rfl rfl rfl) (hp749468 (hp749469 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749471 := hp749330 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 522253447 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl rfl (hp749470 rfl rfl rfl rfl rfl) hp749412

noncomputable def hp749472 := nat_lit 2505223835700278606045369917696

noncomputable def hp749473 := BSN.sin_dyadic_bound_f 39784292 536870912 2 1 536870912 268435456 hp749472 hp708890 hp749472 hp749472 hp708891

noncomputable def hp749474 := @BSN.binarySplit_of_base (BSN.sinEvenP 39784292) (BSN.sinEvenQ 536870912) 0 1 hp749472 hp708890 hp749472 rfl rfl rfl

noncomputable def hp749475 := hp749473 hp749472 39747890 rfl rfl rfl rfl rfl rfl rfl rfl (hp749474 rfl)

noncomputable def hp749476 := @BSN.binarySplit_of_base (BSN.sinOddP 39784292) (BSN.sinOddQ 536870912) 0 1 hp749472 hp708891 hp749472 rfl rfl rfl

noncomputable def hp749477 := nat_lit 95148897844335473223807665995086624548536578751728728760180644684790621258363812546422514551722326712945830400000

noncomputable def hp749478 := nat_lit 18692233847402079688306845482090215634129077582892854416092824289940314566254595526288579486481000000000000

noncomputable def hp749479 := nat_lit 475434060594014221012824404284459900725511271634975499503372630055429860144812414377276937261849635390105152000000

noncomputable def hp749480 := BSN.sin_dyadic_bound_f 717747630 536870912 4 3 536870912 268435456 hp749477 hp642702 hp749478 hp749479 hp642705

noncomputable def hp749481 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 717747630) (BSN.sinEvenQ 536870912) 0 3 hp749477 hp642702 hp749478 rfl rfl rfl

noncomputable def hp749482 := hp749480 hp749478 522253447 rfl rfl rfl rfl rfl rfl rfl rfl (hp749481 rfl)

noncomputable def hp749483 := @BSN.binarySplit_of_base3 (BSN.sinOddP 717747630) (BSN.sinOddQ 536870912) 0 3 hp749479 hp642705 hp749478 rfl rfl rfl

noncomputable def hp749484 := hp749471 hd4944 hd4946 hd4961 hd4963 hd4918 (hp749475 (hp749476 rfl) rfl rfl rfl rfl) (hp749482 (hp749483 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749485 := @hp749325 195187 268435456 (hp749484 rfl rfl rfl rfl rfl) (hp749484 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp749486 := @hp749323 Bool.true 242617095 134217728 195187 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 804332 1000)) (Enclosure.sfrac Bool.false 804332 1000) 11) hp749485

noncomputable def hp749487 := @Enclosure.Real.IsNear.mulLit_tf hp749314 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1))) 9975531 33554432 1

noncomputable def hp749488 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp749313 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749489 := @hp749488 1 1 0 1 9975531 33554432 1 33554432 9975531 33554432 1

noncomputable def hp749490 := @Enclosure.Real.IsNear.of_eq (hp749313 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749491 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 804332 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749492 := @hp749490 (@Inv.inv Real Real.instInv (Real.sqrt hp749315)) Bool.false 9975531 33554432 1 33554432 (hp749491 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 804332 1000) 804332 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000))))

noncomputable def hp749493 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp749315)) Bool.false 19951062 67108864 2 67108864 9975531 33554432

noncomputable def hp749494 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp749315) Bool.false 225732324 67108864 6 67108864 56433081 16777216 3 33554432

noncomputable def hp749495 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 804332 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749496 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 804332 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749497 := @hp749496 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 804332 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 2147708605681

noncomputable def hp749498 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 804332 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 804332 1000 0

noncomputable def hp749499 := @hp749498 1 10680707 67108864 1 67108864 2147708605681 16777216000 201083 16777216000 (Enclosure.Real.IsNear.const Bool.false 804332 1000) hd4949

noncomputable def hp749500 := @hp749497 16777216000 201083 16777216000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 804332 1000) 804332 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000))) (hp749499 rfl)

noncomputable def hp749501 := @hp749495 2147708605681 16777216000 201083 16777216000 379644927 379644964 33554432 hp749500 rfl rfl rfl

noncomputable def hp749502 := @Enclosure.Real.IsNear.recentre' hp749315 Bool.false 759289891 67108864 37 67108864 759289891 67108864 37 67108864 (hp749501 rfl rfl rfl)

noncomputable def hp749503 := @Enclosure.Real.IsNear.sqrt_image hp749315 759289891 67108864 37 67108864 112866159 112866165 33554432 (hp749502 rfl) rfl rfl

noncomputable def hp749504 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp749315) 56433081 16777216 3 33554432 9975530 9975532 33554432 (hp749494 (hp749503 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp749505 := @hp749489 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp749492 (@hp749493 1 33554432 (hp749504 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp749506 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749507 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp749508 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1))) (hp749506 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749507 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp749509 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 804332 1000) 804332 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl

noncomputable def hp749510 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749511 := @hp749510 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749507 (Enclosure.sfrac Bool.false 1 16)))) 85355539

noncomputable def hp749512 := @hp749511 33554432 387 16777216 5876101 33554432 65707951 11418992640000 501557768073439 1125899906842624 3578182226617019 191578906023690240000

noncomputable def hp749513 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749514 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749515 := @hp749513 (@Neg.neg Real Real.instNeg hp749514) Bool.true 85355539 33554432 387 16777216 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749516 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749517 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp749518 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp749519 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 8282961) (@Nat.cast Real Real.instNatCast 4194304)) Bool.false

noncomputable def hp749520 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1))) Bool.false 18651570049474236435785

noncomputable def hp749521 := nat_lit 998484790315811906560402883

noncomputable def hp749522 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp749523 := @Enclosure.Real.IsNear.subLit_ff_p hp749315 (Enclosure.sfrac Bool.false 11 1) 759289891 67108864 37 67108864 11 1 0

noncomputable def hp749524 := @hp749522 500000000000000 21092387 67108864 37 67108864 18651570049474236435785 9444732965739290427392 hp749521 hp738031 hd4948 (@hp749523 1 21092387 21092387 67108864 37 67108864 (hp749502 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749525 := @hp749519 8282961 4194304 233 67108864 Bool.true 13190707 33554432 1 10890000 (@hp749520 9444732965739290427392 hp749521 hp738031 8282961 4194304 233 67108864 (hp749524 rfl) rfl) (Enclosure.sfrac_false_div 8282961 4194304)

noncomputable def hp749526 := nat_lit 9079593406654679151061342964535556840872562829359640995551738086954436847569554354379201

noncomputable def hp749527 := nat_lit 104286333323308890214275586698305949240117382770087754419528742840997491317303581121

noncomputable def hp749528 := nat_lit 54752880428872894919612674768181337072881300664748362805176065594900313597614348592388545

noncomputable def hp749529 := BSN.cos_dyadic_bound_t 8282961 4194304 4 3 33554432 10890000 hp749526 hp633286 hp749527 hp749528 hp633289

noncomputable def hp749530 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 8282961) (BSN.cosEvenQ 4194304) 0 3 hp749526 hp633286 hp749527 rfl rfl rfl

noncomputable def hp749531 := hp749529 hp749527 13190707 rfl rfl rfl rfl rfl rfl rfl rfl (hp749530 rfl)

noncomputable def hp749532 := @BSN.binarySplit_of_base3 (BSN.cosOddP 8282961) (BSN.cosOddQ 4194304) 0 3 hp749528 hp633289 hp749527 rfl rfl rfl

noncomputable def hp749533 := hp749525 (hp749531 (hp749532 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp749534 := @hp749517 13190707 33554432 162779929 45675970560000 (@hp749518 13190707 33554432 2604478864 730815528960000 13190707 33554432 162779929 45675970560000 hp749533 rfl)

noncomputable def hp749535 := @hp749516 13190707 33554432 162779929 45675970560000 85354765 85356313 33554432 hp749534 rfl rfl rfl

noncomputable def hp749536 := @Enclosure.Real.IsNear.recentre' hp749514 Bool.false 170711078 67108864 1548 67108864 85355539 33554432 387 16777216 (hp749535 rfl rfl rfl)

noncomputable def hp749537 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749507 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp749538 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749507 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 58613735)) (@Nat.cast Real Real.instNatCast 33554432)) Bool.true

noncomputable def hp749539 := nat_lit 1107182157507751138567732811525

noncomputable def hp749540 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749507 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp749539

noncomputable def hp749541 := nat_lit 21825614431234528401667616022670157

noncomputable def hp749542 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749507 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp749543 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp749544 := @hp749543 (Enclosure.sfrac Bool.false 1 16) 970597341260599 4503599627370496 4043865975 4503599627370496 1 16 0

noncomputable def hp749545 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)) 444888789357769

noncomputable def hp749546 := @hp749545 4503599627370496 1560838007 4503599627370496 21092387 67108864 37 67108864 65135684973419126849536 970597341260599 4503599627370496 4043865975

noncomputable def hp749547 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)) 21092387 67108864 37

noncomputable def hp749548 := @hp749547 67108864 21092387 67108864 37 67108864 444888789357769 4503599627370496 1560838007 4503599627370496 (@hp749523 1 21092387 21092387 67108864 37 67108864 (hp749502 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749549 := hp749548 (@hp749523 1 21092387 21092387 67108864 37 67108864 (hp749502 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749550 := @hp749546 4503599627370496 (hp749549 rfl) (@hp749523 1 21092387 21092387 67108864 37 67108864 (hp749502 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749551 := @hp749542 500000000000000 1252072317971255 4503599627370496 4043865975 4503599627370496 hp749539 hp627574 hp749541 hp742826 hd4948 (@hp749544 1 20033157087540080 1252072317971255 4503599627370496 4043865975 4503599627370496 (hp749550 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp749552 := @hp749538 58613735 33554432 95 16777216 Bool.true 5876101 33554432 1 10890000 (@hp749540 hp627574 hp749541 hp742826 58613735 33554432 95 16777216 (hp749551 rfl) rfl) (Enclosure.sfrac_true_div 58613735 33554432)

noncomputable def hp749553 := nat_lit 380648966361297345635385190457098581348334484177237362077929205991536997297868146255129706919390625

noncomputable def hp749554 := nat_lit 1644344302643848685260188252111372694784564118563265877257186057072961824586164300644775390625

noncomputable def hp749555 := nat_lit 2300776708864321946961544701601032851237323732651546809244147518240195553228083775119522339648990625

noncomputable def hp749556 := BSN.cos_dyadic_bound_t 58613735 33554432 4 3 33554432 10890000 hp749553 hp681868 hp749554 hp749555 hp681871

noncomputable def hp749557 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 58613735) (BSN.cosEvenQ 33554432) 0 3 hp749553 hp681868 hp749554 rfl rfl rfl

noncomputable def hp749558 := hp749556 hp749554 5876101 rfl rfl rfl rfl rfl rfl rfl rfl (hp749557 rfl)

noncomputable def hp749559 := @BSN.binarySplit_of_base3 (BSN.cosOddP 58613735) (BSN.cosOddQ 33554432) 0 3 hp749555 hp681871 hp749554 rfl rfl rfl

noncomputable def hp749560 := hp749552 (BSN.cos_neg_of_bound 58613735 33554432 Bool.true 5876101 33554432 1 10890000 (hp749558 (hp749559 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp749561 := hp749512 (hp749515 (@Enclosure.Real.IsNear.neg hp749514 Bool.false 85355539 33554432 387 16777216 (hp749536 rfl))) (@hp749537 5876101 33554432 1051327216 182703882240000 5876101 33554432 65707951 11418992640000 (hp749560 rfl) rfl)

noncomputable def hp749562 := @hp749487 33554432 501557768073439 1125899906842624 3578182226617019 191578906023690240000 5003305063707401021109 37778931862957161709568 143118457969692283535807 hp740088 (hp749505 rfl) (@hp749508 Bool.false 501557768073439 1125899906842624 3578182226617019 191578906023690240000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749315 (Enclosure.sfrac Bool.false 11 1)) (hp749509 rfl (hp749318 rfl rfl))) (hp749561 rfl))

noncomputable def hp749563 := @hp749312 hp749310 hp740088 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 804332 1000))) (@hp749317 hp749310 hp740088 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 804332 1000) 11 (hp749318 rfl rfl)) (@hp749321 hp749310 hp740088 hp749486 (hp749562 rfl) rfl rfl))

theorem hd5008 : hp749311 hp740088 := hp749563

noncomputable def hp749564 := nat_lit 12567330852490598761832437

noncomputable def hp749565 := Enclosure.Real.IsNear (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 805627 1000)) Bool.false 1618589635396057945663 1180591620717411303424 hp749564

noncomputable def hp749566 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 805627 1000)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 805627 1000)) Bool.false 1618589635396057945663 1180591620717411303424

noncomputable def hp749567 := @HPow.hPow Real Real Real (@instHPow Real Real Real.instPow) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 805627 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749568 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp749567 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749569 := Real.sqrt (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 805627 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749570 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp749568 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp749571 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 805627 1000)) hp749570 Bool.false 1618589635396057945663 1180591620717411303424

noncomputable def hp749572 := @BSN.floor_sqrt_eq_dec (Enclosure.sfrac Bool.false 805627 1000) 805627 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl

noncomputable def hp749573 := @Enclosure.Real.IsNear.subLit_ft (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) 11) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) hp749568 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1))))

noncomputable def hp749574 := nat_lit 27155427928400909702904414208

noncomputable def hp749575 := @hp749573 20811517 16777216 195505 268435456 154109319673952589375 1180591620717411303424 82452845103411971432437 hp741590 hp749574 1618589635396057945663 1180591620717411303424

noncomputable def hp749576 := @HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) 11)

noncomputable def hp749577 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.mainSumOfPhase (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) 11) hp749576

noncomputable def hp749578 := @Enclosure.Real.IsNear.addLit_ff (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) 11) (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) 11)

noncomputable def hp749579 := @hp749578 332984272 536870912 195505 536870912 332984272 536870912 195505 536870912 357539139580592128 20811517 16777216

noncomputable def hp749580 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) Real.cos Real.sin BSN.quadSignPos

noncomputable def hp749581 := hp749580 BSN.quadSignNeg 9 10 11 805627 1000 192 241 536870912 268435456 9007199254740992

noncomputable def hp749582 := hp749581 Bool.false 833195389975 3672 1236190956 51 169773496 8 1287360220 51 161872664 8

noncomputable def hp749583 := hp749582 Bool.false 474316230 167836 Bool.true 796968880 Bool.true 697881558 28296951008113761 1 Bool.false 46288434

noncomputable def hp749584 := hp749583 Bool.false Bool.false 517292816 Bool.true Bool.false 332984272 195505 BSN.abs_quadSignPos (BSN.cos_quad_nat0 192 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 46288434 536870912) BSN.abs_quadSignNeg

noncomputable def hp749585 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) Real.cos Real.cos BSN.quadSignNeg

noncomputable def hp749586 := hp749585 BSN.quadSignNeg 7 8 9 805627 1000 78 138 536870912 268435456 9007199254740992

noncomputable def hp749587 := hp749586 Bool.false 833195389975 3672 1116391676 51 189812536 8 1179625948 51 178956968 8

noncomputable def hp749588 := hp749587 Bool.false 634406655 137072 Bool.true 421327976 Bool.true 765673432 28296951008113761 1 Bool.false 379857948

noncomputable def hp749589 := hp749588 Bool.true Bool.false 77371068 Bool.true Bool.false 474316230 167836 BSN.abs_quadSignNeg (BSN.cos_quad_nat2 78 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 379857948 536870912) BSN.abs_quadSignNeg

noncomputable def hp749590 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) Real.sin Real.cos BSN.quadSignNeg

noncomputable def hp749591 := hp749590 BSN.quadSignNeg 5 6 7 805627 1000 69 10 536870912 268435456 9007199254740992

noncomputable def hp749592 := hp749591 Bool.false 833195389975 3672 961943533 51 219176632 8 1044702541 51 202918136 8

noncomputable def hp749593 := hp749592 Bool.false 853174246 101862 Bool.false 38982214 Bool.true 12035457 28296951008113761 1 Bool.false 38947969

noncomputable def hp749594 := hp749593 Bool.true Bool.false 536736013 Bool.true Bool.false 634406655 137072 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 69 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 38947969 536870912) BSN.abs_quadSignNeg

noncomputable def hp749595 := hp749590 BSN.quadSignNeg 3 4 5 805627 1000 277 162 536870912 268435456 9007199254740992

noncomputable def hp749596 := hp749595 Bool.false 833195389975 3672 744261104 50 268435448 8 864060384 50 240095976 8

noncomputable def hp749597 := hp749596 Bool.false 1007843338 60208 Bool.false 334283 Bool.false 468008235 28296951008113761 1 Bool.false 334282

noncomputable def hp749598 := hp749597 Bool.true Bool.false 345476856 Bool.true Bool.false 853174246 101862 BSN.abs_quadSignNeg (BSN.cos_quad_nat1 277 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 334282 536870912) BSN.abs_quadSignNeg

noncomputable def hp749599 := BSN.mainSumRS_step2 (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) Real.cos Real.cos BSN.quadSignPos

noncomputable def hp749600 := hp749599 BSN.quadSignPos 1 2 3 805627 1000 632 424 536870912 268435456 9007199254740992

noncomputable def hp749601 := hp749600 Bool.false 833195389975 3672 372130544 50 379625064 8 589812976 50 309962568 8

noncomputable def hp749602 := hp749601 Bool.false 536870816 3730 Bool.false 421986875 Bool.false 460632389 28296951008113761 1 Bool.false 379392036

noncomputable def hp749603 := hp749602 Bool.false Bool.false 351089883 Bool.false Bool.false 1007843338 60208 BSN.abs_quadSignPos (BSN.cos_quad_nat0 632 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 379392036 536870912) BSN.abs_quadSignPos

noncomputable def hp749604 := @Enclosure.Real.IsNear.recentre' (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) 1) Bool.false

noncomputable def hp749605 := @Enclosure.Real.IsNear.of_eq (BSN.mainSumRS (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) 1) (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)))

noncomputable def hp749606 := @Enclosure.Real.IsNear.recentre' (Real.cos (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000))) Bool.false 67108852 67108864

noncomputable def hp749607 := @Enclosure.Real.IsNear.cos_image (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 52074711873) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false 52074711873 33554432

noncomputable def hp749608 := nat_lit 68792934945766099455112061148973172320181227341334660927933

noncomputable def hp749609 := nat_lit 44326848381335445584943892748007368682275319299702784000

noncomputable def hp749610 := @Enclosure.Real.IsNear.recentre' (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) Bool.false hp749608 hp749609 13553280311131242069

noncomputable def hp749611 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 805627 4000) (Real.log (Enclosure.sfrac Bool.false 2596140452516 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1611254))))))

noncomputable def hp749612 := nat_lit 162896489602357260050182430515360000

noncomputable def hp749613 := nat_lit 787403002912431403802598111028163584320

noncomputable def hp749614 := @Enclosure.Real.IsNear.of_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (@HAdd.hAdd Real Real Real (@instHAdd Real Real.instAdd) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp749611 (Enclosure.sfrac Bool.false 805627 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 805627 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp749612 hp749613)) Bool.false

noncomputable def hp749615 := BSN.riemannSiegelThetaApproximant_two_zero_mk (Enclosure.sfrac Bool.false 805627 1000) 805627 1000 2596140452516 16000000 1611254

noncomputable def hp749616 := hp749615 4000 2000 hp749612 hp749613 (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl rfl rfl rfl

noncomputable def hp749617 := @Enclosure.Real.IsNear.addLit_ft_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (hp749611 (Enclosure.sfrac Bool.false 805627 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 805627 2000) (Real.log Real.pi))) (Enclosure.sfrac Bool.true hp749612 hp749613) 27957401782446112598333 18014398509481984000

noncomputable def hp749618 := nat_lit 22013739182645151825635859567671415142457992749227091496938560

noncomputable def hp749619 := @hp749617 13553280311131242069 hp740132 hp749612 hp749613 0 1 hp749618 hp749608 hp749609 13553280311131242069 hp740132

noncomputable def hp749620 := @Enclosure.Real.IsNear.subLit_ff_p (hp749611 (Enclosure.sfrac Bool.false 805627 2000)) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 805627 2000) (Real.log Real.pi)) 7252813765320387584473 3602879701896396800 1130039157235239 484000000000000000000

noncomputable def hp749621 := nat_lit 375237894802306751538043184742400

noncomputable def hp749622 := @Enclosure.Real.IsNear.subLit_ff_p (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 805627 4000) (Real.log (Enclosure.sfrac Bool.false 2596140452516 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1611254))))))

noncomputable def hp749623 := @hp749622 (Enclosure.sfrac Bool.false 805627 2000) 43520511740601159084349 18014398509481984000 1130039157235239 484000000000000000000 805627 2000 0

noncomputable def hp749624 := nat_lit 72528137653203875844730000

noncomputable def hp749625 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 805627 4000) (Real.log (Enclosure.sfrac Bool.false 2596140452516 16000000))) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1611254))))) 43527583183269001924349

noncomputable def hp749626 := nat_lit 97999480228972338162943792486968983552

noncomputable def hp749627 := @hp749625 18014398509481984000 10070352414572651 4356000000000000000000 883930333480355 2251799813685248 200000001089 8712000000000000000 hp749626 43520511740601159084349 18014398509481984000 1130039157235239

noncomputable def hp749628 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 805627 4000) (Real.log (Enclosure.sfrac Bool.false 2596140452516 16000000)) 805627 4000 0 1 54029449339792487 4503599627370496

noncomputable def hp749629 := nat_lit 116027358967648761545752576

noncomputable def hp749630 := @Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2596140452516) (@Nat.cast Real Real.instNatCast 16000000))) Bool.false hp749629 hp617687

noncomputable def hp749631 := BSN.log_rat_reduce_isNear 2596140452516 16000000 17 5192280905032 4194304000000 57296384 268435456 24973259072661432 36028797018963968 87120000 1000000000000000

noncomputable def hp749632 := nat_lit 222460416522265056164687445751569226316491435806612059544865876415462665272746658057380329343875294494720

noncomputable def hp749633 := nat_lit 843949866663500692147547202106053637718162417336008607225179406245138856870452382797597648765831348224

noncomputable def hp749634 := nat_lit 403564784477696908770906308962601695708151222223705523138973494541292471327161058996715317166080

noncomputable def hp749635 := BSN.log_dyadic_bound 498988452516 4693292452516 5 4 hp749632 268435456 87120000 hp749633 hp749634 57296384 5192280905032

noncomputable def hp749636 := hp749635 4194304000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl

noncomputable def hp749637 := @BSN.binarySplit_of_base4 (BSN.artanhP 498988452516) (BSN.artanhQ 4693292452516) 0 4 hp749633 hp749632 hp749634 rfl rfl rfl

noncomputable def hp749638 := hp749631 rfl rfl rfl rfl (hp749636 (hp749637 rfl) rfl rfl rfl rfl) BSN.log2_near_15 rfl

noncomputable def hp749639 := @hp749628 12500018513 1089000000000000000 43527583183269001924349 18014398509481984000 10070352414572651 4356000000000000000000 (Enclosure.Real.IsNear.const Bool.false 805627 4000) (BSN.isNear_log_sfrac 2596140452516 16000000 54029449339792487 4503599627370496 12500018513 1089000000000000000 Bool.false (@hp749630 1000001481040000 87120000000000000000000 54029449339792487 4503599627370496 12500018513 1089000000000000000 (hp749638 rfl rfl rfl) rfl)) rfl

noncomputable def hp749640 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 4) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1611254)))) 1 4

noncomputable def hp749641 := @hp749640 0 1 883930333480355 562949953421312 200000001089 2178000000000000000 883930333480355 2251799813685248 200000001089 8712000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 4)

noncomputable def hp749642 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 1 2) Real.pi) (Real.arctan (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 1000) (@Nat.cast Real Real.instNatCast 1611254))) 884279719003555 562949953421312 1

noncomputable def hp749643 := @hp749642 2000000000000000 20825 33554432 1 10890000 29659780267503895183360 883930333480355 562949953421312 200000001089 2178000000000000000 (@hp615317 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 (Enclosure.Real.IsNear.const Bool.false 1 2) BSN.pi_near_15 rfl)

noncomputable def hp749644 := BSN.arctan_dyadic_bound_f 1000 1611254 1 0 33554432 10890000 0 1 1 0 1

noncomputable def hp749645 := hp749644 1 20825 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 1611254) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 1611254) 0 0 rfl)

noncomputable def hp749646 := hp749641 (hp749643 (hp749645 rfl rfl rfl rfl) rfl rfl) rfl

noncomputable def hp749647 := @hp749620 30944746152147 67108864000 2416881 536870912000 hp749621 27957401782446112598333 18014398509481984000 13553280311131242069 hp740132 (@hp749623 1 hp749624 7252813765320387584473 3602879701896396800 1130039157235239 484000000000000000000 (@hp749627 484000000000000000000 hp749639 hp749646 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 805627 2000) rfl rfl)

noncomputable def hp749648 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 805627 2000) (Real.log Real.pi) 805627 2000 0 1 38410761 33554432

noncomputable def hp749649 := hp749647 (@hp749648 3 268435456 30944746152147 67108864000 2416881 536870912000 (Enclosure.Real.IsNear.const Bool.false 805627 2000) hd4909 rfl) rfl

noncomputable def hp749650 := @hp749610 hp740132 52074711873 33554432 115 16777216 (@hp749614 hp749608 hp749609 13553280311131242069 hp740132 (hp749616 rfl rfl rfl rfl rfl) (hp749619 (hp749649 rfl) (Enclosure.Real.IsNear.const Bool.true hp749612 hp749613) rfl rfl)) rfl

noncomputable def hp749651 := BSN.cos_reduce0 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 52074711873) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 2807667995059186302976) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp749652 := BSN.sin_reduce_arg_pos_rat_q0 52074711873 33554432 226375608064910080 72057594037927936 247 2807667995059186302976 hp619237 rfl rfl rfl rfl

noncomputable def hp749653 := BSN.cos_dyadic_bound_f 79798723 137438953472 1 0 67108864 21801270 0 1 1 0 1

noncomputable def hp749654 := hp749653 1 67108852 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 79798723) (BSN.cosEvenQ 137438953472) 0 0 rfl)

noncomputable def hp749655 := hp749654 (@BSN.binarySplit_of_le (BSN.cosOddP 79798723) (BSN.cosOddQ 137438953472) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp749656 := @BSN.cos_arg_round Bool.false 67108852 67108864 2807667995059186302976 hp619237 79798723 137438953472 21801270 21780000 hp749655 rfl

noncomputable def hp749657 := hp749651 67108852 67108864 247 1000000000000000 21780000 10890000 hp749652 BSN.pi_near_15 hp749656 rfl rfl

noncomputable def hp749658 := @hp749607 115 16777216 Bool.false 67108852 67108864 1 10890000 hp749650 (Enclosure.sfrac_false_div 52074711873 33554432) (hp749657 rfl rfl) rfl

noncomputable def hp749659 := @hp749604 16777213 16777216 79320451 11418992640000 536870816 536870912 3730 536870912 (@hp749605 Bool.false 16777213 16777216 79320451 11418992640000 (BSN.main_sum_rs_one (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000)) (@hp749606 1269127216 182703882240000 16777213 16777216 79320451 11418992640000 (hp749658 rfl) rfl))

noncomputable def hp749660 := @hp749610 hp740132 833195389975 536870912 3672 536870912 (@hp749614 hp749608 hp749609 13553280311131242069 hp740132 (hp749616 rfl rfl rfl rfl rfl) (hp749619 (hp749649 rfl) (Enclosure.Real.IsNear.const Bool.true hp749612 hp749613) rfl rfl)) rfl

noncomputable def hp749661 := hp749603 (BSN.cos_quad_nat0 424 rfl) (BSN.sfrac_eq_quadSignPos_mul Bool.false 351089883 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl rfl (hp749659 rfl) hp749660

noncomputable def hp749662 := nat_lit 4426731820508976300995638143478036262277914646621923170211411285400390625

noncomputable def hp749663 := nat_lit 1005521930342257970765442417323617749079766538017429411411285400390625

noncomputable def hp749664 := nat_lit 13278184417666244387045383545599461551335584406789734651811411285400390625

noncomputable def hp749665 := BSN.cos_dyadic_bound_f 421986875 536870912 3 2 536870912 268435456 hp749662 hp708868 hp749663 hp749664 hp708870

noncomputable def hp749666 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 421986875) (BSN.cosEvenQ 536870912) 0 2 hp749662 hp708868 hp749663 rfl rfl rfl

noncomputable def hp749667 := hp749665 hp749663 379392036 rfl rfl rfl rfl rfl rfl rfl rfl (hp749666 rfl)

noncomputable def hp749668 := @BSN.binarySplit_of_base2 (BSN.cosOddP 421986875) (BSN.cosOddQ 536870912) 0 2 hp749664 hp708870 hp749663 rfl rfl rfl

noncomputable def hp749669 := nat_lit 6285599929650944488671213629174664188143832816089302775516061210569275361

noncomputable def hp749670 := nat_lit 2026916108586688855668495232710209631436842912378364894330089244915681

noncomputable def hp749671 := nat_lit 18852745956735660088302303897058572145168624762443151596759523453217994721

noncomputable def hp749672 := BSN.cos_dyadic_bound_f 460632389 536870912 3 2 536870912 268435456 hp749669 hp708868 hp749670 hp749671 hp708870

noncomputable def hp749673 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 460632389) (BSN.cosEvenQ 536870912) 0 2 hp749669 hp708868 hp749670 rfl rfl rfl

noncomputable def hp749674 := hp749672 hp749670 351089883 rfl rfl rfl rfl rfl rfl rfl rfl (hp749673 rfl)

noncomputable def hp749675 := @BSN.binarySplit_of_base2 (BSN.cosOddP 460632389) (BSN.cosOddQ 536870912) 0 2 hp749671 hp708870 hp749670 rfl rfl rfl

noncomputable def hp749676 := hp749661 hd4911 hd4913 hd4915 hd4917 hd4918 (hp749667 (hp749668 rfl) rfl rfl rfl rfl) (hp749674 (hp749675 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749677 := hp749598 (BSN.cos_quad_nat2 162 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 345476856 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl rfl (hp749676 rfl rfl rfl rfl rfl) hp749660

noncomputable def hp749678 := BSN.sin_dyadic_bound_f 334283 536870912 1 0 536870912 268435456 0 1 1 0 1

noncomputable def hp749679 := hp749678 1 334282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 334283) (BSN.sinEvenQ 536870912) 0 0 rfl)

noncomputable def hp749680 := hp749679 (@BSN.binarySplit_of_le (BSN.sinOddP 334283) (BSN.sinOddQ 536870912) 0 0 rfl) rfl rfl rfl rfl

noncomputable def hp749681 := nat_lit 6698105990070062093287347515803700028838854188495250384353792524927190625

noncomputable def hp749682 := nat_lit 2301589986228096180916632797343315061533678219940077412725667250390625

noncomputable def hp749683 := nat_lit 20089714790237730087500209281816413456393495209045870998235926240280790625

noncomputable def hp749684 := BSN.cos_dyadic_bound_f 468008235 536870912 3 2 536870912 268435456 hp749681 hp708868 hp749682 hp749683 hp708870

noncomputable def hp749685 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 468008235) (BSN.cosEvenQ 536870912) 0 2 hp749681 hp708868 hp749682 rfl rfl rfl

noncomputable def hp749686 := hp749684 hp749682 345476856 rfl rfl rfl rfl rfl rfl rfl rfl (hp749685 rfl)

noncomputable def hp749687 := @BSN.binarySplit_of_base2 (BSN.cosOddP 468008235) (BSN.cosOddQ 536870912) 0 2 hp749683 hp708870 hp749682 rfl rfl rfl

noncomputable def hp749688 := hp749677 hd4920 hd4922 hd4924 hd4926 hd4918 hp749680 (hp749686 (hp749687 rfl) rfl rfl rfl rfl) rfl rfl

noncomputable def hp749689 := hp749594 (BSN.cos_quad_nat2 10 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 536736013 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl rfl (hp749688 rfl rfl rfl rfl) hp749660

noncomputable def hp749690 := nat_lit 2309223695121603359481560505616

noncomputable def hp749691 := BSN.sin_dyadic_bound_f 38982214 536870912 2 1 536870912 268435456 hp749690 hp708890 hp749690 hp749690 hp708891

noncomputable def hp749692 := @BSN.binarySplit_of_base (BSN.sinEvenP 38982214) (BSN.sinEvenQ 536870912) 0 1 hp749690 hp708890 hp749690 rfl rfl rfl

noncomputable def hp749693 := hp749691 hp749690 38947969 rfl rfl rfl rfl rfl rfl rfl rfl (hp749692 rfl)

noncomputable def hp749694 := @BSN.binarySplit_of_base (BSN.sinOddP 38982214) (BSN.sinOddQ 536870912) 0 1 hp749690 hp708891 hp749690 rfl rfl rfl

noncomputable def hp749695 := nat_lit 20982167145058065217590924801

noncomputable def hp749696 := BSN.cos_dyadic_bound_f 12035457 536870912 2 1 536870912 268435456 hp749695 hp708767 hp749695 hp749695 hp708768

noncomputable def hp749697 := @BSN.binarySplit_of_base (BSN.cosEvenP 12035457) (BSN.cosEvenQ 536870912) 0 1 hp749695 hp708767 hp749695 rfl rfl rfl

noncomputable def hp749698 := hp749696 hp749695 536736013 rfl rfl rfl rfl rfl rfl rfl rfl (hp749697 rfl)

noncomputable def hp749699 := @BSN.binarySplit_of_base (BSN.cosOddP 12035457) (BSN.cosOddQ 536870912) 0 1 hp749695 hp708768 hp749695 rfl rfl rfl

noncomputable def hp749700 := hp749689 hd4928 hd4930 hd4932 hd4934 hd4918 (hp749693 (hp749694 rfl) rfl rfl rfl rfl) (hp749698 (hp749699 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749701 := hp749589 (BSN.cos_quad_nat2 138 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 77371068 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl rfl (hp749700 rfl rfl rfl rfl rfl) hp749660

noncomputable def hp749702 := nat_lit 4399142320796637855895351390104478238397779672166562373114386611391430656

noncomputable def hp749703 := nat_lit 993030017062090094841601755063357040533594927753670319714052578738176

noncomputable def hp749704 := nat_lit 13195440902355789387496370966803308001112271826644179778703731729016815616

noncomputable def hp749705 := BSN.cos_dyadic_bound_f 421327976 536870912 3 2 536870912 268435456 hp749702 hp708868 hp749703 hp749704 hp708870

noncomputable def hp749706 := @BSN.binarySplit_of_base2 (BSN.cosEvenP 421327976) (BSN.cosEvenQ 536870912) 0 2 hp749702 hp708868 hp749703 rfl rfl rfl

noncomputable def hp749707 := hp749705 hp749703 379857948 rfl rfl rfl rfl rfl rfl rfl rfl (hp749706 rfl)

noncomputable def hp749708 := @BSN.binarySplit_of_base2 (BSN.cosOddP 421327976) (BSN.cosOddQ 536870912) 0 2 hp749704 hp708870 hp749703 rfl rfl rfl

noncomputable def hp749709 := nat_lit 47459980739964375362674044802712638233582688272661712060412409994508195723023668794207956070285389149860272275456

noncomputable def hp749710 := nat_lit 40599710232612800322154604055440845159429502047283342412118248465295181612724548911772069660573095350501376

noncomputable def hp749711 := nat_lit 287452153850335695153307348705924147869709062046139720449646301033718291203375385713274812434273346183116514918400

noncomputable def hp749712 := BSN.cos_dyadic_bound_f 765673432 536870912 4 3 536870912 268435456 hp749709 hp716712 hp749710 hp749711 hp716714

noncomputable def hp749713 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 765673432) (BSN.cosEvenQ 536870912) 0 3 hp749709 hp716712 hp749710 rfl rfl rfl

noncomputable def hp749714 := hp749712 hp749710 77371068 rfl rfl rfl rfl rfl rfl rfl rfl (hp749713 rfl)

noncomputable def hp749715 := @BSN.binarySplit_of_base3 (BSN.cosOddP 765673432) (BSN.cosOddQ 536870912) 0 3 hp749711 hp716714 hp749710 rfl rfl rfl

noncomputable def hp749716 := hp749701 hd4936 hd4938 hd4940 hd4942 hd4918 (hp749707 (hp749708 rfl) rfl rfl rfl rfl) (hp749714 (hp749715 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749717 := hp749584 (BSN.cos_quad_nat1 241 rfl) (BSN.sfrac_not_eq_quadSignNeg_mul Bool.false 517292816 536870912) (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl rfl (hp749716 rfl rfl rfl rfl rfl) hp749660

noncomputable def hp749718 := nat_lit 55731946281701414098561785206776269723940412021007463160465192097919358309081024823062357711546566473416704000000

noncomputable def hp749719 := nat_lit 65659317032431951897151741848574082695506438982397675977231449036255264055259548257895481081856000000000000

noncomputable def hp749720 := nat_lit 337457148712949492477257267119202237333666145284681346502492970494705245427479419223915331921081346417072537600000

noncomputable def hp749721 := BSN.cos_dyadic_bound_f 796968880 536870912 4 3 536870912 268435456 hp749718 hp716712 hp749719 hp749720 hp716714

noncomputable def hp749722 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 796968880) (BSN.cosEvenQ 536870912) 0 3 hp749718 hp716712 hp749719 rfl rfl rfl

noncomputable def hp749723 := hp749721 hp749719 46288434 rfl rfl rfl rfl rfl rfl rfl rfl (hp749722 rfl)

noncomputable def hp749724 := @BSN.binarySplit_of_base3 (BSN.cosOddP 796968880) (BSN.cosOddQ 536870912) 0 3 hp749720 hp716714 hp749719 rfl rfl rfl

noncomputable def hp749725 := nat_lit 85034446512039472367646730985220356112943913456150489024832883169338655192534456121918608749813765463115934273536

noncomputable def hp749726 := nat_lit 13346907891615791270102274848673864534970867639968017325418225834903622371480575346361476939501532876967936

noncomputable def hp749727 := nat_lit 424924244772416310467248740256496684890123880012836270485946232225702704495532584297045917182338040234091703504896

noncomputable def hp749728 := BSN.sin_dyadic_bound_f 697881558 536870912 4 3 536870912 268435456 hp749725 hp642702 hp749726 hp749727 hp642705

noncomputable def hp749729 := @BSN.binarySplit_of_base3 (BSN.sinEvenP 697881558) (BSN.sinEvenQ 536870912) 0 3 hp749725 hp642702 hp749726 rfl rfl rfl

noncomputable def hp749730 := hp749728 hp749726 517292816 rfl rfl rfl rfl rfl rfl rfl rfl (hp749729 rfl)

noncomputable def hp749731 := @BSN.binarySplit_of_base3 (BSN.sinOddP 697881558) (BSN.sinOddQ 536870912) 0 3 hp749727 hp642705 hp749726 rfl rfl rfl

noncomputable def hp749732 := hp749717 hd4944 hd4946 hd4961 hd4963 hd4918 (hp749723 (hp749724 rfl) rfl rfl rfl rfl) (hp749730 (hp749731 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749733 := @hp749579 195505 268435456 (hp749732 rfl rfl rfl rfl rfl) (hp749732 rfl rfl rfl rfl rfl) rfl rfl

noncomputable def hp749734 := @hp749577 Bool.false 20811517 16777216 195505 268435456 (BSN.main_sum_of_phase_eq (riemannSiegelThetaApproximant 2 0 (Enclosure.sfrac Bool.false 805627 1000)) (Enclosure.sfrac Bool.false 805627 1000) 11) hp749733

noncomputable def hp749735 := @Enclosure.Real.IsNear.mulLit_tf hp749568 (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1))) 155805 524288 1

noncomputable def hp749736 := @Enclosure.Real.IsNear.mulLit_tf (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) (@Neg.neg Real Real.instNeg (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne))) 11) (hp749567 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749737 := @hp749736 1 1 0 1 155805 524288 1 33554432 155805 524288 1

noncomputable def hp749738 := @Enclosure.Real.IsNear.of_eq (hp749567 (@Neg.neg Real Real.instNeg (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@OfNat.ofNat Real 1 (@One.toOfNat1 Real Real.instOne)) (@OfNat.ofNat Real 4 (@instOfNatAtLeastTwo Real 4 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 3 (@Nat.instNeZeroSucc 2)))))))

noncomputable def hp749739 := BSN.rpow_neg_quarter_mk (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 805627 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749740 := @hp749738 (@Inv.inv Real Real.instInv (Real.sqrt hp749569)) Bool.false 155805 524288 1 33554432 (hp749739 (BSN.t_div_two_pi_nonneg (Enclosure.sfrac Bool.false 805627 1000) 805627 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000))))

noncomputable def hp749741 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt hp749569)) Bool.false 19943040 67108864 2 67108864 155805 524288

noncomputable def hp749742 := @Enclosure.Real.IsNear.recentre' (Real.sqrt hp749569) Bool.false 225823128 67108864 6 67108864 28227891 8388608 3 33554432

noncomputable def hp749743 := @Enclosure.Real.IsNear.sqrt_image (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 805627 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749744 := @Enclosure.Real.IsNear.of_eq (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (Enclosure.sfrac Bool.false 805627 1000) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@OfNat.ofNat Real 2 (@instOfNatAtLeastTwo Real 2 Real.instNatCast (@Nat.instAtLeastTwoHAddOfNat 1 (@Nat.instNeZeroSucc 0)))) Real.pi))

noncomputable def hp749745 := @hp749744 (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 805627 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi))) Bool.false 8604665938289

noncomputable def hp749746 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 805627 1000) (@Inv.inv Real Real.instInv (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi)) 805627 1000 0

noncomputable def hp749747 := @hp749746 1 10680707 67108864 1 67108864 8604665938289 67108864000 805627 67108864000 (Enclosure.Real.IsNear.const Bool.false 805627 1000) hd4949

noncomputable def hp749748 := @hp749745 67108864000 805627 67108864000 (BSN.t_div_two_pi_mk (Enclosure.sfrac Bool.false 805627 1000) 805627 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000))) (hp749747 rfl)

noncomputable def hp749749 := @hp749743 8604665938289 67108864000 805627 67108864000 379950425 379950461 33554432 hp749748 rfl rfl rfl

noncomputable def hp749750 := @Enclosure.Real.IsNear.recentre' hp749569 Bool.false 759900886 67108864 36 67108864 379950443 33554432 9 16777216 (hp749749 rfl rfl rfl)

noncomputable def hp749751 := @Enclosure.Real.IsNear.sqrt_image hp749569 379950443 33554432 9 16777216 112911561 112911567 33554432 (hp749750 rfl) rfl rfl

noncomputable def hp749752 := @Enclosure.Real.IsNear.inv_image (Real.sqrt hp749569) 28227891 8388608 3 33554432 9971519 9971521 33554432 (hp749742 (hp749751 rfl rfl rfl rfl) rfl) rfl

noncomputable def hp749753 := @hp749737 33554432 (@hp740271 1 0 1 (BSN.neg_one_pow_odd_mk 11 rfl) (Enclosure.Real.IsNear.const Bool.true 1 1)) (hp749740 (@hp749741 1 33554432 (hp749752 rfl rfl rfl rfl rfl) rfl))

noncomputable def hp749754 := @HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749755 := @HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp749756 := @Enclosure.Real.IsNear.of_eq (Zeta.RiemannSiegel.correction (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1))) (hp749754 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749755 (Enclosure.sfrac Bool.false 1 16)))))

noncomputable def hp749757 := BSN.cos_two_pi_p_ne_zero_mk (Enclosure.sfrac Bool.false 805627 1000) 805627 1000 11 (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl

noncomputable def hp749758 := @Enclosure.Real.IsNear.mulLit_tt (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749759 := @hp749758 (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749755 (Enclosure.sfrac Bool.false 1 16)))) 150792275

noncomputable def hp749760 := @hp749759 67108864 1183 67108864 6559465 33554432 258067429 45675970560000 989116650132875 2251799813685248 2061582161422843 127719270682460160000

noncomputable def hp749761 := @Enclosure.Real.IsNear.of_eq (@Inv.inv Real Real.instInv (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749762 := @Inv.inv Real Real.instInv (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749763 := @hp749761 (@Neg.neg Real Real.instNeg hp749762) Bool.true 150792275 67108864 1183 67108864 (BSN.inv_eq_neg_inv_neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749764 := @Enclosure.Real.IsNear.inv_image (@Neg.neg Real Real.instNeg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)))))

noncomputable def hp749765 := @Enclosure.Real.IsNear.neg (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp749766 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)))) Bool.true

noncomputable def hp749767 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 68183185) (@Nat.cast Real Real.instNatCast 33554432)) Bool.false

noncomputable def hp749768 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1))) Bool.false 9595930268193406761505

noncomputable def hp749769 := nat_lit 242874678728004067047818239

noncomputable def hp749770 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)) 884279719003555 140737488355328 1

noncomputable def hp749771 := @Enclosure.Real.IsNear.subLit_ff_p hp749569 (Enclosure.sfrac Bool.false 11 1) 379950443 33554432 9 16777216 11 1 0

noncomputable def hp749772 := @hp749770 500000000000000 10851691 33554432 9 16777216 9595930268193406761505 4722366482869645213696 hp749769 hp631123 hd4948 (@hp749771 1 10851691 10851691 33554432 9 16777216 (hp749750 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749773 := @hp749767 68183185 33554432 57 16777216 Bool.true 29866249 67108864 1 10890000 (@hp749768 4722366482869645213696 hp749769 hp631123 68183185 33554432 57 16777216 (hp749772 rfl) rfl) (Enclosure.sfrac_false_div 68183185 33554432)

noncomputable def hp749774 := nat_lit 2230327582613198088437760

noncomputable def hp749775 := BSN.cos_reduce1 (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast 68183185) (@Nat.cast Real Real.instNatCast 33554432)) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Nat.cast Real Real.instNatCast hp749774) (@Nat.cast Real Real.instNatCast hp619237)) 226375608064910080 72057594037927936 Bool.false

noncomputable def hp749776 := BSN.sin_reduce_arg_pos_rat_q1 68183185 33554432 226375608064910080 72057594037927936 0 hp749774 hp619237 rfl rfl rfl rfl

noncomputable def hp749777 := nat_lit 16146388650848561199566631978419965456198561

noncomputable def hp749778 := nat_lit 42817430781178796431748579083484854091482398720

noncomputable def hp749779 := nat_lit 299722015468251575022240053584393978640376791040

noncomputable def hp749780 := BSN.sin_dyadic_bound_f 63389722487 137438953472 2 1 67108864 21801270 hp749777 hp749778 hp749777 hp749777 hp749779

noncomputable def hp749781 := @BSN.binarySplit_of_base (BSN.sinEvenP 63389722487) (BSN.sinEvenQ 137438953472) 0 1 hp749777 hp749778 hp749777 rfl rfl rfl

noncomputable def hp749782 := hp749780 hp749777 29866249 rfl rfl rfl rfl rfl rfl rfl rfl (hp749781 rfl)

noncomputable def hp749783 := @BSN.binarySplit_of_base (BSN.sinOddP 63389722487) (BSN.sinOddQ 137438953472) 0 1 hp749777 hp749779 hp749777 rfl rfl rfl

noncomputable def hp749784 := @BSN.sin_arg_round Bool.false 29866249 67108864 hp749774 hp619237 63389722487 137438953472 21801270 21780000 (hp749782 (hp749783 rfl) rfl rfl rfl rfl) rfl

noncomputable def hp749785 := hp749775 29866249 67108864 0 1000000000000000 21780000 10890000 hp749776 BSN.pi_near_15 hp749784 rfl rfl

noncomputable def hp749786 := @hp749765 29866249 67108864 39844201 11418992640000 (@hp749766 29866249 67108864 637507216 182703882240000 29866249 67108864 39844201 11418992640000 (hp749773 (hp749785 rfl rfl) rfl rfl) rfl)

noncomputable def hp749787 := @hp749764 29866249 67108864 39844201 11418992640000 75395546 75396729 33554432 hp749786 rfl rfl rfl

noncomputable def hp749788 := @Enclosure.Real.IsNear.recentre' hp749762 Bool.false 150792275 67108864 1183 67108864 150792275 67108864 1183 67108864 (hp749787 rfl rfl rfl)

noncomputable def hp749789 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749755 (Enclosure.sfrac Bool.false 1 16)))) Bool.true

noncomputable def hp749790 := @Enclosure.Real.IsNear.cos_image (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749755 (Enclosure.sfrac Bool.false 1 16))) (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid)) (@Neg.neg Real Real.instNeg (@Nat.cast Real Real.instNatCast 118618313)) (@Nat.cast Real Real.instNatCast 67108864)) Bool.true

noncomputable def hp749791 := nat_lit 280079572860913220496064380725

noncomputable def hp749792 := @Enclosure.Real.IsNear.recentre' (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749755 (Enclosure.sfrac Bool.false 1 16))) Bool.true hp749791

noncomputable def hp749793 := nat_lit 1677591024123867167655921082289827

noncomputable def hp749794 := @Enclosure.Real.IsNear.mulLit_ft (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (Enclosure.sfrac Bool.false 2 1) Real.pi) (hp749755 (Enclosure.sfrac Bool.false 1 16)) 884279719003555 140737488355328 1

noncomputable def hp749795 := @Enclosure.Real.IsNear.subLit_tf (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)))

noncomputable def hp749796 := @hp749795 (Enclosure.sfrac Bool.false 1 16) 246363130185031 1125899906842624 62165061 70368744177664 1 16 0

noncomputable def hp749797 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1))) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)) 117759197559481

noncomputable def hp749798 := @hp749797 1125899906842624 24416325 70368744177664 10851691 33554432 9 16777216 8266574899100770107392 246363130185031 1125899906842624 62165061

noncomputable def hp749799 := @Enclosure.Real.IsNear.mulLit_ff (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)) (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)) 10851691 33554432 9

noncomputable def hp749800 := @hp749799 16777216 10851691 33554432 9 16777216 117759197559481 1125899906842624 24416325 70368744177664 (@hp749771 1 10851691 10851691 33554432 9 16777216 (hp749750 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749801 := hp749800 (@hp749771 1 10851691 10851691 33554432 9 16777216 (hp749750 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749802 := @hp749798 70368744177664 (hp749801 rfl) (@hp749771 1 10851691 10851691 33554432 9 16777216 (hp749750 rfl) (Enclosure.Real.IsNear.const Bool.false 11 1) rfl rfl)

noncomputable def hp749803 := @hp749794 500000000000000 316731874362695 1125899906842624 62165061 70368744177664 hp749791 hp682141 hp749793 hp634263 hd4948 (@hp749796 1 5067709989803120 316731874362695 1125899906842624 62165061 70368744177664 (hp749802 rfl rfl) (Enclosure.Real.IsNear.const Bool.false 1 16) rfl rfl)

noncomputable def hp749804 := @hp749790 118618313 67108864 373 67108864 Bool.true 6559465 33554432 1 10890000 (@hp749792 hp682141 hp749793 hp634263 118618313 67108864 373 67108864 (hp749803 rfl) rfl) (Enclosure.sfrac_true_div 118618313 67108864)

noncomputable def hp749805 := nat_lit 1634894809792979042631004490718953518661867699174298011092724115091811662204635357140582129776034273761

noncomputable def hp749806 := nat_lit 7759270959286676751823471962113211971913700317241443729077837627943087981466074388060663200307681

noncomputable def hp749807 := nat_lit 9880127330608729726954661064504913166618924550960723815917565054608388560193295044820997144820200987105

noncomputable def hp749808 := BSN.cos_dyadic_bound_t 118618313 67108864 4 3 33554432 10890000 hp749805 hp745658 hp749806 hp749807 hp745661

noncomputable def hp749809 := @BSN.binarySplit_of_base3 (BSN.cosEvenP 118618313) (BSN.cosEvenQ 67108864) 0 3 hp749805 hp745658 hp749806 rfl rfl rfl

noncomputable def hp749810 := hp749808 hp749806 6559465 rfl rfl rfl rfl rfl rfl rfl rfl (hp749809 rfl)

noncomputable def hp749811 := @BSN.binarySplit_of_base3 (BSN.cosOddP 118618313) (BSN.cosOddQ 67108864) 0 3 hp749807 hp745661 hp749806 rfl rfl rfl

noncomputable def hp749812 := hp749804 (BSN.cos_neg_of_bound 118618313 67108864 Bool.true 6559465 33554432 1 10890000 (hp749810 (hp749811 rfl) rfl rfl rfl rfl)) rfl

noncomputable def hp749813 := hp749760 (hp749763 (@Enclosure.Real.IsNear.neg hp749762 Bool.false 150792275 67108864 1183 67108864 (hp749788 rfl))) (@hp749789 6559465 33554432 4129078864 730815528960000 6559465 33554432 258067429 45675970560000 (hp749812 rfl) rfl)

noncomputable def hp749814 := @hp749735 33554432 989116650132875 2251799813685248 2061582161422843 127719270682460160000 154109319673952589375 1180591620717411303424 82452845103411971432437 hp741590 (hp749753 rfl) (@hp749756 Bool.false 989116650132875 2251799813685248 2061582161422843 127719270682460160000 (BSN.correction_mk (@HSub.hSub Real Real Real (@instHSub Real Real.instSub) hp749569 (Enclosure.sfrac Bool.false 11 1)) (hp749757 rfl (hp749572 rfl rfl))) (hp749813 rfl))

noncomputable def hp749815 := @hp749566 hp749564 hp741590 (@Eq.refl Real (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 805627 1000))) (@hp749571 hp749564 hp741590 (BSN.hardyZApproximantRS₀_eq (Enclosure.sfrac Bool.false 805627 1000) 11 (hp749572 rfl rfl)) (@hp749575 hp749564 hp741590 hp749734 (hp749814 rfl) rfl rfl))

theorem hd5009 : hp749565 hp741590 := hp749815

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

noncomputable def hp790762 := @Enclosure.Real.IsNear.of_eq (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000)) Bool.false 556919581 10737418240 1213 10737418240

noncomputable def hp791697 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) 799149 1000 800445 1000

noncomputable def hp791698 := hp791697 (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl rfl rfl

noncomputable def hp791699 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698))

noncomputable def hp791700 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 799149 1000) 799149 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) rfl rfl

noncomputable def hp791701 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698))

noncomputable def hp791702 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698)) 99586979194371739750349

noncomputable def hp791703 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 799149 1000))

noncomputable def hp791704 := @hp791702 75557863725914323419136 hp748296 hp740088 (@hp791703 Bool.true 99586979194371739750349 75557863725914323419136 hp748296 hp740088 (hd4340 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698) hd5004)

noncomputable def hp791705 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698)) 4336259190851626260111

noncomputable def hp791706 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 800445 1000))

noncomputable def hp791707 := @hp791705 1180591620717411303424 209342818390221548923717 hp748549 (@hp791706 Bool.false 4336259190851626260111 1180591620717411303424 209342818390221548923717 hp748549 (hd4359 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698) hd5005)

noncomputable def hp791708 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698) hp791700 (hp791701 (hp791704 rfl rfl rfl) (hp791707 rfl rfl rfl))

noncomputable def hp791709 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791710 := hp791709 (Enclosure.sfrac Bool.false 799149 1000) 749551 1000 799149 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791711 := hp791710 (@Eq.refl Real (Enclosure.sfrac Bool.false 799149 1000)) rfl rfl rfl rfl

noncomputable def hp791712 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791713 := @hp791712 Bool.true Bool.false 99586979194371739750349 75557863725914323419136 hp748296 hp740088 556919581 10737418240 1213 10737418240 (@hp791703 Bool.true 99586979194371739750349 75557863725914323419136 hp748296 hp740088 (hd4340 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698) hd5004)

noncomputable def hp791714 := hp791713 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791715 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791716 := hp791715 (Enclosure.sfrac Bool.false 800445 1000) 749551 1000 800445 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791717 := hp791716 (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl rfl rfl rfl

noncomputable def hp791718 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791719 := @hp791718 Bool.false Bool.false 4336259190851626260111 1180591620717411303424 209342818390221548923717 hp748549 556919581 10737418240 1213 10737418240 (@hp791706 Bool.false 4336259190851626260111 1180591620717411303424 209342818390221548923717 hp748549 (hd4359 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698) hd5005)

noncomputable def hp791720 := hp791719 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791722 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) 800445 1000 801741 1000

noncomputable def hp791723 := hp791722 (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl rfl rfl

noncomputable def hp791724 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723))

noncomputable def hp791725 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 800445 1000) 800445 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl rfl

noncomputable def hp791726 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723))

noncomputable def hp791727 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723)) 4336259190851626260111

noncomputable def hp791728 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 800445 1000))

noncomputable def hp791729 := @hp791727 1180591620717411303424 209342818390221548923717 hp748549 (@hp791728 Bool.false 4336259190851626260111 1180591620717411303424 209342818390221548923717 hp748549 (hd4340 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723) hd5005)

noncomputable def hp791730 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723)) 7484371100719826081219

noncomputable def hp791731 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 801741 1000))

noncomputable def hp791732 := @hp791730 18889465931478580854784 hp748807 hp740088 (@hp791731 Bool.true 7484371100719826081219 18889465931478580854784 hp748807 hp740088 (hd4359 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723) hd5006)

noncomputable def hp791733 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723) hp791725 (hp791726 (hp791729 rfl rfl rfl) (hp791732 rfl rfl rfl))

noncomputable def hp791734 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791735 := hp791734 (Enclosure.sfrac Bool.false 800445 1000) 749551 1000 800445 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791736 := hp791735 (@Eq.refl Real (Enclosure.sfrac Bool.false 800445 1000)) rfl rfl rfl rfl

noncomputable def hp791737 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791738 := @hp791737 Bool.false Bool.false 4336259190851626260111 1180591620717411303424 209342818390221548923717 hp748549 556919581 10737418240 1213 10737418240 (@hp791728 Bool.false 4336259190851626260111 1180591620717411303424 209342818390221548923717 hp748549 (hd4340 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723) hd5005)

noncomputable def hp791739 := hp791738 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791740 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791741 := hp791740 (Enclosure.sfrac Bool.false 801741 1000) 749551 1000 801741 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791742 := hp791741 (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl rfl rfl rfl

noncomputable def hp791743 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791744 := @hp791743 Bool.true Bool.false 7484371100719826081219 18889465931478580854784 hp748807 hp740088 556919581 10737418240 1213 10737418240 (@hp791731 Bool.true 7484371100719826081219 18889465931478580854784 hp748807 hp740088 (hd4359 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723) hd5006)

noncomputable def hp791745 := hp791744 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791747 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) 801741 1000 803037 1000

noncomputable def hp791748 := hp791747 (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl rfl rfl

noncomputable def hp791749 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748))

noncomputable def hp791750 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 801741 1000) 801741 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl rfl

noncomputable def hp791751 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748))

noncomputable def hp791752 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748)) 7484371100719826081219

noncomputable def hp791753 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 801741 1000))

noncomputable def hp791754 := @hp791752 18889465931478580854784 hp748807 hp740088 (@hp791753 Bool.true 7484371100719826081219 18889465931478580854784 hp748807 hp740088 (hd4340 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748) hd5006)

noncomputable def hp791755 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748)) 49210302343757826609345

noncomputable def hp791756 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 803037 1000))

noncomputable def hp791757 := @hp791755 151115727451828646838272 hp749064 hp742600 (@hp791756 Bool.false 49210302343757826609345 151115727451828646838272 hp749064 hp742600 (hd4359 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748) hd5007)

noncomputable def hp791758 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748) hp791750 (hp791751 (hp791754 rfl rfl rfl) (hp791757 rfl rfl rfl))

noncomputable def hp791759 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791760 := hp791759 (Enclosure.sfrac Bool.false 801741 1000) 749551 1000 801741 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791761 := hp791760 (@Eq.refl Real (Enclosure.sfrac Bool.false 801741 1000)) rfl rfl rfl rfl

noncomputable def hp791762 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791763 := @hp791762 Bool.true Bool.false 7484371100719826081219 18889465931478580854784 hp748807 hp740088 556919581 10737418240 1213 10737418240 (@hp791753 Bool.true 7484371100719826081219 18889465931478580854784 hp748807 hp740088 (hd4340 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748) hd5006)

noncomputable def hp791764 := hp791763 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791765 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791766 := hp791765 (Enclosure.sfrac Bool.false 803037 1000) 749551 1000 803037 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791767 := hp791766 (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl rfl rfl rfl

noncomputable def hp791768 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791769 := @hp791768 Bool.false Bool.false 49210302343757826609345 151115727451828646838272 hp749064 hp742600 556919581 10737418240 1213 10737418240 (@hp791756 Bool.false 49210302343757826609345 151115727451828646838272 hp749064 hp742600 (hd4359 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748) hd5007)

noncomputable def hp791770 := hp791769 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791772 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) 803037 1000 804332 1000

noncomputable def hp791773 := hp791772 (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl rfl rfl

noncomputable def hp791774 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773))

noncomputable def hp791775 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 803037 1000) 803037 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl rfl

noncomputable def hp791776 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773))

noncomputable def hp791777 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773)) 49210302343757826609345

noncomputable def hp791778 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 803037 1000))

noncomputable def hp791779 := @hp791777 151115727451828646838272 hp749064 hp742600 (@hp791778 Bool.false 49210302343757826609345 151115727451828646838272 hp749064 hp742600 (hd4340 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773) hd5007)

noncomputable def hp791780 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773)) 63287336101024613243211

noncomputable def hp791781 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 804332 1000))

noncomputable def hp791782 := @hp791780 37778931862957161709568 hp749310 hp740088 (@hp791781 Bool.true 63287336101024613243211 37778931862957161709568 hp749310 hp740088 (hd4359 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773) hd5008)

noncomputable def hp791783 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773) hp791775 (hp791776 (hp791779 rfl rfl rfl) (hp791782 rfl rfl rfl))

noncomputable def hp791784 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791785 := hp791784 (Enclosure.sfrac Bool.false 803037 1000) 749551 1000 803037 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791786 := hp791785 (@Eq.refl Real (Enclosure.sfrac Bool.false 803037 1000)) rfl rfl rfl rfl

noncomputable def hp791787 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791788 := @hp791787 Bool.false Bool.false 49210302343757826609345 151115727451828646838272 hp749064 hp742600 556919581 10737418240 1213 10737418240 (@hp791778 Bool.false 49210302343757826609345 151115727451828646838272 hp749064 hp742600 (hd4340 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773) hd5007)

noncomputable def hp791789 := hp791788 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791790 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791791 := hp791790 (Enclosure.sfrac Bool.false 804332 1000) 749551 1000 804332 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791792 := hp791791 (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl rfl rfl rfl

noncomputable def hp791793 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791794 := @hp791793 Bool.true Bool.false 63287336101024613243211 37778931862957161709568 hp749310 hp740088 556919581 10737418240 1213 10737418240 (@hp791781 Bool.true 63287336101024613243211 37778931862957161709568 hp749310 hp740088 (hd4359 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773) hd5008)

noncomputable def hp791795 := hp791794 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791797 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) 804332 1000 805627 1000

noncomputable def hp791798 := hp791797 (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl rfl rfl

noncomputable def hp791799 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798))

noncomputable def hp791800 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 804332 1000) 804332 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl rfl

noncomputable def hp791801 := BSN.mul_neg_of_neg_pos_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798))

noncomputable def hp791802 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798)) 63287336101024613243211

noncomputable def hp791803 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 804332 1000))

noncomputable def hp791804 := @hp791802 37778931862957161709568 hp749310 hp740088 (@hp791803 Bool.true 63287336101024613243211 37778931862957161709568 hp749310 hp740088 (hd4340 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798) hd5008)

noncomputable def hp791805 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798)) 1618589635396057945663

noncomputable def hp791806 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 805627 1000))

noncomputable def hp791807 := @hp791805 1180591620717411303424 hp749564 hp741590 (@hp791806 Bool.false 1618589635396057945663 1180591620717411303424 hp749564 hp741590 (hd4359 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798) hd5009)

noncomputable def hp791808 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798) hp791800 (hp791801 (hp791804 rfl rfl rfl) (hp791807 rfl rfl rfl))

noncomputable def hp791809 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791810 := hp791809 (Enclosure.sfrac Bool.false 804332 1000) 749551 1000 804332 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791811 := hp791810 (@Eq.refl Real (Enclosure.sfrac Bool.false 804332 1000)) rfl rfl rfl rfl

noncomputable def hp791812 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791813 := @hp791812 Bool.true Bool.false 63287336101024613243211 37778931862957161709568 hp749310 hp740088 556919581 10737418240 1213 10737418240 (@hp791803 Bool.true 63287336101024613243211 37778931862957161709568 hp749310 hp740088 (hd4340 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798) hd5008)

noncomputable def hp791814 := hp791813 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791815 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791816 := hp791815 (Enclosure.sfrac Bool.false 805627 1000) 749551 1000 805627 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791817 := hp791816 (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl rfl rfl rfl

noncomputable def hp791818 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791819 := @hp791818 Bool.false Bool.false 1618589635396057945663 1180591620717411303424 hp749564 hp741590 556919581 10737418240 1213 10737418240 (@hp791806 Bool.false 1618589635396057945663 1180591620717411303424 hp749564 hp741590 (hd4359 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798) hd5009)

noncomputable def hp791820 := hp791819 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791822 := @Enclosure.dec_le_dec (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) 805627 1000 806921 1000

noncomputable def hp791823 := hp791822 (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl rfl rfl

noncomputable def hp791824 := @Or.inr (Zeta.Certificates.ZIntervalRS.Certificate (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823)) (Zeta.Certificates.ZIntervalRS.Certificate₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823))

noncomputable def hp791825 := @BSN.thirtyTwoPi_le_dec (Enclosure.sfrac Bool.false 805627 1000) 805627 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl rfl

noncomputable def hp791826 := BSN.mul_neg_of_pos_neg_r (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823)) (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823))

noncomputable def hp791827 := @Enclosure.Real.IsNear.pos_val (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823)) 1618589635396057945663

noncomputable def hp791828 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 805627 1000))

noncomputable def hp791829 := @hp791827 1180591620717411303424 hp749564 hp741590 (@hp791828 Bool.false 1618589635396057945663 1180591620717411303424 hp749564 hp741590 (hd4340 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823) hd5009)

noncomputable def hp791830 := @Enclosure.Real.IsNear.neg_val (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823)) 2227330288615246330305

noncomputable def hp791831 := @Enclosure.Real.IsNear.of_eq (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823)) (hardyZApproximantRS₀ (Enclosure.sfrac Bool.false 806921 1000))

noncomputable def hp791832 := @hp791830 295147905179352825856 209648501612658346520693 hp748549 (@hp791831 Bool.true 2227330288615246330305 295147905179352825856 209648501612658346520693 hp748549 (hd4359 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823) hd5010)

noncomputable def hp791833 := @Zeta.Certificates.ZIntervalRS.Certificate₀.mk (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823) hp791825 (hp791826 (hp791829 rfl rfl rfl) (hp791832 rfl rfl rfl))

noncomputable def hp791834 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791835 := hp791834 (Enclosure.sfrac Bool.false 805627 1000) 749551 1000 805627 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791836 := hp791835 (@Eq.refl Real (Enclosure.sfrac Bool.false 805627 1000)) rfl rfl rfl rfl

noncomputable def hp791837 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.fstVal₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791838 := @hp791837 Bool.false Bool.false 1618589635396057945663 1180591620717411303424 hp749564 hp741590 556919581 10737418240 1213 10737418240 (@hp791828 Bool.false 1618589635396057945663 1180591620717411303424 hp749564 hp741590 (hd4340 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823) hd5009)

noncomputable def hp791839 := hp791838 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl

noncomputable def hp791840 := BSN.norm_gt_hardyZErrorBoundRS₀_of_le (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823)) (Enclosure.sfrac Bool.false 749551 1000)

noncomputable def hp791841 := hp791840 (Enclosure.sfrac Bool.false 806921 1000) 749551 1000 806921 1000 (@Eq.refl Real (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791842 := hp791841 (@Eq.refl Real (Enclosure.sfrac Bool.false 806921 1000)) rfl rfl rfl rfl

noncomputable def hp791843 := @Enclosure.norm_gt_of_isNear (Zeta.Certificates.ZIntervalRS.sndVal₀ (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823)) (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))

noncomputable def hp791844 := @hp791843 Bool.true Bool.false 2227330288615246330305 295147905179352825856 209648501612658346520693 hp748549 556919581 10737418240 1213 10737418240 (@hp791831 Bool.true 2227330288615246330305 295147905179352825856 209648501612658346520693 hp748549 (hd4359 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823) hd5010)

noncomputable def hp791845 := hp791844 (hp790762 (@Eq.refl Real (hardyZErrorBoundRS₀ (Enclosure.sfrac Bool.false 749551 1000))) hd4952) rfl rfl rfl
open Zeta.Certificates
noncomputable def certificatePairs : List (Σ' I : ZIntervalRS, I.Certified) := [(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 799149 1000) (Enclosure.sfrac Bool.false 800445 1000) hp791698) (hp791699 (hp791708 (hp791711 (hp791714 rfl rfl)) (hp791717 (hp791720 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 800445 1000) (Enclosure.sfrac Bool.false 801741 1000) hp791723) (hp791724 (hp791733 (hp791736 (hp791739 rfl rfl)) (hp791742 (hp791745 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 801741 1000) (Enclosure.sfrac Bool.false 803037 1000) hp791748) (hp791749 (hp791758 (hp791761 (hp791764 rfl rfl)) (hp791767 (hp791770 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 803037 1000) (Enclosure.sfrac Bool.false 804332 1000) hp791773) (hp791774 (hp791783 (hp791786 (hp791789 rfl rfl)) (hp791792 (hp791795 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 804332 1000) (Enclosure.sfrac Bool.false 805627 1000) hp791798) (hp791799 (hp791808 (hp791811 (hp791814 rfl rfl)) (hp791817 (hp791820 rfl rfl))))),
(@PSigma.mk Zeta.Certificates.ZIntervalRS Zeta.Certificates.ZIntervalRS.Certified (hd4339 (Enclosure.sfrac Bool.false 805627 1000) (Enclosure.sfrac Bool.false 806921 1000) hp791823) (hp791824 (hp791833 (hp791836 (hp791839 rfl rfl)) (hp791842 (hp791845 rfl rfl)))))]

theorem solution : Zeta.Certificates.BatchSpec 6 799149 1000 806921 1000 :=
  ⟨CertifiedZeroIntervals.ofCertifiedRS certificatePairs (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.cons_cons (le_refl _) (List.IsChain.singleton _)))))), rfl, rfl, rfl⟩
#print axioms solution
